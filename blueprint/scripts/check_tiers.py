#!/usr/bin/env python3
"""Compare the public claim ledger with Verso's generated graph metadata."""

import argparse
import json
from pathlib import Path
import re
import sys

BLUEPRINT = Path(__file__).resolve().parents[1]
LEDGER_IDS = {
    "PRICE": "PRICE(c)",
    "BIN-REDUCE": "BIN-REDUCE",
    "BIN-W3-8": "BIN-W3-8",
    "BIN-CATALOG-RECOVERY": "BIN-CATALOG-RECOVERY",
    "BIN-C9": "BIN-C9",
    "BIN-LAW-SELECTOR": "BIN-LAW-SELECTOR",
    "GEN-W3-8": "GEN-W3-8",
    "GEN-C9": "GEN-C9",
    "LOWER-1960": "LOWER-1960",
}
DEFINITIONS = (
    "DEF-LAW", "DEF-INFO", "DEF-LATENT", "DEF-SCORE", "DEF-TAU",
    "DEF-CODE", "DEF-DETSCORE", "DEF-W3", "DEF-SELECTOR",
)
DEFINITION_SUBNODES = ("BIN-COUNT-SELECTOR", "BIN-RATIONAL-SELECTOR")
SUBNODES = (
    "PRICE-IDENTITY", "BIN-NORMAL-FORM", "BIN-PHASE-NONPOS",
    "BIN-PHASE-POS", "BIN-SEAM-BALANCED", "BIN-SEAM-LOW-PRIOR",
    "BIN-SPARSE", "BIN-SELECTOR-C9", *DEFINITION_SUBNODES,
)
TIER_TAGS = {"kernel-verified", "paper-proof", "conjecture", "external"}


def name(value):
    """Lean pretty-prints punctuation-bearing name components in quotes."""
    if not isinstance(value, str):
        raise ValueError(f"Expected a Lean name string, received {value!r}")
    return value.replace("\u00ab", "").replace("\u00bb", "")


def enum(value):
    if isinstance(value, str):
        return value
    if isinstance(value, dict) and len(value) == 1:
        return next(iter(value))
    raise ValueError(f"Unexpected enum representation: {value!r}")


def ledger_tiers(path):
    wanted = set(LEDGER_IDS.values())
    rows = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        cells = [cell.strip() for cell in line.split("|")[1:-1]]
        if len(cells) != 4:
            continue
        row_id = cells[0].strip("\x60")
        if row_id not in wanted:
            continue
        if row_id in rows:
            raise ValueError(f"Duplicate ledger row: {row_id}")
        status = cells[2]
        # The external row quotes the local tier only to deny that status.
        if status.startswith("External "):
            tier = "external"
        else:
            match = re.match(r"\x60(kernel-verified|paper proof|conjecture)\x60", status)
            if not match:
                raise ValueError(f"Unrecognized ledger status for {row_id}: {status}")
            tier = match.group(1).replace(" ", "-")
        rows[row_id] = tier
    return rows


def external_declarations(code_data):
    """Read declaration records, including presence, from the code-data sum."""
    records = []

    def visit(value):
        if isinstance(value, dict):
            if "canonical" in value and "present" in value:
                records.append(value)
            else:
                for child in value.values():
                    visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(code_data)
    return records


def index_manifest(manifest):
    entries = {}
    for entry in manifest["previews"]:
        if enum(entry["targetKind"]) != "block" or enum(entry["facet"]) != "statement":
            continue
        label = entry.get("authoredLabel") or name(entry["label"])
        if label in entries:
            raise ValueError(f"Duplicate statement entry: {label}")
        entries[label] = entry
    nodes = {}
    for graph in manifest["graphs"]:
        for node in graph["nodes"]:
            label = name(node["label"])
            if label in nodes:
                previous = nodes[label]
                for field in ("statementStatus", "proofStatus", "parent"):
                    if previous.get(field) != node.get(field):
                        raise ValueError(f"Graph variants disagree on {label}.{field}")
            nodes[label] = node
    groups = {name(group["label"]): group for group in manifest["groups"]}
    return entries, nodes, groups


def formalized(node):
    statement = enum(node["statementStatus"]) == "formalized"
    proof = enum(node["proofStatus"]) in {"formalized", "formalizedWithAncestors"}
    return statement, proof


def check(ledger, manifest):
    tiers = ledger_tiers(ledger)
    entries, nodes, groups = index_manifest(manifest)
    failures = 0
    unresolved = 0
    for label in (*DEFINITIONS, *LEDGER_IDS, *SUBNODES):
        errors = []
        entry = entries.get(label)
        node = nodes.get(label)
        if entry is None:
            errors.append("missing manifest statement")
        if node is None:
            errors.append("missing graph node")
        details = ""
        if entry is not None and node is not None:
            tags = set(entry["tags"])
            decls = external_declarations(entry.get("codeData"))
            resolved = [decl for decl in decls if decl["present"] is True]
            unresolved += len(decls) - len(resolved)
            statement, proof = formalized(node)
            details = (
                f"tags={','.join(sorted(tags))} "
                f"declarations={len(resolved)}/{len(decls)} "
                f"statement={enum(node['statementStatus'])} "
                f"proof={enum(node['proofStatus'])}"
            )
            if label in DEFINITIONS or label in DEFINITION_SUBNODES:
                if tags != {"definition"}:
                    errors.append("definition node must be tagged definition only")
                if not resolved or len(resolved) != len(decls):
                    errors.append("no complete set of resolved declarations")
            if label in SUBNODES:
                # A parent is a graph-group relation, not a proof dependency.
                parent = entry.get("parent")
                group_name = name(parent) if parent is not None else None
                if label not in DEFINITION_SUBNODES and "sub-node" not in tags:
                    errors.append("missing sub-node tag")
                if group_name not in groups or node.get("parent") != parent:
                    errors.append("missing or inconsistent parent relation")
                elif not any(
                    name(member["label"]) == label
                    for member in groups[group_name]["entries"]
                ):
                    errors.append("parent group does not contain this node")
            elif label in LEDGER_IDS:
                tier = tiers.get(LEDGER_IDS[label])
                if tier is None:
                    errors.append("missing ledger row")
                elif tags & TIER_TAGS != {tier}:
                    errors.append(f"tier tags {sorted(tags & TIER_TAGS)} != ledger {tier}")
                if tier == "kernel-verified":
                    if not resolved or len(resolved) != len(decls):
                        errors.append("no complete set of resolved declarations")
                    if not (statement and proof):
                        errors.append("kernel-verified node is not formalized")
                    if any(enum(decl["provedStatus"]) != "proved" for decl in resolved):
                        errors.append("declaration status is not complete")
                elif tier in {"paper-proof", "conjecture", "external"}:
                    if statement or proof:
                        errors.append("unformalized ledger row is marked formalized")
                    if decls:
                        errors.append("claim row links declarations belonging in sub-nodes")
        if errors:
            failures += 1
            print(f"FAIL {label}: {'; '.join(errors)} {details}".rstrip())
        else:
            print(f"PASS {label}: {details}")
    print(f"Unresolved declarations: {unresolved}; node failures: {failures}")
    return int(failures > 0 or unresolved > 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=BLUEPRINT.parent / "docs/claims.md")
    parser.add_argument(
        "--manifest", type=Path,
        default=BLUEPRINT / "_out/site/html-multi/-verso-data/blueprint-manifest.json",
    )
    args = parser.parse_args()
    try:
        manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
        return check(args.ledger, manifest)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"FAIL tier check: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
