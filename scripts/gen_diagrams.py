#!/usr/bin/env python3
"""Generate two Mermaid diagrams for the Stochastic-to-Deterministic Latents repository.

Usage:
    python gen_diagrams.py REPO_ROOT                      # both diagrams to stdout
    python gen_diagrams.py REPO_ROOT IMPORTS.mmd CLAIMS.mmd   # each diagram to its file

The script only reads the repository. It writes nothing under REPO_ROOT.

Diagram (a): module import graph
--------------------------------
Read from `StochasticToDeterministicLatents.lean` (the root) and every `*.lean`
file under `StochasticToDeterministicLatents/`. Only lines matching
`^import\\s+<Name>\\s*$` count (the anchor matters: `Binary/Table.lean` has a
docstring line beginning with the word "important"). Local modules are nodes,
labelled by the last component of their name (the `Binary/` and
`Binary/FactorNine/` subgraphs supply the rest); the root file is the node
`root`. Every `stoch_to_det.*` import collapses into one boundary node and
every `Mathlib.*` import into another. Any other import prefix is an error.
Edge direction is "imports": `A --> B` means A imports B.

Diagram (b): claim DAG
----------------------
`docs/claims.md` does not encode its dependency DAG in a machine-readable form.
It is an ASCII picture inside the first ```text fence after the `## Dependencies`
heading, and the parse below is written against the exact current shape of that
picture. The rules, so a change to the text is caught rather than misread:

  * The heading `## Dependencies` must occur exactly once, and exactly one
    fenced ```text block must lie between it and the next `## ` heading;
    other fenced blocks there (the generated ```mermaid diagram) are skipped.
  * Every non-blank line of the block must match one of four forms:
      1. `LHS ---> RHS`             sources LHS, target RHS
      2. `LHS ---> RHS ---+`        as 1, and RHS also joins the open group
      3. `LHS ---+`                 LHS joins the open group
      4. `LHS ---+--> RHS`          LHS joins the open group; RHS is its target
    where an arrow is two or more `-` followed by `>`, and LHS is one or more
    items separated by ` + `. Blank lines close a group; a closed group must
    have exactly one target and at least one source, else the parse fails.
  * An item that matches the claim-ID shape `NAME(-PART)*` with an optional
    parenthesised argument, e.g. `PRICE(8)` or `BIN-W3-8`, is a claim node.
    Any other item (currently "selected binary normal form", "scalar phase
    estimates", "boundary transfer", and the target `C_* >= 1.960073002187`)
    is an auxiliary node drawn with a dashed outline and no tier.
  * A claim ID with a parenthesised argument that has no ledger row of its own
    is mapped to the row whose argument is `(c)` when that row exists (so
    `PRICE(8)` and `PRICE(4)` become `PRICE(c)` with the instantiation shown
    as an edge label). Any other claim ID without a ledger row is an error.
  * Ledger rows come from the table under `## Ledger`: lines starting with
    "| `ID` |" and having exactly four cells. A row's tier is the first
    backticked token in its "Mathematical status" cell that is one of
    `kernel-verified`, `paper proof`, `interval-certified`, `conjecture` and
    is not immediately preceded by the word "not". A row with no such token
    must mention `native_decide` (an external compiler-backed certificate)
    and is drawn with the class `external`; otherwise the parse fails.
  * Ledger rows absent from the picture are still drawn, as isolated nodes,
    with a warning on stderr.

On success the script prints to stderr a manifest of every file and line
range it read, so a later edit to any of them is known to require rerunning.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

LIB = "StochasticToDeterministicLatents"
UPSTREAM_PREFIX = "stoch_to_det."
MATHLIB_PREFIX = "Mathlib."

TIERS = {
    "kernel-verified": "kernel",
    "paper proof": "paper",
    "interval-certified": "interval",
    "conjecture": "conjecture",
}

CLASSDEFS = """\
classDef kernel fill:#d9f2d9,stroke:#2e7d32,color:#111;
classDef paper fill:#fff3cd,stroke:#b8860b,color:#111;
classDef interval fill:#dbe9ff,stroke:#1e5aa8,color:#111;
classDef conjecture fill:#f5f5f5,stroke:#777,stroke-dasharray:5 3,color:#111;
classDef external fill:#f8d7da,stroke:#a33,color:#111;
classDef aux fill:none,stroke:#999,stroke-dasharray:2 2,color:#333;"""

CLAIM_ID_RE = re.compile(r"^[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*(?:\([A-Za-z0-9]+\))?$")

manifest: list[str] = []


def fail(msg: str) -> None:
    sys.stderr.write(f"gen_diagrams.py: error: {msg}\n")
    sys.exit(1)


def warn(msg: str) -> None:
    sys.stderr.write(f"gen_diagrams.py: warning: {msg}\n")


def node_id(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", name).strip("_")


# ---------------------------------------------------------------- imports ---

IMPORT_RE = re.compile(r"^import\s+(\S+)\s*$")


def module_name(path: Path, root: Path) -> str:
    rel = path.relative_to(root / LIB).with_suffix("")
    return ".".join(rel.parts)  # e.g. "Binary.FactorNine.PositivePhase"


def parse_imports(root: Path) -> dict[str, list[str]]:
    root_file = root / f"{LIB}.lean"
    lib_dir = root / LIB
    if not root_file.is_file():
        fail(f"missing root file {root_file}")
    if not lib_dir.is_dir():
        fail(f"missing library directory {lib_dir}")
    files = [root_file] + sorted(lib_dir.rglob("*.lean"))
    graph: dict[str, list[str]] = {}
    for f in files:
        mod = "root" if f == root_file else module_name(f, root)
        imports: list[str] = []
        lines = f.read_text(encoding="utf-8").splitlines()
        matched_lines: list[int] = []
        for i, line in enumerate(lines, start=1):
            m = IMPORT_RE.match(line)
            if m:
                imports.append(m.group(1))
                matched_lines.append(i)
        if matched_lines:
            manifest.append(
                f"{f.relative_to(root).as_posix()}: import lines "
                f"{matched_lines[0]}-{matched_lines[-1]}"
            )
        graph[mod] = imports
    return graph


def imports_mermaid(graph: dict[str, list[str]]) -> str:
    local = {m for m in graph if m != "root"}
    out = ["%% Module import graph. Edge A --> B means A imports B. The root",
           "%% module imports every module and is not drawn.",
           "%% Generated by gen_diagrams.py; do not edit by hand.",
           "graph TD"]
    used_upstream = used_mathlib = False
    edges: list[str] = []
    for mod, imports in graph.items():
        if mod == "root":
            # The root imports every module; drawing those edges only clutters
            # the structural picture. The imports are still parsed above so an
            # unknown or missing import is reported.
            continue
        for imp in imports:
            if imp == LIB:
                target = "root"
            elif imp.startswith(LIB + "."):
                target = imp[len(LIB) + 1:]
                if target not in local:
                    fail(f"{mod} imports unknown local module {imp}")
            elif imp.startswith(UPSTREAM_PREFIX):
                target, used_upstream = "UPSTREAM", True
            elif imp.startswith(MATHLIB_PREFIX):
                target, used_mathlib = "MATHLIB", True
            else:
                fail(f"{mod} imports {imp}, which has no boundary rule")
            edges.append(f"  {node_id(mod)} --> {node_id(target)}")

    def decl(mod: str) -> str:
        return f'  {node_id(mod)}["{mod.rsplit(".", 1)[-1]}"]'

    top = sorted(m for m in local if not m.startswith("Binary."))
    binary = sorted(m for m in local if m.startswith("Binary.") and not m.startswith("Binary.FactorNine."))
    factor_nine = sorted(m for m in local if m.startswith("Binary.FactorNine."))
    out.extend(decl(m) for m in top)
    out.append('  subgraph BINARY["Binary/"]')
    out.extend("  " + decl(m) for m in binary)
    if factor_nine:
        out.append('    subgraph FACTORNINE["Binary/FactorNine/"]')
        out.extend("    " + decl(m) for m in factor_nine)
        out.append("    end")
    out.append("  end")
    if used_upstream:
        out.append('  UPSTREAM[("stoch_to_det.* (pinned upstream)")]')
    if used_mathlib:
        out.append('  MATHLIB[("Mathlib.*")]')
    out.extend(sorted(set(edges), key=edges.index))
    out.append("  classDef boundary fill:#eee,stroke:#666,stroke-dasharray:4 2,color:#111;")
    out.append("  class UPSTREAM,MATHLIB boundary;")
    return "\n".join(out) + "\n"


# ------------------------------------------------------------------ claims ---

ARROW = r"-{2,}>"
LINE_GROUP_TARGET = re.compile(rf"^(?P<lhs>.+?)\s*-{{2,}}\+{ARROW}\s*(?P<rhs>.+?)\s*$")
LINE_ARROW = re.compile(rf"^(?P<lhs>.+?)\s*{ARROW}\s*(?P<rhs>.+?)(?P<tail>\s+-{{1,}}\+)?\s*$")
LINE_GROUP_SOURCE = re.compile(r"^(?P<lhs>.+?)\s*-{2,}\+\s*$")


def split_items(text: str) -> list[str]:
    items = [t.strip() for t in text.split(" + ")]
    if any(not t for t in items):
        fail(f"empty item in {text!r}")
    return items


def find_dependency_block(lines: list[str]) -> tuple[int, int]:
    heads = [i for i, l in enumerate(lines) if l.strip() == "## Dependencies"]
    if len(heads) != 1:
        fail(f"expected exactly one '## Dependencies' heading, found {len(heads)}")
    start = heads[0] + 1
    end = next((i for i in range(start, len(lines)) if lines[i].startswith("## ")), len(lines))
    # The section also holds this script's own ```mermaid output, so only the
    # ```text fence pair is the picture; any other fenced block is skipped.
    fences = [i for i in range(start, end) if lines[i].strip().startswith("```")]
    if len(fences) % 2 != 0:
        fail("unbalanced fences in the Dependencies section")
    text = [(fences[k], fences[k + 1]) for k in range(0, len(fences), 2)
            if lines[fences[k]].strip() == "```text"]
    if len(text) != 1:
        fail("expected exactly one ```text fence in the Dependencies section")
    return text[0][0] + 1, text[0][1]  # half-open line index range of the body


def parse_dag(lines: list[str], lo: int, hi: int) -> list[tuple[str, str]]:
    """Return (source, target) pairs in file order."""
    edges: list[tuple[str, str]] = []
    group_sources: list[str] = []
    group_target: str | None = None
    group_open = False

    def close_group(where: int) -> None:
        nonlocal group_sources, group_target, group_open
        if not group_open:
            return
        if group_target is None or not group_sources:
            fail(f"dependency group ending before line {where} has no target or no sources")
        edges.extend((s, group_target) for s in group_sources)
        group_sources, group_target, group_open = [], None, False

    for i in range(lo, hi):
        raw = lines[i]
        line = raw.strip()
        if not line:
            close_group(i + 1)
            continue
        if m := LINE_GROUP_TARGET.match(line):
            if group_open and group_target is not None:
                fail(f"line {i + 1}: second target for one group")
            group_open = True
            group_sources.extend(split_items(m.group("lhs")))
            group_target = m.group("rhs").strip()
        elif m := LINE_ARROW.match(line):
            rhs = m.group("rhs").strip()
            for s in split_items(m.group("lhs")):
                edges.append((s, rhs))
            if m.group("tail"):
                group_open = True
                group_sources.append(rhs)
        elif m := LINE_GROUP_SOURCE.match(line):
            group_open = True
            group_sources.extend(split_items(m.group("lhs")))
        else:
            fail(f"line {i + 1} of claims.md does not match any known dependency form: {raw!r}")
    close_group(hi + 1)
    return edges


LEDGER_ROW = re.compile(r"^\|\s*`(?P<id>[^`]+)`\s*\|")
TIER_TOKEN = re.compile(r"`([^`]+)`")


def parse_ledger(lines: list[str]) -> tuple[dict[str, str], tuple[int, int]]:
    heads = [i for i, l in enumerate(lines) if l.strip() == "## Ledger"]
    if len(heads) != 1:
        fail(f"expected exactly one '## Ledger' heading, found {len(heads)}")
    start = heads[0] + 1
    end = next((i for i in range(start, len(lines)) if lines[i].startswith("## ")), len(lines))
    tiers: dict[str, str] = {}
    first = last = None
    for i in range(start, end):
        line = lines[i]
        m = LEDGER_ROW.match(line)
        if not m:
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 4:
            fail(f"line {i + 1}: ledger row has {len(cells)} cells, expected 4")
        cid, status = cells[0].strip("`"), cells[2]
        if cid in tiers:
            fail(f"line {i + 1}: duplicate ledger row {cid}")
        tier = None
        for tm in TIER_TOKEN.finditer(status):
            tok = tm.group(1)
            if tok in TIERS and not status[: tm.start()].rstrip().endswith("not"):
                tier = TIERS[tok]
                break
        if tier is None:
            if "native_decide" not in status:
                fail(f"line {i + 1}: no tier found in status cell of {cid}: {status!r}")
            tier = "external"
        tiers[cid] = tier
        first = i + 1 if first is None else first
        last = i + 1
    if not tiers:
        fail("no ledger rows found")
    return tiers, (first, last)


def canonical_claim(item: str, tiers: dict[str, str]) -> tuple[str, str | None]:
    """Map a DAG item to (node, edge_label). Non-claims map to themselves."""
    if not CLAIM_ID_RE.match(item):
        return item, None
    if item in tiers:
        return item, None
    m = re.match(r"^(?P<name>[^(]+)\((?P<arg>[^)]+)\)$", item)
    if m and f"{m.group('name')}(c)" in tiers:
        return f"{m.group('name')}(c)", f"c={m.group('arg')}"
    fail(f"dependency item {item!r} looks like a claim ID but has no ledger row")


def claims_mermaid(root: Path) -> str:
    path = root / "docs" / "claims.md"
    if not path.is_file():
        fail(f"missing {path}")
    lines = path.read_text(encoding="utf-8").splitlines()
    lo, hi = find_dependency_block(lines)
    raw_edges = parse_dag(lines, lo, hi)
    tiers, (lfirst, llast) = parse_ledger(lines)
    manifest.append(f"docs/claims.md: dependency picture lines {lo + 1}-{hi} (fenced block body)")
    manifest.append(f"docs/claims.md: ledger rows lines {lfirst}-{llast}")

    nodes: dict[str, str] = {}   # node -> class
    edges: list[tuple[str, str, str | None]] = []
    for src, dst in raw_edges:
        s, slabel = canonical_claim(src, tiers)
        d, dlabel = canonical_claim(dst, tiers)
        if dlabel:
            fail(f"instantiated claim {dst!r} used as a target")
        nodes.setdefault(s, tiers.get(s, "aux"))
        nodes.setdefault(d, tiers.get(d, "aux"))
        edges.append((s, d, slabel))
    for cid, tier in tiers.items():
        if cid not in nodes:
            warn(f"ledger row {cid} does not appear in the dependency picture; drawn isolated")
            nodes[cid] = tier

    out = ["%% Claim DAG from docs/claims.md. Edge A --> B means B depends on A.",
           "%% Node colour is the ledger tier; dashed plain nodes are inputs that are not claims.",
           "%% Generated by gen_diagrams.py; do not edit by hand.",
           "graph TD"]
    for n, cls in nodes.items():
        out.append(f'  {node_id(n)}["{n}"]:::{cls}')
    seen: set[tuple[str, str, str | None]] = set()
    for s, d, label in edges:
        if (s, d, label) in seen:
            continue
        seen.add((s, d, label))
        if label:
            out.append(f'  {node_id(s)} -- "{label}" --> {node_id(d)}')
        else:
            out.append(f"  {node_id(s)} --> {node_id(d)}")
    out.append('  subgraph LEGEND["Tier (from the ledger)"]')
    out.append("    direction LR")
    legend = [("kernel", "kernel-verified"), ("paper", "paper proof"),
              ("interval", "interval-certified"), ("conjecture", "conjecture"),
              ("external", "external certificate (not a tier)")]
    for cls, text in legend:
        if cls in nodes.values():
            out.append(f'    L_{cls}["{text}"]:::{cls}')
    out.append("  end")
    out.extend("  " + l for l in CLASSDEFS.splitlines())
    return "\n".join(out) + "\n"


# -------------------------------------------------------------------- main ---

def main(argv: list[str]) -> None:
    if len(argv) not in (2, 4):
        sys.stderr.write(__doc__.split("\n\n")[1] + "\n")
        sys.exit(2)
    root = Path(argv[1]).resolve()
    imports = imports_mermaid(parse_imports(root))
    claims = claims_mermaid(root)
    if len(argv) == 4:
        Path(argv[2]).write_text(imports, encoding="utf-8", newline="\n")
        Path(argv[3]).write_text(claims, encoding="utf-8", newline="\n")
    else:
        sys.stdout.write(imports)
        sys.stdout.write("\n")
        sys.stdout.write(claims)
    sys.stderr.write("gen_diagrams.py read:\n")
    for m in manifest:
        sys.stderr.write(f"  {m}\n")


if __name__ == "__main__":
    main(sys.argv)
