# Repository guidance

This Lean 4 / Mathlib project proves the certificate-free binary factor-nine
theorem for stochastic-to-deterministic latents. Read [docs/claims.md](docs/claims.md)
and [verification/README.md](verification/README.md) before editing. They define
the mathematical scope and admission requirements.

## Build discipline

- Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` unchanged.
  Do not run `lake update`. Invalidating the Mathlib cache can cause an
  hours-long rebuild.
- Do not create clones or worktrees for Lean work. Use the prepared checkout.
- Check for active `lean.exe` and `lake.exe` processes before every Lean or
  Lake invocation. Run one build at a time and never kill another task's
  process. Rebuild affected modules in dependency order, one target at a time.
- Long root builds and Verify may exceed ten minutes. Run them with persistent
  logs and a detached controller if the foreground timeout could terminate
  them. Keep logs and scratch files outside the repository.
- This pinned Lake has no `-j` jobs option. Do not rely on it to serialize
  compilation of several stale modules.

The authoritative commands, from the repository root, are:

```sh
lake build StochasticToDeterministicLatents
lake env lean -DrelaxedAutoImplicit=false Verify.lean
lake build StochasticToDeterministicLatents.Binary.FactorNine
```

Use a full module name to build one module. Direct `lake env lean <file>` does
not apply the lakefile's Lean options. Pass `-DrelaxedAutoImplicit=false` for
scratch checks: unbound multi-character identifiers must be errors. Rebuild
the root after import changes before running Verify, which reads its olean.

The root exports 21 modules and Verify has 495 theorem endpoints. Recount
after changes. A successful Verify run is silent and exits 0; a build may
replay linter warnings. There is no separate test framework: the required
checks are builds, theorem coverage, the axiom audit, and the claim ledger.

## Architecture and mathematical scope

The [blueprint](docs/blueprint.md) fixes notation and explains the mechanism.
The [Lean contracts](docs/lean-contracts.md) distinguish current declarations
from future targets and map the public modules.

- `Information` and `Latent` are reducible `abbrev` facades over upstream.
  Keep them definitionally identical; do not reimplement their definitions.
- `Deterministic` defines codes over the canonical finite alphabet
  `Code α β = (α × β) → Fin (card (α × β))`.
- `Bridge` is the only local module allowed to import upstream `Envelope`,
  `Duality`, `Seed`, or `Quotient`. Other modules use its public interfaces.
- Binary normal forms, chart ledgers, scalar phase estimates, and catalog
  recovery supply the full-support bound. `SparseLimit` transfers a supplied
  bound on `T` to all laws; FactorNine supplies its binary premise at nine.
- `Binary.Reduction` proves cost minimality over `BinaryCode`. The numerical
  factor-nine proof does not depend on this minimality theorem.

Preserve the distinction between an all-law bound on `T` and full-support
guarantees for a selected optimal latent or the named selector. Neither scalar
phase arm alone proves `BIN-W3-8`. The count/rational selector refinement and
the arbitrary-alphabet conjectures keep their separate scopes and evidence
tiers. The sharper factor-five route and its interval certificate are held for
a later release; the transfer manifest records that deferral, and no other
description of the route appears in this tree.

Use `score_p(L)` / `Latent.score` for a supplied latent, `tau(p)` for the
stochastic optimum, `D_p(g)` / `detScore` for a supplied code, and `T(p)` for
the deterministic optimum. All information quantities are in bits, with
`0 log 0 = 0`; scalar natural-log ledgers must retain their explicit bit
conversions. `Phi(q)` is a component functional, not a latent score.

## Mathematical notation in Markdown

Mathematics in Markdown is TeX, rendered by GitHub. Inline math uses the
backtick form, a dollar sign, a backtick, the TeX, a backtick, and a dollar
sign, as in `` $`\tau(p) \le T(p)`$ ``. Display math uses a ```` ```math ````
fence. Plain-dollar math is never used: GitHub applies Markdown escapes and
emphasis inside it, so braces, thin spaces, and underscores break silently,
and a `<` before a letter becomes an HTML tag. The `verify` job fails on any
dollar sign that does not touch a backtick; run the same check locally:

```sh
git ls-files '*.md' | xargs grep -nP '(?<!`)\x24(?!`)'
```

Measured rules, from the rendering tests behind pull request #9:

- Conditioning bars are `\mid`, never a bare `|`, which splits table cells.
- Operator names use `\mathrm`, as in `\mathrm{score}_p(L)` and
  `\mathrm{W3}(L)`; GitHub forbids `\operatorname` and `\DeclareMathOperator`.
  The Verso blueprint keeps `\operatorname` under KaTeX.
- No macros: `\newcommand` and `\def` do not work. No `\tag`, `\label`, or
  `\eqref`. An equation number is `\qquad \text{(6.1)}` at the end of the
  display, and cross-references are prose.
- A bare `\\` does not break a line; multi-line displays use `aligned` or
  `gathered`.
- Fences render in list items and blockquotes, not inside `<details>` or
  table cells. Keep math out of headings, link text, and italics.
- Lean names, paths, commands, ledger identifiers, and evidence tiers stay
  in code spans; two scripts parse the ledger table by those exact tokens.

Pages not yet converted keep their code-span notation until their own
conversion pull request, which passes the same independent read as any
other prose change to a paper-proof page.

## Admission and review

Follow the [verification procedure](verification/README.md#admitting-a-change).
For each module, enumerate all public theorems, discover their actual axiom
sets, and pin them in Verify with `assert_no_sorry` and guarded `#print axioms`.
A `Prop`-valued definition is not proof evidence. An executable definition is
not a refinement theorem, and a refinement claim requires reachable input
conditions as well as the comparison theorem.

Keep new modules out of the root until their individual build and review pass.
Every admission updates the [admission record](verification/admissions.md) and
the claim ledger, even when no claim status changes. Promote a claim only when
its exact public declaration passes the complete audit. A result verified only
elsewhere remains qualified as such. The evidence tiers are `kernel-verified`,
`paper proof`, and `conjecture`; external-source labels are qualifiers.

Before committing, run the trust scan in the verification guide, inspect the
complete diff, check local Markdown links, and run `git diff --check`.
Commit and pull-request subjects are at most 50 characters: squash merge
appends the pull-request number, and GitHub's file listing truncates subjects
near 57 characters at common widths. Details belong in the body. The `verify`
job rejects a pull request whose title, or single commit's subject, is longer.
Mathematical prose changes require an independent check against the actual
source artifacts. A page at `paper proof` is admitted only after an
independent read against its sources and a cold read of the public tree, with
every display re-derived under the public notation. Scripts under `scripts/`
replay identities and regenerate diagrams; they are not evidence. Back up a
new untracked Lean module outside the repository before applying validator
corrections.

## Attribution and repository contents

The upstream ancestor is `DLorell/stoch_to_det`, under Apache-2.0. Each adapted
Lean file must retain a concise origin, license, and modification notice.
The per-file inventory of adapted working-material declarations, with its
merge, specialization, and private re-proof accounting, is kept privately
outside this repository; research module and declaration names never appear
in the public tree. A repository link alone is not sufficient attribution.

Unpublished working material is an attribution source, not public evidence or
a build dependency. Preserve that distinction when moving inventories.
[docs/provenance.md](docs/provenance.md) defines the policy and
[docs/transfer-manifest.md](docs/transfer-manifest.md) records transfer decisions.

Keep private workspace paths, raw reports, transcripts, review bundles,
campaign logs, and generated build products outside the tree. The admission
record contains verified results only. Selector examples illustrate
definitions and branches; they do not prove a numerical bound or executable
refinement. Text files use LF, as specified in `.gitattributes`.
