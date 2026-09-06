# Binary factor-nine blueprint

This nested Lake package renders the public library's definitions and claim
dependencies as a Verso Blueprint site. The [claim ledger](../docs/claims.md)
is authoritative for mathematical scope and evidence tiers. The graph links
existing declarations and introduces no mathematical theorems.

The [published site](https://AlexisOlson.github.io/stochastic-to-deterministic-latents/)
is deployed by the blueprint workflow on every push to `main` that touches
the blueprint or the Lean sources.

## Build

Use the checked-in toolchain and both manifests. Reserve one Lean/Lake build
at a time. Check for existing Lean and Lake processes before each invocation;
the wrappers stop if another build occupies the slot.

From the repository root, fetch the Mathlib cache, build the library, and run
the audit as described in [verification](../verification/README.md). Then,
from this directory, fetch the nested Mathlib cache and build the nested Lake
package. On Windows, run the PowerShell wrapper in `scripts/build.ps1`; on
Linux, run the Bash wrapper in `scripts/ci.sh`. The wrappers generate the
site, check its metadata, and compare its tiers with the ledger. Logs go to a
temporary directory outside the checkout, or to `VBP_LOG_DIR` when set.

The nested manifest resolves its own Mathlib checkout under
`.lake/packages/mathlib`. It has the same revision as the root's Mathlib.
The update hook can already restore its compiled cache; subsequent cache
fetches reuse that cache. The CI workflow fetches both checkouts' compiled
artifacts before building. Never update dependencies from the root package.

The generated entry page is `_out/site/html-multi/index.html`. On this Verso
pin, Windows generation writes the bundled search files to
`_out/static-web/search`; the PowerShell wrapper copies them to the
`-verso-search` directory expected by the HTML.

The wrappers also replace checkout-specific source locations in the generated
metadata with repository-relative paths before checking the export. This
changes source paths only; declaration records and graph status are preserved.

## Declaration status and tiers

Each `lean` attribute names existing public declarations from imported
modules. Strict resolution makes a missing or ambiguous name an elaboration
error. Verso derives graph status from the presence and completeness of those
declarations. For claims, tags record the ledger classification; they do not
set status.

Verso's generated-data check verifies preview references, cache coverage,
group membership, and graph preview keys. It is not the library's theorem
audit. The root verification remains responsible for the audited proof
dependencies. The tier checker reads the generated declaration records and
graph statuses as well as the ledger rows named in its id table, which must
list every claim row that has a node.

The ledger's `paper proof` spelling maps to the graph tag `paper-proof`.
Its external-source qualifier maps to `external`; this does not introduce a
new evidence tier. Definition nodes, including the count and rational
backend sub-nodes, carry only the `definition` tag and require a complete
set of resolved declarations. They carry no claim tier: a compiled
definition is not proof evidence. The refinement claim itself remains
tagged `paper-proof` and unformalized.

The binary selected-latent and named-selector bounds require full support.
The all-law result concerns `T` and an existential deterministic code.
The arbitrary-alphabet claims remain conjectures. The external lower bound
is a citation whose verification is not reproduced here.

## Package and publication

The package root module imports `Blueprint.lean`, which assembles the
`Chapters/` documents. `Main.lean` is the generator. The pinned dependency
provides the `vbp` CLI and targets the package root module, as prescribed by
its project template.

The workflow `blueprint.yml` builds the site, checks its metadata and ledger
tiers, and uploads a Pages artifact for pull requests targeting `main`
that change the blueprint, Lean sources, the root manifest or toolchain,
or the blueprint workflow. New runs cancel older runs for the same ref.
It also supports manual dispatch. The deploy job runs only on pushes to
`main`; on pull requests it is skipped and the artifact is the validation.
No package build changes the root toolchain or dependency configuration.
