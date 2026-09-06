# Verify the Lean library

The public library proves the binary factor-nine theorem. Its root exports 21
modules, and [Verify.lean](../Verify.lean) audits all 495 public theorem
endpoints. Thirty public `lemma` declarations in TransposeNormalForm are
not pinned separately; they are used only inside audited proofs, where the
audit covers them transitively, and pinning or privatizing them is pending. The [admission record](admissions.md) lists the modules, dates,
discovered axiom sets, and exact claim promotions.

## Build and audit

Use the toolchain in [lean-toolchain](../lean-toolchain) and the dependencies
pinned in [lake-manifest.json](../lake-manifest.json). With Lean's `elan`
toolchain manager installed, run these commands from the repository root:

```sh
lake exe cache get
lake build StochasticToDeterministicLatents
lake env lean -DrelaxedAutoImplicit=false Verify.lean
```

The first command obtains the Mathlib cache and is useful when it is absent.
The root build must finish successfully before running Verify, which reads
compiled imports. A successful audit exits with code 0 and no output. The library's own
modules build without linter warnings; a warning naming one of them is a
regression to fix, never to suppress. The pinned upstream dependency emits
about seventy linter warnings of its own, which are distinct from elaboration
or audit failures and are not changed here.

The root build and audit passed in the prepared local checkout on 2026-09-04.
A fresh-machine replay has not been performed. Do not change the pinned
toolchain or dependencies, or run `lake update`, as part of a verification run.

On a shared machine, reserve one Lean build at a time. Check for active
`lean.exe` and `lake.exe` processes before every invocation. If another task
is using the slot, wait for it to finish. Long builds and Verify can exceed
ten minutes; preserve their logs and use a detached process when a foreground
command timeout could terminate them.

## What the audit checks

Each public theorem in Verify has both an `assert_no_sorry` check and a
`#print axioms` result pinned with `#guard_msgs`. Every pin was discovered by
Lean after compilation. A mismatch must be investigated; changing the expected
set to silence a failure is not an audit.

The four binary C9 headlines each report
`[propext, Classical.choice, Quot.sound]`. Two supporting theorems use smaller
sets, listed in the [axiom exceptions](admissions.md#axiom-sets). The audit
does not require every theorem to use the same set.

A definition of type `Prop` states a proposition. Checking that definition's
dependencies does not prove an inhabitant. Audit the theorem that proves it,
including when its proof reaches a private helper. Executable selector
definitions likewise do not establish agreement with the mathematical real
selector; the missing refinement signatures are labelled in the
[Lean contracts](../docs/lean-contracts.md).

Scan the repository's Lean files for trust shortcuts as well:

```sh
grep -rn -E '\b(sorry|admit|native_decide|unsafe)\b|^\s*(private |protected |noncomputable )*axiom\b' --include='*.lean' StochasticToDeterministicLatents StochasticToDeterministicLatents.lean Verify.lean
```

The scan should print nothing. `grep` exits with code 1 when it finds no
matches, which is the passing case; `assert_no_sorry` is not matched because
`_` is a word character. The same pattern works with `rg --glob '*.lean'`.
On Windows, run it from Git Bash; `grep` is not on the PowerShell path.
Review any other mechanism that could bypass kernel checking. This repository
does not classify compiler-backed `native_decide` certificates as
`kernel-verified`.

## Admitting a change

A module is **compiled** when it builds by its full Lake name. It is
**root-admitted** when the root imports it, the library builds, and every public
theorem is audited. A claim is **promoted** only when an audited declaration
proves its exact statement in the [claim ledger](../docs/claims.md).

For a new or changed theorem module:

1. Check its imports and provenance. Test removal of questionable imports in
   external scratch copies. Build dependencies first, then the module by its
   full name, for example
   `lake build StochasticToDeterministicLatents.Binary.FactorNine`.
2. Enumerate every public theorem, including attributed declarations. Scan for
   trust shortcuts and discover each theorem's actual axiom set in an external
   scratch file.
3. Review the declarations and human-readable proof against their source
   artifacts. Correct substantive mismatches before root admission.
4. Add the root import, theorem assertions, and discovered pins as needed.
   Update the admission record and the claim ledger in the same change.
5. Run the full root build and Verify. Check theorem coverage, local links,
   the Markdown math check from CLAUDE.md, private paths, generated
   artifacts, and `git diff --check`.

Use `lake build <Module.Name>` for the authoritative module check. Direct
`lake env lean <file>` does not apply the lakefile's Lean options; an external
scratch check must pass `-DrelaxedAutoImplicit=false` explicitly. Rebuild an
edited root before running Verify so it does not read stale imports.
