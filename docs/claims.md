# Claim DAG and status ledger

This is the current status record. Each claim has its exact scope and evidence
below. [Lean contracts](lean-contracts.md) separate existing declarations from
future targets; [admissions](../verification/admissions.md) record the local
audits and their history.

## Status vocabulary

| Status | Meaning |
|---|---|
| `kernel-verified` | Lean compiled with no unfinished proof dependency, and its exact axiom set was audited. The repository in which this occurred is named. |
| `paper proof` | Complete rigorous prose derivation with no unresolved step; not formalized. |
| `conjecture` | Unresolved mathematical claim. |

External-source labels identify where and how evidence was checked. They are
qualifiers, not additional tiers. A composite proof inherits the weakest tier
of the inputs it needs.

## Dependencies

```text
selected binary normal form + scalar phase estimates --> BIN-W3-8
BIN-W3-8 + PRICE(8) + boundary transfer ----------------> BIN-C9
BIN-W3-8 + BIN-CATALOG-RECOVERY + PRICE(8) -------------> D_p(g_p) <= 9*tau(p) on full support

PRICE(8) + GEN-W3-8 ---------------------------> GEN-C9

LOWER-1960 ------------------------------------> C_* >= 1.960073002187
```

The same dependencies as a diagram, with the ledger tier as node colour;
regenerate it with `scripts/gen_diagrams.py` whenever the picture above or
the ledger table changes:

```mermaid
graph TD
  selected_binary_normal_form["selected binary normal form"]:::aux
  BIN_W3_8["BIN-W3-8"]:::kernel
  scalar_phase_estimates["scalar phase estimates"]:::aux
  BIN_C9["BIN-C9"]:::kernel
  PRICE_c["PRICE(c)"]:::kernel
  boundary_transfer["boundary transfer"]:::aux
  D_p_g_p_9_tau_p_on_full_support["D_p(g_p) <= 9*tau(p) on full support"]:::aux
  BIN_CATALOG_RECOVERY["BIN-CATALOG-RECOVERY"]:::kernel
  GEN_C9["GEN-C9"]:::conjecture
  GEN_W3_8["GEN-W3-8"]:::conjecture
  LOWER_1960["LOWER-1960"]:::external
  C_1_960073002187["C_* >= 1.960073002187"]:::aux
  BIN_REDUCE["BIN-REDUCE"]:::kernel
  BIN_LAW_SELECTOR["BIN-LAW-SELECTOR"]:::paper
  selected_binary_normal_form --> BIN_W3_8
  scalar_phase_estimates --> BIN_W3_8
  BIN_W3_8 --> BIN_C9
  PRICE_c -- "c=8" --> BIN_C9
  boundary_transfer --> BIN_C9
  BIN_W3_8 --> D_p_g_p_9_tau_p_on_full_support
  BIN_CATALOG_RECOVERY --> D_p_g_p_9_tau_p_on_full_support
  PRICE_c -- "c=8" --> D_p_g_p_9_tau_p_on_full_support
  PRICE_c -- "c=8" --> GEN_C9
  GEN_W3_8 --> GEN_C9
  LOWER_1960 --> C_1_960073002187
  subgraph LEGEND["Tier (from the ledger)"]
    direction LR
    L_kernel["kernel-verified"]:::kernel
    L_paper["paper proof"]:::paper
    L_conjecture["conjecture"]:::conjecture
    L_external["external certificate (not a tier)"]:::external
  end
  classDef kernel fill:#d9f2d9,stroke:#2e7d32,color:#111;
  classDef paper fill:#fff3cd,stroke:#b8860b,color:#111;
  classDef interval fill:#dbe9ff,stroke:#1e5aa8,color:#111;
  classDef conjecture fill:#f5f5f5,stroke:#777,stroke-dasharray:5 3,color:#111;
  classDef external fill:#f8d7da,stroke:#a33,color:#111;
  classDef aux fill:none,stroke:#999,stroke-dasharray:2 2,color:#333;
```

C9 bounds a selected chart code directly; its numerical upper bound does not
need the separate minimality theorem `BIN-REDUCE`, which therefore has no
edge above. Catalog recovery also bounds the mathematical law-only selector
`g_p` on full support (the third line; the endpoint is
`Binary.detScore_selector_le_nine_mul_tau_of_fullSupport`). `BIN-LAW-SELECTOR`
defines that selector and records the open executable contract; it is a
definition consumed by the third line, not a numerical claim.

`BIN-W3-8` requires full support. The generic theorem
`T_le_mul_tau_of_forall_fullSupport` transfers a supplied full-support bound
on `T` to all laws. FactorNine supplies its binary premise at nine. The
[sparse proof](binary-factor-nine.md#6-sparse-and-degenerate-laws) gives no
corresponding selected-latent `W3` or named-selector boundary guarantee.

## Ledger

Here `C_*` is the infimum of constants `C` for which `T(p) <= C*tau(p)` holds
for every law on arbitrary finite alphabets. Namespace prefixes in formal
names below are `StochasticToDeterministicLatents`.

| ID | Statement | Mathematical status | Evidence in this repository |
|---|---|---|---|
| `PRICE(c)` | If `L` attains `tau(p)` and `W3(L) <= c*tau(p)`, then `T(p) <= (1+c)*tau(p)`. | `kernel-verified` in this repository (2026-09-01), through the public declaration `StochasticToDeterministicLatents.T_le_one_add_mul_tau_of_w3`. | [Pricing](../StochasticToDeterministicLatents/Pricing.lean) supplies the fixed-code identity and conditional bound. The attaining latent and its `W3` bound are hypotheses; pricing alone supplies no numerical factor. |
| `BIN-REDUCE` | On the supplied positive transposed binary chart, every code in the canonical four-label code space `BinaryCode` is dominated in `W3Cost` by the constant or high-singleton code. | `kernel-verified` in this repository (2026-09-03), through the public declaration `StochasticToDeterministicLatents.Binary.TransposeChart.min_chartCodes_le_w3Cost`. The arbitrary-output-alphabet form, `kernel-verified` in the reviewed source workspace, remains qualified as such. | [Reduction](../StochasticToDeterministicLatents/Binary/Reduction.lean) audits all three cost-dominance endpoints. The public cost type uses `BinaryCode`; the arbitrary-output reward lemma is private, and no public theorem converts that broader statement to a cost bound. The supplied chart need not attain `tau`. The infimum identity is not a separate declaration. |
| `BIN-W3-8` | Every full-support binary-observable law has some attained `tau`-optimal latent `L` with `W3(L) <= 8*tau(p)`. | `kernel-verified` in this repository (2026-09-04), certificate-free, through `StochasticToDeterministicLatents.Binary.exists_optimalLatent_w3_le_eight_of_fullSupport`. | [FactorNine](../StochasticToDeterministicLatents/Binary/FactorNine.lean) selects an attained optimizer and a catalog code of cost at most `8*tau(p)`; `w3_le_w3Cost` gives the result. The selected-latent conclusion requires full support. |
| `BIN-C9` | For every binary `2 x 2` law, some deterministic code `g` satisfies `T(p) <= D_p(g) <= 9*tau(p)`. | `kernel-verified` in this repository (2026-09-04), certificate-free, through `StochasticToDeterministicLatents.Binary.exists_code_detScore_le_nine_mul_tau` and `StochasticToDeterministicLatents.Binary.T_le_nine_mul_tau`. | [FactorNine](../StochasticToDeterministicLatents/Binary/FactorNine.lean) prices the full-support witness, uses [SparseLimit](../StochasticToDeterministicLatents/SparseLimit.lean), then finite deterministic attainment. Its named selector bound requires full support. The sparse conclusion contains neither a selected-latent `W3` estimate nor a bound for that selector. |
| `BIN-LAW-SELECTOR` | The determinant/mass/two-arm rule defines a law-only `g_p`; on count or rational input it is an exact finite procedure. | `paper proof` for the full mathematical rule. Selected exact count sublemmas were `kernel-verified` in the reviewed source workspace; the full contract was not. | [Selector](../StochasticToDeterministicLatents/Binary/Selector.lean) and [CountSelector](../StochasticToDeterministicLatents/Binary/CountSelector.lean) provide definitions and audited structural lemmas. No refinement connects the count or rational backend to the mathematical real selector. The latter has a verified C9 bound on full support; the full executable contract remains open. |
| `BIN-CATALOG-RECOVERY` | For a full-support law and a supplied contact or transpose-chart presentation of an optimal latent, the chart-selected constant or high-singleton code has an equal-`W3Cost` representative in the law-defined catalog, including the balanced tie. | `kernel-verified` in this repository (2026-09-03), through `StochasticToDeterministicLatents.Binary.exists_catalogCode_of_contactPresentation` and `StochasticToDeterministicLatents.Binary.exists_catalogCode_of_transposeChartPresentation`. | [CatalogRecovery](../StochasticToDeterministicLatents/Binary/CatalogRecovery.lean) proves the equal-cost recovery at a supplied presentation, including the balanced `W3Cost` tie; the tie is proved for `W3Cost`, not for `D_p`. [NormalForm](../StochasticToDeterministicLatents/Binary/NormalForm.lean) supplies the presentation at the selected optimizer, and [FactorNine](../StochasticToDeterministicLatents/Binary/FactorNine.lean) composes them at factor eight; the law-quantified composition with a catalog code is private there, and only its `W3` weakening is public. The row-major representative need not be equivariant. No sparse-law statement about the selector is part of this row. |
| `GEN-W3-8` | Every arbitrary finite law admits a selected attained optimizer with `W3(L) <= 8*tau(p)`. | `conjecture`. | No proof. See the [general construction problem](blueprint.md#6-the-open-arbitrary-alphabet-factor-nine-route). |
| `GEN-C9` | For arbitrary finite alphabets, `T(p) <= 9*tau(p)`. | `conjecture`; `PRICE(8)` would prove it from `GEN-W3-8`, whose premise remains open. | No proof. The generic sparse transfer still requires a full-support numerical bound for these alphabets. |
| `LOWER-1960` | There exists a law on `Fin 12 x Fin 12` with `T(p)/tau(p) >= 1.960073002187`; hence the best universal finite-alphabet constant `C_*` is at least `1.960073002187`. | External compiler-backed Lean certificate using `native_decide`; not `kernel-verified` under this repository's terminology. | The external [StochToDet1960.exists_lower_bound_1960073002187](https://github.com/satchlj/stoch-to-det-lower/blob/main/StochToDet1960/Proof.lean) supplies the witness. Its compiler-backed verification is not reproduced here. |

## Formal scope

All locally verified rows above are supported by root-imported declarations
in [Verify.lean](../Verify.lean). Each headline has discovered axiom set
`[propext, Classical.choice, Quot.sound]`. The
[admission record](../verification/admissions.md) includes the complete module
coverage and the two smaller axiom sets among supporting theorems.

The canonical code alphabet represents partitions of the observation space.
The library has no public theorem converting an arbitrary-output code into
`BinaryCode` with preserved cost. Likewise, the full-support recovery theorem
uses balanced equality of `W3Cost`; no public declaration states a balanced
`D_p` identity or the cell-relabeling invariance of `detScore` and `T`. Agreement
with the reviewed selector construction is recorded as a source comparison,
not a theorem relating this library to unpublished names.

The [selector refinement contracts](lean-contracts.md#bin-law-selector)
specify the missing count/rational normalization, support, score-key, and
agreement results. Total executable definitions and catalog membership alone
do not discharge that contract.

## Publication rule

Promote a row only when its exact public declaration passes the complete
[local verification procedure](../verification/README.md) and is named here.
A result checked only in another workspace retains that qualifier and its
actual verification mechanism.
