import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.SparseLimit
import StochasticToDeterministicLatents.Binary.FactorNine

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Boundary transfer and binary factor nine" =>

:::group "boundary"
Boundary transfer and binary factor nine.
:::

The boundary transfer acts on the deterministic optimum.

:::theorem "BIN-SPARSE" (parent := "boundary") (lean := "StochasticToDeterministicLatents.T_le_mul_tau_of_forall_fullSupport") (uses := "DEF-LAW, DEF-TAU, DEF-DETSCORE") (tags := "kernel-verified, sub-node")
Fix finite nonempty alphabets and $`C\geq0`. If every full-support probability law on those alphabets satisfies $`T(p)\leq C\tau(p)`, then every probability law on the same alphabets satisfies that bound. This theorem transfers neither a selected-latent cost estimate nor a named-selector guarantee.
:::

:::proof "BIN-SPARSE"
Smooth the law by mixing with the uniform law, smooth an attained latent, and pass the deterministic inequality to the limit. See [proof section 6](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#6-sparse-and-degenerate-laws).
:::

:::theorem "BIN-C9" (parent := "boundary") (lean := "StochasticToDeterministicLatents.Binary.exists_code_detScore_le_nine_mul_tau, StochasticToDeterministicLatents.Binary.T_le_nine_mul_tau") (uses := "BIN-W3-8, PRICE, BIN-SPARSE, DEF-DETSCORE") (tags := "kernel-verified")
For every binary $`2\times2` probability law, some deterministic code $`g` satisfies $`T(p)\leq D_p(g)\leq9\tau(p)`. In particular, $`T(p)\leq9\tau(p)` also holds when cells have zero mass.
:::

:::proof "BIN-C9"
Pricing at $`c=8` gives the full-support bound. Apply the generic boundary transfer at $`C=9`, then finite deterministic attainment. See [proof sections 6 and 7](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#6-sparse-and-degenerate-laws).
:::
