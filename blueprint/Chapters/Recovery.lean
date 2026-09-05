import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Binary.CatalogRecovery
import StochasticToDeterministicLatents.Binary.FactorNine

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Catalog recovery and the full-support selector" =>

:::group "recovery"
Catalog recovery and the full-support selector.
:::

Catalog recovery connects the code selected on a supplied chart to the catalog defined from the observable law.

:::theorem "BIN-CATALOG-RECOVERY" (parent := "recovery") (lean := "StochasticToDeterministicLatents.Binary.exists_catalogCode_of_contactPresentation, StochasticToDeterministicLatents.Binary.exists_catalogCode_of_transposeChartPresentation") (uses := "DEF-SELECTOR, DEF-W3, DEF-TAU") (tags := "kernel-verified")
For a full-support law and a supplied contact or transpose-chart presentation of an optimal latent, the chart-selected constant or high-singleton code has an equal-cost representative in the law-defined catalog, including the balanced tie. The equality is for $`\operatorname{W3Cost}`.
:::

:::proof "BIN-CATALOG-RECOVERY"
Transport the oriented chart code and recover its support-canonical catalog representative, including the balanced cost tie. The transpose-chart endpoint explicitly assumes $`c<b` and $`ad<bc`; the contact presentation supplies these strict chart inequalities. These theorems carry no numerical constant. See the [catalog recovery contract](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/lean-contracts.md#bin-catalog-recovery).
:::

:::theorem "BIN-SELECTOR-C9" (parent := "recovery") (lean := "StochasticToDeterministicLatents.Binary.detScore_selector_le_nine_mul_tau_of_fullSupport") (uses := "BIN-W3-8, BIN-CATALOG-RECOVERY, PRICE, DEF-SELECTOR") (tags := "kernel-verified, sub-node")
For every full-support binary probability law, the mathematical real-valued selector $`g_p` satisfies $`D_p(g_p)\leq9\tau(p)`.
:::

:::proof "BIN-SELECTOR-C9"
Recover the catalog code from the same selected optimal latent, price it, and use the selector's minimum-score property in the catalog. See [proof section 7](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#7-pricing-and-recovery-from-the-law).
:::
