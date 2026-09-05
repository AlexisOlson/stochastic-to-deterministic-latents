import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Binary.NormalForm
import StochasticToDeterministicLatents.Binary.TransposeNormalForm
import StochasticToDeterministicLatents.Binary.Reduction

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Selected binary normal form" =>

:::group "normal-form"
Selected binary normal form.
:::

The selected optimizer supplies the chart on which the scalar estimates apply.

:::theorem "BIN-NORMAL-FORM" (parent := "normal-form") (lean := "StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm, StochasticToDeterministicLatents.Binary.selectedOptimizer_zeroOrContactPresentation") (uses := "DEF-LAW, DEF-LATENT, DEF-TAU, DEF-W3") (tags := "kernel-verified, sub-node")
For each full-support binary probability law, the normal form selects an attained optimal quotient latent. It has either one active component and zero determinization cost, or two active components with an oriented contact presentation. The latter preserves the selected latent's score and transports canonical-code costs.
:::

:::proof "BIN-NORMAL-FORM"
Select an attained optimizer, cluster identical component laws, and orient the two-contact branch. See [proof section 1](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#1-binary-normal-form).
:::

:::theorem "BIN-REDUCE" (parent := "normal-form") (lean := "StochasticToDeterministicLatents.Binary.TransposeChart.min_chartCodes_le_w3Cost") (uses := "DEF-W3, DEF-CODE") (tags := "kernel-verified")
On a supplied positive transposed binary chart, every code in the canonical four-label space is dominated in determinization cost by the constant code or the high-singleton code. The supplied chart need not attain $`\tau(p)`; the public cost theorem quantifies over this canonical code space.
:::

:::proof "BIN-REDUCE"
The finite partition argument merges neutral mass and compares the two tails. See [blueprint section 3](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/blueprint.md#3-why-the-binary-search-collapses). This separate minimality theorem has no dependency edge into the numerical factor-nine bound.
:::
