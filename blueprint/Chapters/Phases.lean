import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Binary.FactorNine.NonpositivePhase
import StochasticToDeterministicLatents.Binary.FactorNine.PositivePhase
import StochasticToDeterministicLatents.Binary.FactorNine.SeamEndpoints
import StochasticToDeterministicLatents.Binary.FactorNine

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Scalar phases and seam endpoints" =>

:::group "phases"
Scalar phases and seam endpoints.
:::

On a strict scalar contact chart, let $`Q` be its normalization and $`R_H` the high-singleton reward in bits. The scalar quantities satisfy $`\bar K=Q\log(2)I(L;(X,Y))`, $`\bar R=Q\log(2)R_H`, and $`\bar B=Q\log(2)B_q`, where $`B_q` is the sum of the two latent-observable conditional information terms in the latent score.

:::theorem "BIN-PHASE-NONPOS" (parent := "phases") (lean := "StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_eight_mul_mixingSum_of_phaseReward_nonpos") (uses := "DEF-W3, DEF-SCORE") (tags := "kernel-verified, sub-node")
For every scalar contact chart in its strict interior, $`\bar R\leq0` implies $`\bar K\leq8\bar B`. Dividing by the positive factor $`Q\log(2)` gives the corresponding inequality in bits.
:::

:::proof "BIN-PHASE-NONPOS"
Integral comparisons reduce the mixing sum to its equal-mass endpoint and bound the observable information by sixteen times the midpoint contribution. See [proof section 4](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#4-the-nonpositive-phase).
:::

:::theorem "BIN-SEAM-BALANCED" (parent := "phases") (lean := "StochasticToDeterministicLatents.Binary.proxy_pos_at_balancedSeam") (uses := "DEF-INFO") (tags := "kernel-verified, sub-node")
For every $`0<x\leq2/5`, the positive-phase proxy $`J=(5/2)F-A_H` is strictly positive at $`s=2m` and $`\pi=1/2`. Here $`m=x^3/(1+x+x^2)`, and $`F` and $`A_H` use the natural-log normalization of the scalar chart.
:::

:::proof "BIN-SEAM-BALANCED"
The balanced seam estimate follows from a monotonicity argument and exact rational-log bounds at $`x=2/5`. See the [balanced endpoint](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#balanced-endpoint).
:::

:::theorem "BIN-SEAM-LOW-PRIOR" (parent := "phases") (lean := "StochasticToDeterministicLatents.Binary.proxy_pos_at_lowPriorSeam") (uses := "DEF-INFO") (tags := "kernel-verified, sub-node")
For every $`0<x\leq2/5`, the same proxy $`J=(5/2)F-A_H` is strictly positive at $`s=2m` and $`\pi=3x^4`.
:::

:::proof "BIN-SEAM-LOW-PRIOR"
A kernel lower bound, entropy upper bound, and monotonicity reduce the estimate to an exact positive rational-log margin at $`x=2/5`. See the [low-prior endpoint](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#endpoint-pi3r).
:::

:::theorem "BIN-PHASE-POS" (parent := "phases") (lean := "StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos") (uses := "BIN-SEAM-BALANCED, BIN-SEAM-LOW-PRIOR, DEF-W3, DEF-SCORE") (tags := "kernel-verified, sub-node")
Given positivity at both seam endpoints, every scalar contact chart in its strict interior with $`\bar R\geq0` satisfies $`\bar K-\bar R\leq8\bar B`. The two seam nodes discharge those hypotheses. Division by $`Q\log(2)>0` converts the inequality to bits.
:::

:::proof "BIN-PHASE-POS"
The loss split bounds the high-information loss by half the off-diagonal loss. Monotonicity in mass and concavity in the prior reduce the remaining entropy estimate to the two seam endpoints. See [proof section 5](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-nine.md#5-the-positive-phase).
:::

:::theorem "BIN-W3-8" (parent := "phases") (lean := "StochasticToDeterministicLatents.Binary.exists_optimalLatent_w3_le_eight_of_fullSupport") (uses := "BIN-NORMAL-FORM, BIN-PHASE-NONPOS, BIN-PHASE-POS, DEF-W3, DEF-TAU") (tags := "kernel-verified")
Every full-support binary-observable probability law has some attained $`\tau`-optimal latent $`L` with $`\operatorname{W3}(L)\leq8\tau(p)`.
:::

:::proof "BIN-W3-8"
The unary branch has zero cost. In the contact branch the two scalar phases bound the selected chart code, and the minimum cost is at most that code's cost. See [blueprint section 4](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/blueprint.md#4-the-binary-estimate).
:::
