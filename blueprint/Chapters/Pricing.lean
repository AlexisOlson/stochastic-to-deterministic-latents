import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Pricing

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Pricing determinization" =>

:::group "pricing"
Pricing determinization.
:::

Pricing compares a supplied latent with a supplied canonical code.

:::theorem "PRICE-IDENTITY" (parent := "pricing") (lean := "StochasticToDeterministicLatents.detScore_eq_latentScore_add_w3Cost_sub_rebate, StochasticToDeterministicLatents.scoreRebate_nonneg, StochasticToDeterministicLatents.detScore_le_latentScore_add_w3Cost") (uses := "DEF-SCORE, DEF-DETSCORE, DEF-W3") (tags := "kernel-verified, sub-node")
For every supplied $`L` representing $`p` and canonical code $`g`, $`D_p(g)=\operatorname{score}_p(L)+\operatorname{W3Cost}_L(g)-2R_L(g)`. Since $`R_L(g)\geq0`, $`D_p(g)\leq\operatorname{score}_p(L)+\operatorname{W3Cost}_L(g)`.
:::

:::proof "PRICE-IDENTITY"
Expand the entropy expressions and cancel terms. Nonnegativity of the four conditional mutual informations permits dropping the rebate. See [blueprint section 2](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/blueprint.md#2-price-the-act-of-determinizing).
:::

:::theorem "PRICE" (parent := "pricing") (lean := "StochasticToDeterministicLatents.T_le_one_add_mul_tau_of_w3") (uses := "PRICE-IDENTITY, DEF-TAU") (tags := "kernel-verified")
For finite alphabets, if $`L` attains $`\tau(p)` and $`\operatorname{W3}(L)\leq c\tau(p)`, then $`T(p)\leq(1+c)\tau(p)`. The constant $`c` is supplied with its cost bound.
:::

:::proof "PRICE"
Minimize the fixed-code inequality over the finite canonical code space and substitute optimality of the supplied latent. This is [PRICE(c) in the ledger](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/claims.md#ledger).
:::
