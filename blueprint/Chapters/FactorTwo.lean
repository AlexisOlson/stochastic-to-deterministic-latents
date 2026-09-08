import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Binary.FactorTwo
import StochasticToDeterministicLatents.Binary.FactorTwo.Witness

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The binary factor-two theorem" =>

:::group "factortwo"
The binary factor-two theorem.
:::

The factor-two bound is proved along the contact chords, independently of the factor-nine route. Its two clauses are separate theorems: the inequality holds for every binary law, and the clause naming the codes holds on full support.

:::theorem "BIN-C2" (parent := "factortwo") (lean := "StochasticToDeterministicLatents.Binary.T_le_two_mul_tau, StochasticToDeterministicLatents.Binary.exists_witnessCode") (uses := "BIN-TAU-EXACT, BIN-SPARSE, DEF-DETSCORE") (tags := "kernel-verified")
For every binary $`2\times2` law, $`T(p)\leq2\tau(p)`. On full support the constant code or one of the four singleton codes has $`D_p(g)\leq2\tau(p)`. Neither clause is a sharpness claim: no declaration exhibits a law and a code whose score equals $`2\tau(p)`, none locates the isolated cell from the law, and the constant is not claimed to be the least possible. The library holds no binary lower bound above $`1`.
:::

:::proof "BIN-C2"
Compare the two deterministic scores with the exact stochastic optimum along each contact chord, so that one of three gates closes at every chord domain, then transfer to zero-cell laws through the boundary transfer at $`C=2`. The witness clause keeps the two competing codes the chord argument already exhibits and carries the chosen one back along the table symmetries. See [the factor-two page](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-factor-two.md).
:::
