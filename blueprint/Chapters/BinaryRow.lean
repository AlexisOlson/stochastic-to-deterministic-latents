import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.BinaryRow.FactorTwentySevenQuarters

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The binary-row factor-seven theorem" =>

:::group "binaryrow"
The binary-row factor-seven theorem.
:::

When one alphabet is binary and the other is any finite set, the constant is $`27/4`; since $`27/4<7`, the result is called factor seven. The inequality holds for every such law, and the clause naming the code holds on full support over $`\{0,1\}\times Y`.

:::theorem "BIN-ROW-C27-4" (parent := "binaryrow") (lean := "StochasticToDeterministicLatents.BinaryRow.T_le_twentySevenQuarters_mul_tau, StochasticToDeterministicLatents.BinaryRow.T_le_twentySevenQuarters_mul_tau_col, StochasticToDeterministicLatents.BinaryRow.exists_rowWitnessCode") (uses := "BIN-SPARSE, DEF-TAU, DEF-DETSCORE") (tags := "kernel-verified")
For every law on $`\{0,1\}\times Y` or $`Y\times\{0,1\}` with $`Y` finite and nonempty, $`T(p)\leq(27/4)\tau(p)`. On full support over $`\{0,1\}\times Y` the constant code, the row code, or a purified code of a $`\tau`-optimal latent with positive weights and distinct components has $`D_p(g)\leq(27/4)\tau(p)`. The constant is not claimed to be the least possible, and at $`Y=\{0,1\}` the bound is implied by the factor-two theorem.
:::

:::proof "BIN-ROW-C27-4"
On full support an optimal latent either gives $`\tau(p)=I_p(X;Y)`, where the constant code works, or has two distinct contact components whose row parameters $`s<t` split the argument at $`t/s=16`. Below the split, a variance identity and the replica bound compare the constant and row codes with the score over six bands of the ratio; above it, a purified code of the optimal latent costs at most the score plus three times the label's entropy given the pair, at most $`(1148/173)\tau(p)`. Zero-cell laws follow through the boundary transfer at $`C=27/4`, and the column orientation by transposition. See [the binary-row pages](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-rows-27-4.md).
:::
