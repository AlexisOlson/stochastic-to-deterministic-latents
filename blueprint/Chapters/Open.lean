import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Binary.CountSelector

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Executable refinement, the binary stochastic optimum, conjectures, and external evidence" =>

:::group "open"
Executable refinement, the binary stochastic optimum, conjectures, and external evidence.
:::

The ledger distinguishes the executable refinement contract from the compiled definitions and the binary numerical theorems. The four paper-proof nodes on the binary stochastic optimum have no Lean declarations; their target signatures are in the [Lean contracts](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/lean-contracts.md#binary-stochastic-optimum), and the [stochastic-optimum page](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/binary-stochastic-optimum.md) holds the proofs.

:::definition "BIN-COUNT-SELECTOR" (parent := "open") (lean := "StochasticToDeterministicLatents.Binary.CountTable, StochasticToDeterministicLatents.Binary.CountTable.realTable, StochasticToDeterministicLatents.Binary.CountTable.catalog, StochasticToDeterministicLatents.Binary.CountTable.selector") (uses := "DEF-SELECTOR") (tags := "definition")
The count backend defines a finite selector using integer products and score keys. Its compiled definition does not establish agreement with the mathematical real selector; that refinement requires the positive-total input condition.
:::

:::definition "BIN-RATIONAL-SELECTOR" (parent := "open") (lean := "StochasticToDeterministicLatents.Binary.RationalTable, StochasticToDeterministicLatents.Binary.RationalTable.toCountTable, StochasticToDeterministicLatents.Binary.RationalTable.realTable, StochasticToDeterministicLatents.Binary.RationalTable.selector") (uses := "DEF-SELECTOR") (tags := "definition")
The rational backend clears denominators and applies the count selector. Its agreement with the mathematical real selector remains an unimplemented refinement target.
:::

:::proposition "BIN-LAW-SELECTOR" (parent := "open") (uses := "DEF-SELECTOR, BIN-COUNT-SELECTOR, BIN-RATIONAL-SELECTOR") (tags := "paper-proof")
The determinant, mass, and two-arm rule defines a law-only selector $`g_p`; on count or rational input it is an exact finite procedure. The ledger assigns paper proof to the full mathematical rule. No refinement theorem connects either backend to the mathematical real selector. The compiled definitions linked as sub-nodes do not prove that contract.
:::

:::proposition "BIN-CONSTANT-TEST" (parent := "open") (uses := "DEF-LAW, DEF-SCORE, DEF-TAU") (tags := "paper-proof")
For a binary law $`p` with nondegenerate marginals, the constant latent is $`\tau`-optimal, so that $`\tau(p)=T(p)=I_p(X;Y)`, if and only if the rational inequalities $`A\geq0`, $`E\geq0`, and $`V^3\leq AEM` hold, where $`A,E,V,M` are explicit rational functions of the four cells. Paper proof; the sympy replay script is not evidence.
:::

:::proposition "BIN-TWO-COMPONENTS" (parent := "open") (uses := "DEF-LATENT, BIN-CONSTANT-TEST") (tags := "paper-proof")
Every $`\tau`-optimal finite latent of a binary law, on any support, carries at most two distinct component laws on its positive-weight labels; merging equal components gives a two-label optimizer. Paper proof, by bounding the contact set of one supporting affine majorant of the concave envelope. The kernel-verified normal form covers the full-support, selected-optimizer case in its own dual-kernel formulation and is corroboration, not an input.
:::

:::proposition "BIN-TAU-EXACT" (parent := "open") (uses := "BIN-CONSTANT-TEST, BIN-TWO-COMPONENTS") (tags := "paper-proof")
For every binary law, $`\tau(p)` and the unique optimal component measure are explicit. Product laws have $`\tau=T=I=0`. Otherwise, after orienting $`ad-bc>0`, the largest nonnegative root $`u_0` of $`u^3-(b+c)u^2-bc\,u-bc\,(a+d)` decides: the constant latent is optimal when $`\sqrt{ad}\leq u_0`, and otherwise the optimizer is the diagonal-swap pair with product $`u_0^2` and $`\tau(p)=\Psi(p)-\Phi(q_+)`. Paper proof; no public declaration computes $`\tau` from a law.
:::

:::proposition "BIN-DISAGREEMENT-BAND" (parent := "open") (uses := "BIN-TAU-EXACT") (tags := "paper-proof")
If the disagreement mass $`p_{01}+p_{10}` lies in $`[1/3,2/3]`, the constant latent is $`\tau`-optimal and $`\tau(p)=T(p)=I_p(X;Y)`; no larger interval in that statistic alone suffices. Paper proof.
:::

:::proposition "BIN-C2" (parent := "open") (uses := "BIN-TAU-EXACT, DEF-DETSCORE") (tags := "paper-proof")
For every binary $`2\times2` law, $`T(p)\leq2\tau(p)`; on full support the constant code or one of the four singleton codes attains $`D_p(g)\leq2\tau(p)`. Paper proof, by comparing the two deterministic scores with the exact stochastic optimum along each contact chord and transferring to zero-cell laws through the kernel-verified sparse limit. The constant is not claimed to be sharp; the only kernel-verified binary constant here is $`9`, and the library holds no binary lower bound above $`1`.
:::

:::proposition "GEN-W3-8" (parent := "open") (uses := "DEF-LAW, DEF-TAU, DEF-W3") (tags := "conjecture")
Every arbitrary finite probability law admits a selected attained optimizer $`L` with $`\operatorname{W3}(L)\leq8\tau(p)`. This remains a conjecture.
:::

:::proposition "GEN-C9" (parent := "open") (uses := "PRICE, GEN-W3-8, DEF-DETSCORE") (tags := "conjecture")
For arbitrary finite alphabets and every probability law $`p`, $`T(p)\leq9\tau(p)`. Pricing at $`c=8` would prove this from the general selected-optimizer estimate, whose premise remains open.
:::

:::proposition "LOWER-1960" (parent := "open") (uses := "DEF-TAU, DEF-DETSCORE") (tags := "external")
There exists a law on $`\operatorname{Fin}(12)\times\operatorname{Fin}(12)` with $`T(p)/\tau(p)\geq1.960073002187`. Thus the infimum $`C_*` of valid universal finite-alphabet constants is at least this number. The [external compiler-backed Lean certificate](https://github.com/satchlj/stoch-to-det-lower/blob/main/StochToDet1960/Proof.lean) is not kernel-verified here, and its verification is not reproduced in this repository.
:::
