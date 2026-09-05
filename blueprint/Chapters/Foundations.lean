import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Information
import StochasticToDeterministicLatents.Latent
import StochasticToDeterministicLatents.Deterministic
import StochasticToDeterministicLatents.Pricing
import StochasticToDeterministicLatents.Binary.Selector

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Laws, information, and codes" =>

:::group "foundations"
Laws, information, and codes.
:::

All information quantities are in bits, with zero contribution from a zero-probability event.

:::definition "DEF-LAW" (parent := "foundations") (lean := "StochasticToDeterministicLatents.IsPMF") (uses := "") (tags := "definition, kernel-verified")
A law on finite alphabets $`\alpha` and $`\beta` is a nonnegative function $`p : \alpha\times\beta\to\mathbb R` with total mass one.
:::

:::definition "DEF-INFO" (parent := "foundations") (lean := "StochasticToDeterministicLatents.entropy, StochasticToDeterministicLatents.entropyOf, StochasticToDeterministicLatents.condEntropy, StochasticToDeterministicLatents.mutualInfo, StochasticToDeterministicLatents.condMutualInfo") (uses := "DEF-LAW") (tags := "definition, kernel-verified")
Entropy $`H`, conditional entropy $`H(\cdot\mid\cdot)`, mutual information $`I(\cdot;\cdot)`, and conditional mutual information $`I(\cdot;\cdot\mid\cdot)` use the public reducible facades. Entropy of a nonnegative finite measure is one-homogeneous; on a probability law it is Shannon entropy.
:::

:::definition "DEF-LATENT" (parent := "foundations") (lean := "StochasticToDeterministicLatents.Latent") (uses := "DEF-LAW") (tags := "definition, kernel-verified")
A finite stochastic latent $`L` is a finite mixture representation of the joint law $`p`, with a prior on latent labels and a conditional law of $`(X,Y)` for each label.
:::

:::definition "DEF-SCORE" (parent := "foundations") (lean := "StochasticToDeterministicLatents.Latent.score") (uses := "DEF-LATENT, DEF-INFO") (tags := "definition, kernel-verified")
The score of a supplied latent is $`\operatorname{score}_p(L)=I(X;Y\mid L)+I(L;X\mid Y)+I(L;Y\mid X)`.
:::

:::definition "DEF-TAU" (parent := "foundations") (lean := "StochasticToDeterministicLatents.tau") (uses := "DEF-SCORE") (tags := "definition, kernel-verified")
The stochastic optimum is $`\tau(p)=\inf_L\operatorname{score}_p(L)`, with the infimum over finite stochastic latents representing $`p`.
:::

:::definition "DEF-CODE" (parent := "foundations") (lean := "StochasticToDeterministicLatents.Code, StochasticToDeterministicLatents.constantCode") (uses := "DEF-LAW") (tags := "definition, kernel-verified")
The canonical code space is $`\operatorname{Code}(\alpha,\beta)=(\alpha\times\beta)\to\operatorname{Fin}(|\alpha\times\beta|)`. There is one available label per observation cell. The constant code induces a single block.
:::

:::definition "DEF-DETSCORE" (parent := "foundations") (lean := "StochasticToDeterministicLatents.detScore, StochasticToDeterministicLatents.T") (uses := "DEF-CODE, DEF-INFO") (tags := "definition, kernel-verified")
A supplied code has score $`D_p(g)=I(X;Y\mid g)+H(g\mid X)+H(g\mid Y)`. The deterministic optimum $`T(p)=\min_g D_p(g)` is the attained finite minimum over canonical codes.
:::

:::definition "DEF-W3" (parent := "foundations") (lean := "StochasticToDeterministicLatents.w3Cost, StochasticToDeterministicLatents.w3, StochasticToDeterministicLatents.scoreRebate") (uses := "DEF-LATENT, DEF-CODE, DEF-INFO") (tags := "definition, kernel-verified")
For a supplied latent and code, $`\operatorname{W3Cost}_L(g)=I(L;(X,Y)\mid g)+3H(g\mid L)` and $`\operatorname{W3}(L)=\min_g\operatorname{W3Cost}_L(g)`. The score rebate $`R_L(g)` is the sum of four conditional mutual informations appearing in the pricing identity.
:::

:::definition "DEF-SELECTOR" (parent := "foundations") (lean := "StochasticToDeterministicLatents.Binary.selector, StochasticToDeterministicLatents.Binary.catalog, StochasticToDeterministicLatents.Binary.determinant, StochasticToDeterministicLatents.Binary.diagonalProduct, StochasticToDeterministicLatents.Binary.offDiagonalProduct, StochasticToDeterministicLatents.Binary.lowerMassEndpoint, StochasticToDeterministicLatents.Binary.activeCell?, StochasticToDeterministicLatents.Binary.RealTable, StochasticToDeterministicLatents.Binary.BinaryCode, StochasticToDeterministicLatents.Binary.rowMajorCells, StochasticToDeterministicLatents.Binary.constantCode, StochasticToDeterministicLatents.Binary.singletonCode, StochasticToDeterministicLatents.Binary.realSupported, StochasticToDeterministicLatents.Binary.canonicalizeWithSupport, StochasticToDeterministicLatents.Binary.canonicalizeRealCode") (uses := "DEF-CODE, DEF-DETSCORE") (tags := "definition, kernel-verified")
For a binary table with nonzero determinant, its sign selects the diagonal or off-diagonal pair. The lower-mass endpoint supplies a singleton; a mass tie uses row-major order. The catalog contains the constant code and this singleton after canonicalization on nonzero support, which is positive support for probability laws. When the determinant is zero, the catalog contains only the constant code. The selector returns the singleton only if its exact deterministic score is smaller; a determinant-zero table or final score tie returns the constant code. This mathematical function is defined classically on arbitrary real tables.
:::
