import Verso
import VersoManual
import VersoBlueprint
import StochasticToDeterministicLatents.Binary.CountSelector

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Executable refinement, general conjectures, and external evidence" =>

:::group "open"
Executable refinement, general conjectures, and external evidence.
:::

The ledger distinguishes the executable refinement contract from the compiled definitions and the binary numerical theorems.

:::definition "BIN-COUNT-SELECTOR" (parent := "open") (lean := "StochasticToDeterministicLatents.Binary.CountTable, StochasticToDeterministicLatents.Binary.CountTable.realTable, StochasticToDeterministicLatents.Binary.CountTable.catalog, StochasticToDeterministicLatents.Binary.CountTable.selector") (uses := "DEF-SELECTOR") (tags := "definition")
The count backend defines a finite selector using integer products and score keys. Its compiled definition does not establish agreement with the mathematical real selector; that refinement requires the positive-total input condition.
:::

:::definition "BIN-RATIONAL-SELECTOR" (parent := "open") (lean := "StochasticToDeterministicLatents.Binary.RationalTable, StochasticToDeterministicLatents.Binary.RationalTable.toCountTable, StochasticToDeterministicLatents.Binary.RationalTable.realTable, StochasticToDeterministicLatents.Binary.RationalTable.selector") (uses := "DEF-SELECTOR") (tags := "definition")
The rational backend clears denominators and applies the count selector. Its agreement with the mathematical real selector remains an unimplemented refinement target.
:::

:::proposition "BIN-LAW-SELECTOR" (parent := "open") (uses := "DEF-SELECTOR, BIN-COUNT-SELECTOR, BIN-RATIONAL-SELECTOR") (tags := "paper-proof")
The determinant, mass, and two-arm rule defines a law-only selector $`g_p`; on count or rational input it is an exact finite procedure. The ledger assigns paper proof to the full mathematical rule. No refinement theorem connects either backend to the mathematical real selector. The compiled definitions linked as sub-nodes do not prove that contract.
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
