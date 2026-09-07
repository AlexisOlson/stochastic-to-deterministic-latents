import StochasticToDeterministicLatents.Information
import StochasticToDeterministicLatents.Latent
import StochasticToDeterministicLatents.Deterministic
import StochasticToDeterministicLatents.Bridge
import StochasticToDeterministicLatents.Binary.Table
import StochasticToDeterministicLatents.Binary.Selector
import StochasticToDeterministicLatents.Binary.CountSelector
import StochasticToDeterministicLatents.Pricing
import StochasticToDeterministicLatents.Binary.Symmetry
import StochasticToDeterministicLatents.Binary.Chart
import StochasticToDeterministicLatents.Binary.ContactChart
import StochasticToDeterministicLatents.Binary.TransposeNormalForm
import StochasticToDeterministicLatents.Binary.CatalogRecovery
import StochasticToDeterministicLatents.Binary.NormalForm
import StochasticToDeterministicLatents.SparseLimit
import StochasticToDeterministicLatents.Binary.ScalarEstimates
import StochasticToDeterministicLatents.Binary.Reduction
import StochasticToDeterministicLatents.Binary.FactorNine.NonpositivePhase
import StochasticToDeterministicLatents.Binary.FactorNine.PositivePhase
import StochasticToDeterministicLatents.Binary.FactorNine.SeamEndpoints
import StochasticToDeterministicLatents.Binary.FactorNine
import StochasticToDeterministicLatents.Binary.FactorTwo.Shape
import StochasticToDeterministicLatents.Binary.FactorTwo.Defs
import StochasticToDeterministicLatents.Binary.FactorTwo.Contact
import StochasticToDeterministicLatents.Binary.FactorTwo.Touch
import StochasticToDeterministicLatents.Binary.FactorTwo.RationalTest
import StochasticToDeterministicLatents.Binary.FactorTwo.NormBound
import StochasticToDeterministicLatents.Binary.FactorTwo.Optimum
import StochasticToDeterministicLatents.Binary.FactorTwo.Orientation
import StochasticToDeterministicLatents.Binary.FactorTwo.Chord
import StochasticToDeterministicLatents.Binary.FactorTwo.ChordScalars
import StochasticToDeterministicLatents.Binary.FactorTwo.SingletonScore
import StochasticToDeterministicLatents.Binary.FactorTwo.Margins
import StochasticToDeterministicLatents.Binary.FactorTwo.Gates
import StochasticToDeterministicLatents.Binary.FactorTwo.Strip

/-!
# Stochastic-to-Deterministic Latents

The root exports the finite-information and latent interfaces, deterministic
codes and pricing, binary normal forms, scalar phase estimates, catalog
recovery, and the sparse-law transfer.

`Binary.T_le_nine_mul_tau` proves `T p ≤ 9 * tau p` for every binary
probability law. `Binary.exists_code_detScore_le_nine_mul_tau` supplies a
deterministic witness. On full support,
`Binary.detScore_selector_le_nine_mul_tau_of_fullSupport` bounds the law-only
selector and `Binary.exists_optimalLatent_w3_le_eight_of_fullSupport` supplies
an attained optimal latent with determinization cost at most eight times
`tau p`.

The arbitrary-alphabet factor-nine conjecture retains its separate evidence
tier. See `docs/claims.md` for the claim ledger, `verification/README.md`
for the verification procedure, and `verification/admissions.md` for the
admission record.
-/

namespace StochasticToDeterministicLatents

end StochasticToDeterministicLatents
