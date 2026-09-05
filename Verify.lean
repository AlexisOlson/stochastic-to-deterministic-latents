import Mathlib.Util.AssertNoSorry
import StochasticToDeterministicLatents

/-!
This is the kernel-audit entry point. Foundational wrappers are checked here as
they enter the public library. Each public theorem endpoint receives an
`assert_no_sorry` check and an exact guarded axiom expectation. Every pinned set
below was discovered by running `#print axioms` after compilation, never written
down in advance; a mismatch is a failed admission until explained.
-/

/-! ## Information -/

assert_no_sorry StochasticToDeterministicLatents.IsPMF.isFiniteMeasure
/-- info: 'StochasticToDeterministicLatents.IsPMF.isFiniteMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.IsPMF.isFiniteMeasure

assert_no_sorry StochasticToDeterministicLatents.entropy_nonneg
/-- info: 'StochasticToDeterministicLatents.entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.entropy_nonneg

assert_no_sorry StochasticToDeterministicLatents.pushforward_isPMF
/-- info: 'StochasticToDeterministicLatents.pushforward_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.pushforward_isPMF

assert_no_sorry StochasticToDeterministicLatents.entropy_pushforward_le
/-- info: 'StochasticToDeterministicLatents.entropy_pushforward_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.entropy_pushforward_le

assert_no_sorry StochasticToDeterministicLatents.entropyOf_equiv
/-- info: 'StochasticToDeterministicLatents.entropyOf_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.entropyOf_equiv

assert_no_sorry StochasticToDeterministicLatents.condEntropy_nonneg
/-- info: 'StochasticToDeterministicLatents.condEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.condEntropy_nonneg

assert_no_sorry StochasticToDeterministicLatents.mutualInfo_nonneg
/-- info: 'StochasticToDeterministicLatents.mutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.mutualInfo_nonneg

assert_no_sorry StochasticToDeterministicLatents.condMutualInfo_nonneg
/-- info: 'StochasticToDeterministicLatents.condMutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.condMutualInfo_nonneg

/-! ## Latent -/

assert_no_sorry StochasticToDeterministicLatents.Latent.joint_isPMF
/-- info: 'StochasticToDeterministicLatents.Latent.joint_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.joint_isPMF

assert_no_sorry StochasticToDeterministicLatents.Latent.score_nonneg
/-- info: 'StochasticToDeterministicLatents.Latent.score_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.score_nonneg

assert_no_sorry StochasticToDeterministicLatents.tau_nonneg
/-- info: 'StochasticToDeterministicLatents.tau_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.tau_nonneg

assert_no_sorry StochasticToDeterministicLatents.tau_le_score
/-- info: 'StochasticToDeterministicLatents.tau_le_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.tau_le_score

/-! ## Deterministic -/

assert_no_sorry StochasticToDeterministicLatents.detScore_nonneg
/-- info: 'StochasticToDeterministicLatents.detScore_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.detScore_nonneg

assert_no_sorry StochasticToDeterministicLatents.T_le_detScore
/-- info: 'StochasticToDeterministicLatents.T_le_detScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.T_le_detScore

assert_no_sorry StochasticToDeterministicLatents.T_nonneg
/-- info: 'StochasticToDeterministicLatents.T_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.T_nonneg

assert_no_sorry StochasticToDeterministicLatents.exists_optimalCode
/-- info: 'StochasticToDeterministicLatents.exists_optimalCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.exists_optimalCode

/-! ## Bridge -/

assert_no_sorry StochasticToDeterministicLatents.detScore_eq_upstream
/-- info: 'StochasticToDeterministicLatents.detScore_eq_upstream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.detScore_eq_upstream

assert_no_sorry StochasticToDeterministicLatents.T_eq_upstream
/-- info: 'StochasticToDeterministicLatents.T_eq_upstream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.T_eq_upstream

assert_no_sorry StochasticToDeterministicLatents.exists_optimalLatent
/-- info: 'StochasticToDeterministicLatents.exists_optimalLatent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.exists_optimalLatent

assert_no_sorry StochasticToDeterministicLatents.latent_score_eq
/-- info: 'StochasticToDeterministicLatents.latent_score_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.latent_score_eq

assert_no_sorry StochasticToDeterministicLatents.entropy_eq_continuousEntropy
/-- info: 'StochasticToDeterministicLatents.entropy_eq_continuousEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.entropy_eq_continuousEntropy

assert_no_sorry StochasticToDeterministicLatents.continuous_continuousEntropy
/-- info: 'StochasticToDeterministicLatents.continuous_continuousEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.continuous_continuousEntropy

assert_no_sorry StochasticToDeterministicLatents.continuous_pushforward
/-- info: 'StochasticToDeterministicLatents.continuous_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.continuous_pushforward

assert_no_sorry StochasticToDeterministicLatents.Latent.ofFunction_isDet
/-- info: 'StochasticToDeterministicLatents.Latent.ofFunction_isDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.ofFunction_isDet

assert_no_sorry StochasticToDeterministicLatents.Latent.ofFunction_score_eq_detScore
/-- info: 'StochasticToDeterministicLatents.Latent.ofFunction_score_eq_detScore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.ofFunction_score_eq_detScore

assert_no_sorry StochasticToDeterministicLatents.contact_support_eq
/-- info: 'StochasticToDeterministicLatents.contact_support_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.contact_support_eq

assert_no_sorry StochasticToDeterministicLatents.exists_seedSetup
/-- info: 'StochasticToDeterministicLatents.exists_seedSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.exists_seedSetup

assert_no_sorry StochasticToDeterministicLatents.SeedSetup.optimal
/-- info: 'StochasticToDeterministicLatents.SeedSetup.optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.SeedSetup.optimal

assert_no_sorry StochasticToDeterministicLatents.SeedSetup.contact
/-- info: 'StochasticToDeterministicLatents.SeedSetup.contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.SeedSetup.contact

assert_no_sorry StochasticToDeterministicLatents.SeedSetup.feasible
/-- info: 'StochasticToDeterministicLatents.SeedSetup.feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.SeedSetup.feasible

assert_no_sorry StochasticToDeterministicLatents.SeedSetup.conn
/-- info: 'StochasticToDeterministicLatents.SeedSetup.conn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.SeedSetup.conn

assert_no_sorry StochasticToDeterministicLatents.SeedSetup.prior_pos
/-- info: 'StochasticToDeterministicLatents.SeedSetup.prior_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.SeedSetup.prior_pos

assert_no_sorry StochasticToDeterministicLatents.SeedSetup.isPMF
/-- info: 'StochasticToDeterministicLatents.SeedSetup.isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.SeedSetup.isPMF

assert_no_sorry StochasticToDeterministicLatents.Clustering.spec
/-- info: 'StochasticToDeterministicLatents.Clustering.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.spec

assert_no_sorry StochasticToDeterministicLatents.Clustering.surj
/-- info: 'StochasticToDeterministicLatents.Clustering.surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.surj

assert_no_sorry StochasticToDeterministicLatents.Clustering.Q_injective
/-- info: 'StochasticToDeterministicLatents.Clustering.Q_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.Q_injective

assert_no_sorry StochasticToDeterministicLatents.Clustering.Q_isContact
/-- info: 'StochasticToDeterministicLatents.Clustering.Q_isContact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.Q_isContact

assert_no_sorry StochasticToDeterministicLatents.exists_clustering
/-- info: 'StochasticToDeterministicLatents.exists_clustering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.exists_clustering

/-! ## Binary.Table -/

assert_no_sorry StochasticToDeterministicLatents.Binary.canonicalizeWithSupport_of_false
/-- info: 'StochasticToDeterministicLatents.Binary.canonicalizeWithSupport_of_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.canonicalizeWithSupport_of_false

assert_no_sorry StochasticToDeterministicLatents.Binary.canonicalizeRealCode_of_eq_zero
/-- info: 'StochasticToDeterministicLatents.Binary.canonicalizeRealCode_of_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.canonicalizeRealCode_of_eq_zero

/-! ## Binary.Selector -/

assert_no_sorry StochasticToDeterministicLatents.Binary.activeCell?_eq_none_iff
/-- info: 'StochasticToDeterministicLatents.Binary.activeCell?_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.activeCell?_eq_none_iff

assert_no_sorry StochasticToDeterministicLatents.Binary.activeCell?_eq_none_of_determinant_eq_zero
/-- info: 'StochasticToDeterministicLatents.Binary.activeCell?_eq_none_of_determinant_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.activeCell?_eq_none_of_determinant_eq_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.selector_eq_constantCode_of_determinant_eq_zero
/-- info: 'StochasticToDeterministicLatents.Binary.selector_eq_constantCode_of_determinant_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selector_eq_constantCode_of_determinant_eq_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.selector_mem_catalog
/-- info: 'StochasticToDeterministicLatents.Binary.selector_mem_catalog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selector_mem_catalog

assert_no_sorry StochasticToDeterministicLatents.Binary.detScore_selector_le_of_mem
/-- info: 'StochasticToDeterministicLatents.Binary.detScore_selector_le_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.detScore_selector_le_of_mem

assert_no_sorry StochasticToDeterministicLatents.Binary.selector_eq_constantCode_of_score_tie
/-- info: 'StochasticToDeterministicLatents.Binary.selector_eq_constantCode_of_score_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selector_eq_constantCode_of_score_tie

/-! ## Binary.CountSelector -/

assert_no_sorry StochasticToDeterministicLatents.Binary.CountTable.canonicalizeCode_of_count_eq_zero
/-- info: 'StochasticToDeterministicLatents.Binary.CountTable.canonicalizeCode_of_count_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.CountTable.canonicalizeCode_of_count_eq_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.CountTable.activeCell?_eq_none_iff
/-- info: 'StochasticToDeterministicLatents.Binary.CountTable.activeCell?_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.CountTable.activeCell?_eq_none_iff

assert_no_sorry StochasticToDeterministicLatents.Binary.CountTable.selector_eq_constantCode_of_products_eq
/-- info: 'StochasticToDeterministicLatents.Binary.CountTable.selector_eq_constantCode_of_products_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.CountTable.selector_eq_constantCode_of_products_eq

assert_no_sorry StochasticToDeterministicLatents.Binary.CountTable.selector_mem_catalog
/-- info: 'StochasticToDeterministicLatents.Binary.CountTable.selector_mem_catalog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.CountTable.selector_mem_catalog

/-! ## Pricing -/

assert_no_sorry StochasticToDeterministicLatents.w3_le_w3Cost
/-- info: 'StochasticToDeterministicLatents.w3_le_w3Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.w3_le_w3Cost

assert_no_sorry StochasticToDeterministicLatents.exists_optimalW3Code
/-- info: 'StochasticToDeterministicLatents.exists_optimalW3Code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.exists_optimalW3Code

assert_no_sorry StochasticToDeterministicLatents.detScore_eq_latentScore_add_w3Cost_sub_rebate
/-- info: 'StochasticToDeterministicLatents.detScore_eq_latentScore_add_w3Cost_sub_rebate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.detScore_eq_latentScore_add_w3Cost_sub_rebate

assert_no_sorry StochasticToDeterministicLatents.scoreRebate_nonneg
/-- info: 'StochasticToDeterministicLatents.scoreRebate_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.scoreRebate_nonneg

assert_no_sorry StochasticToDeterministicLatents.detScore_le_latentScore_add_w3Cost
/-- info: 'StochasticToDeterministicLatents.detScore_le_latentScore_add_w3Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.detScore_le_latentScore_add_w3Cost

assert_no_sorry StochasticToDeterministicLatents.T_le_one_add_mul_tau_of_w3
/-- info: 'StochasticToDeterministicLatents.T_le_one_add_mul_tau_of_w3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.T_le_one_add_mul_tau_of_w3

/-! ## Binary.Symmetry -/

assert_no_sorry StochasticToDeterministicLatents.Binary.TableSymmetry.normalize_equiv
/-- info: 'StochasticToDeterministicLatents.Binary.TableSymmetry.normalize_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TableSymmetry.normalize_equiv

assert_no_sorry StochasticToDeterministicLatents.Binary.TableSymmetry.inverse_equiv
/-- info: 'StochasticToDeterministicLatents.Binary.TableSymmetry.inverse_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TableSymmetry.inverse_equiv

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_apply_equiv
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_apply_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_apply_equiv

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_pos
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_symm_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_symm_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_symm_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_trans
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_trans

assert_no_sorry StochasticToDeterministicLatents.Binary.transportCode_transportCode
/-- info: 'StochasticToDeterministicLatents.Binary.transportCode_transportCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.transportCode_transportCode

assert_no_sorry StochasticToDeterministicLatents.Binary.transportCode_constantCode
/-- info: 'StochasticToDeterministicLatents.Binary.transportCode_constantCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.transportCode_constantCode

assert_no_sorry StochasticToDeterministicLatents.Binary.transportCode_singletonCode
/-- info: 'StochasticToDeterministicLatents.Binary.transportCode_singletonCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.transportCode_singletonCode

assert_no_sorry StochasticToDeterministicLatents.Binary.entropyOf_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.entropyOf_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.entropyOf_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.condEntropy_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.condEntropy_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.condEntropy_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.condMutualInfo_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.condMutualInfo_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.condMutualInfo_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.condMutualInfo_congr_equiv
/-- info: 'StochasticToDeterministicLatents.Binary.condMutualInfo_congr_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.condMutualInfo_congr_equiv

assert_no_sorry StochasticToDeterministicLatents.Binary.condEntropy_congr_equiv
/-- info: 'StochasticToDeterministicLatents.Binary.condEntropy_congr_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.condEntropy_congr_equiv

assert_no_sorry StochasticToDeterministicLatents.Binary.detScore_relabelCodeLabels
/-- info: 'StochasticToDeterministicLatents.Binary.detScore_relabelCodeLabels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.detScore_relabelCodeLabels

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_relabelCodeLabels
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_relabelCodeLabels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_relabelCodeLabels

assert_no_sorry StochasticToDeterministicLatents.Latent.relabel_joint
/-- info: 'StochasticToDeterministicLatents.Latent.relabel_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.relabel_joint

assert_no_sorry StochasticToDeterministicLatents.Latent.pullback_joint
/-- info: 'StochasticToDeterministicLatents.Latent.pullback_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.pullback_joint

assert_no_sorry StochasticToDeterministicLatents.Latent.reindex_joint
/-- info: 'StochasticToDeterministicLatents.Latent.reindex_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.reindex_joint

assert_no_sorry StochasticToDeterministicLatents.Latent.pullback_relabel_joint
/-- info: 'StochasticToDeterministicLatents.Latent.pullback_relabel_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.pullback_relabel_joint

assert_no_sorry StochasticToDeterministicLatents.Latent.score_relabel
/-- info: 'StochasticToDeterministicLatents.Latent.score_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.score_relabel

assert_no_sorry StochasticToDeterministicLatents.Latent.score_pullback
/-- info: 'StochasticToDeterministicLatents.Latent.score_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.score_pullback

assert_no_sorry StochasticToDeterministicLatents.Latent.score_reindex
/-- info: 'StochasticToDeterministicLatents.Latent.score_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.score_reindex

assert_no_sorry StochasticToDeterministicLatents.Binary.tau_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.tau_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.tau_pushforward

assert_no_sorry StochasticToDeterministicLatents.Latent.score_eq_tau_relabel
/-- info: 'StochasticToDeterministicLatents.Latent.score_eq_tau_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.score_eq_tau_relabel

assert_no_sorry StochasticToDeterministicLatents.Latent.score_eq_tau_pullback
/-- info: 'StochasticToDeterministicLatents.Latent.score_eq_tau_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Latent.score_eq_tau_pullback

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_relabel
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_relabel

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_pullback
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_pullback

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_pullback_inverse
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_pullback_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_pullback_inverse

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_reindex
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_reindex

assert_no_sorry StochasticToDeterministicLatents.Binary.w3_relabel
/-- info: 'StochasticToDeterministicLatents.Binary.w3_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3_relabel

assert_no_sorry StochasticToDeterministicLatents.Binary.w3_pullback
/-- info: 'StochasticToDeterministicLatents.Binary.w3_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3_pullback

assert_no_sorry StochasticToDeterministicLatents.Binary.w3_reindex
/-- info: 'StochasticToDeterministicLatents.Binary.w3_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3_reindex

assert_no_sorry StochasticToDeterministicLatents.Binary.feasible_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.feasible_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.feasible_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.isContact_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.isContact_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.isContact_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.univ_isConnected
/-- info: 'StochasticToDeterministicLatents.Binary.univ_isConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.univ_isConnected

assert_no_sorry StochasticToDeterministicLatents.Binary.support_eq_univ_of_pos
/-- info: 'StochasticToDeterministicLatents.Binary.support_eq_univ_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.support_eq_univ_of_pos

/-! ## Binary.Chart -/

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.pi_lt_one
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.pi_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.pi_lt_one

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.prior_zero
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.prior_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.prior_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.prior_one
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.prior_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.prior_one

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.prior_zero_pos
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.prior_zero_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.prior_zero_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.prior_one_pos
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.prior_one_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.prior_one_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.firstComponent_isPMF
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.firstComponent_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.firstComponent_isPMF

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.secondComponent_isPMF
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.secondComponent_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.secondComponent_isPMF

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.prior_isPMF
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.prior_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.prior_isPMF

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.law_isPMF
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.law_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.law_isPMF

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_eq_observableInfo_sub_codeReward
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_eq_observableInfo_sub_codeReward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_eq_observableInfo_sub_codeReward

assert_no_sorry StochasticToDeterministicLatents.Binary.codeReward_constantCode
/-- info: 'StochasticToDeterministicLatents.Binary.codeReward_constantCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.codeReward_constantCode

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_constantCode
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_constantCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_constantCode

assert_no_sorry StochasticToDeterministicLatents.Binary.phaseSelector_eq_singletonCode_of_codeReward_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.phaseSelector_eq_singletonCode_of_codeReward_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.phaseSelector_eq_singletonCode_of_codeReward_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.phaseSelector_eq_constantCode_of_codeReward_neg
/-- info: 'StochasticToDeterministicLatents.Binary.phaseSelector_eq_constantCode_of_codeReward_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.phaseSelector_eq_constantCode_of_codeReward_neg

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_phaseSelector_eq_observableInfo_sub_max
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_phaseSelector_eq_observableInfo_sub_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_phaseSelector_eq_observableInfo_sub_max

/-! ## Binary.ContactChart -/

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.y_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.y_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.y_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.r_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.r_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.r_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.r_le_one
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.r_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.r_le_one

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.highMass_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.highMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.highMass_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.s_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.s_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.s_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.denominator_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.denominator_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.denominator_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.ratio_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.ratio_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.ratio_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.contact_eq
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.contact_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.contact_eq

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.s_le_y
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.s_le_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.s_le_y

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.contact_shifted
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.contact_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.contact_shifted

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.e_add_ell
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.e_add_ell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.e_add_ell

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.e_add_ell_add_s
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.e_add_ell_add_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.e_add_ell_add_s

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_e
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_e

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_r
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_r

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_one
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_sub_one

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.e_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.e_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.e_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.ell_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.ell_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.ell_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.e_le_ell
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.e_le_ell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.e_le_ell

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.e_lt_norm
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.e_lt_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.e_lt_norm

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.r_lt_norm
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.r_lt_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.r_lt_norm

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.one_lt_norm
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.one_lt_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.one_lt_norm

assert_no_sorry StochasticToDeterministicLatents.Binary.xLogX_zero
/-- info: 'StochasticToDeterministicLatents.Binary.xLogX_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.xLogX_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.xLogX_one
/-- info: 'StochasticToDeterministicLatents.Binary.xLogX_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.xLogX_one

assert_no_sorry StochasticToDeterministicLatents.Binary.continuous_xLogX
/-- info: 'StochasticToDeterministicLatents.Binary.continuous_xLogX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.continuous_xLogX

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_zero_left
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_zero_left

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_zero_right
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_zero_right

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_comm
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_comm

assert_no_sorry StochasticToDeterministicLatents.Binary.continuous_pairEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.continuous_pairEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.continuous_pairEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.splitEntropy_eq_pairEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.splitEntropy_eq_pairEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.splitEntropy_eq_pairEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.splitEntropy_zero
/-- info: 'StochasticToDeterministicLatents.Binary.splitEntropy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.splitEntropy_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.splitEntropy_self
/-- info: 'StochasticToDeterministicLatents.Binary.splitEntropy_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.splitEntropy_self

assert_no_sorry StochasticToDeterministicLatents.Binary.splitEntropy_symm
/-- info: 'StochasticToDeterministicLatents.Binary.splitEntropy_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.splitEntropy_symm

assert_no_sorry StochasticToDeterministicLatents.Binary.continuous_splitEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.continuous_splitEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.continuous_splitEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_xLogX
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_xLogX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_xLogX

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_left
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_left

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_right
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_right

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_expand
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_expand

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.contactEntropyGap_expand
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.contactEntropyGap_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.contactEntropyGap_expand

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.mixingTerm_expand
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.mixingTerm_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.mixingTerm_expand

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.mixingSum_expand
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.mixingSum_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.mixingSum_expand

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.phaseReward_eq_splitEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.phaseReward_eq_splitEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.phaseReward_eq_splitEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.strictInterior_gates_of_contactEquation
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.strictInterior_gates_of_contactEquation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.strictInterior_gates_of_contactEquation

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_coordinates
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_coordinates

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_strictInterior
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_strictInterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_strictInterior

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_law
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.toScalarChart_law

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.phaseReward_eq_highInformation_sub_three_mul_highConditionalEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.phaseReward_eq_highInformation_sub_three_mul_highConditionalEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.phaseReward_eq_highInformation_sub_three_mul_highConditionalEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.offDiagonalLoss_eq_highInformationLoss_add_lowInformationLoss
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.offDiagonalLoss_eq_highInformationLoss_add_lowInformationLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.offDiagonalLoss_eq_highInformationLoss_add_lowInformationLoss

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss_of_orientation
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss_of_orientation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss_of_orientation

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.lowInformation_le_highInformation
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.lowInformation_le_highInformation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.lowInformation_le_highInformation

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss_of_information_order
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss_of_information_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss_of_information_order

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss

assert_no_sorry StochasticToDeterministicLatents.Binary.norm_mul_binEntropy_div
/-- info: 'StochasticToDeterministicLatents.Binary.norm_mul_binEntropy_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.norm_mul_binEntropy_div

assert_no_sorry StochasticToDeterministicLatents.Binary.norm_mul_negMulLog_div
/-- info: 'StochasticToDeterministicLatents.Binary.norm_mul_negMulLog_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.norm_mul_negMulLog_div

assert_no_sorry StochasticToDeterministicLatents.Binary.log_two_mul_codeReward_singleton
/-- info: 'StochasticToDeterministicLatents.Binary.log_two_mul_codeReward_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_two_mul_codeReward_singleton

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_mul_log_two_mul_observableInfo_eq
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_mul_log_two_mul_observableInfo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_mul_log_two_mul_observableInfo_eq

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_mul_log_two_mul_score_eq_contactEntropyGap_add_mixingSum
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_mul_log_two_mul_score_eq_contactEntropyGap_add_mixingSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.norm_mul_log_two_mul_score_eq_contactEntropyGap_add_mixingSum

assert_no_sorry StochasticToDeterministicLatents.Binary.norm_mul_scalarSingletonReward_eq_splitEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.norm_mul_scalarSingletonReward_eq_splitEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.norm_mul_scalarSingletonReward_eq_splitEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_codeReward_singleton_eq_phaseReward
/-- info: 'StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_codeReward_singleton_eq_phaseReward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_codeReward_singleton_eq_phaseReward

assert_no_sorry StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_max_eq_max_mul
/-- info: 'StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_max_eq_max_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_max_eq_max_mul

assert_no_sorry StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_w3Cost_phaseSelector_eq_of_observableInfo
/-- info: 'StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_w3Cost_phaseSelector_eq_of_observableInfo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.norm_mul_log_two_mul_w3Cost_phaseSelector_eq_of_observableInfo

/-! ## Binary.TransposeNormalForm -/

assert_no_sorry StochasticToDeterministicLatents.Clustering.quotientLatent_score_eq
/-- info: 'StochasticToDeterministicLatents.Clustering.quotientLatent_score_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.quotientLatent_score_eq

assert_no_sorry StochasticToDeterministicLatents.Clustering.quotientLatent_w3Cost_eq
/-- info: 'StochasticToDeterministicLatents.Clustering.quotientLatent_w3Cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.quotientLatent_w3Cost_eq

assert_no_sorry StochasticToDeterministicLatents.Clustering.quotientLatent_w3_eq
/-- info: 'StochasticToDeterministicLatents.Clustering.quotientLatent_w3_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.quotientLatent_w3_eq

assert_no_sorry StochasticToDeterministicLatents.Clustering.s_pos
/-- info: 'StochasticToDeterministicLatents.Clustering.s_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Clustering.s_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_fullSupport_seedSetup
/-- info: 'StochasticToDeterministicLatents.Binary.exists_fullSupport_seedSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_fullSupport_seedSetup

assert_no_sorry StochasticToDeterministicLatents.Binary.clustering_three_indices_duplicate
/-- info: 'StochasticToDeterministicLatents.Binary.clustering_three_indices_duplicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.clustering_three_indices_duplicate

assert_no_sorry StochasticToDeterministicLatents.Binary.positiveCubeRootIdentities
/-- info: 'StochasticToDeterministicLatents.Binary.positiveCubeRootIdentities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.positiveCubeRootIdentities

assert_no_sorry StochasticToDeterministicLatents.Binary.twoThirdsPowerMaximum
/-- info: 'StochasticToDeterministicLatents.Binary.twoThirdsPowerMaximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoThirdsPowerMaximum

assert_no_sorry StochasticToDeterministicLatents.Binary.rowMarginal_eq_sum
/-- info: 'StochasticToDeterministicLatents.Binary.rowMarginal_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.rowMarginal_eq_sum

assert_no_sorry StochasticToDeterministicLatents.Binary.columnMarginal_eq_sum
/-- info: 'StochasticToDeterministicLatents.Binary.columnMarginal_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.columnMarginal_eq_sum

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_fst_eq_rowMarginal
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_fst_eq_rowMarginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_fst_eq_rowMarginal

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_snd_eq_columnMarginal
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_snd_eq_columnMarginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_snd_eq_columnMarginal

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryPMF_sum
/-- info: 'StochasticToDeterministicLatents.Binary.binaryPMF_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryPMF_sum

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryPMF_some_pos
/-- info: 'StochasticToDeterministicLatents.Binary.binaryPMF_some_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryPMF_some_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.positive_twoTerm_rpow
/-- info: 'StochasticToDeterministicLatents.Binary.positive_twoTerm_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.positive_twoTerm_rpow

assert_no_sorry StochasticToDeterministicLatents.Binary.cubeLaw_isPMF
/-- info: 'StochasticToDeterministicLatents.Binary.cubeLaw_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.cubeLaw_isPMF

assert_no_sorry StochasticToDeterministicLatents.Binary.oneThird_rpow_cube
/-- info: 'StochasticToDeterministicLatents.Binary.oneThird_rpow_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.oneThird_rpow_cube

assert_no_sorry StochasticToDeterministicLatents.Binary.twoThirds_rpow_cube
/-- info: 'StochasticToDeterministicLatents.Binary.twoThirds_rpow_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoThirds_rpow_cube

assert_no_sorry StochasticToDeterministicLatents.Binary.twoThirds_root_le_one
/-- info: 'StochasticToDeterministicLatents.Binary.twoThirds_root_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoThirds_root_le_one

assert_no_sorry StochasticToDeterministicLatents.Binary.twoThirds_eq_one_bestResponse
/-- info: 'StochasticToDeterministicLatents.Binary.twoThirds_eq_one_bestResponse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoThirds_eq_one_bestResponse

assert_no_sorry StochasticToDeterministicLatents.Binary.lambda_univ_eq_rows
/-- info: 'StochasticToDeterministicLatents.Binary.lambda_univ_eq_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lambda_univ_eq_rows

assert_no_sorry StochasticToDeterministicLatents.Binary.lambda_univ_eq_columns
/-- info: 'StochasticToDeterministicLatents.Binary.lambda_univ_eq_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lambda_univ_eq_columns

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_lambda_eq_one
/-- info: 'StochasticToDeterministicLatents.Binary.contact_lambda_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_lambda_eq_one

assert_no_sorry StochasticToDeterministicLatents.Binary.normalized_cubeParameter_rpow_scale
/-- info: 'StochasticToDeterministicLatents.Binary.normalized_cubeParameter_rpow_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.normalized_cubeParameter_rpow_scale

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_hasRowCubeParameter
/-- info: 'StochasticToDeterministicLatents.Binary.contact_hasRowCubeParameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_hasRowCubeParameter

assert_no_sorry StochasticToDeterministicLatents.Binary.feasibilityExpression_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.feasibilityExpression_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.feasibilityExpression_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.swapBitLaw_isPMF
/-- info: 'StochasticToDeterministicLatents.Binary.swapBitLaw_isPMF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.swapBitLaw_isPMF

assert_no_sorry StochasticToDeterministicLatents.Binary.nested_twoThirds_endpoint_strict
/-- info: 'StochasticToDeterministicLatents.Binary.nested_twoThirds_endpoint_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.nested_twoThirds_endpoint_strict

assert_no_sorry StochasticToDeterministicLatents.Binary.feasible_row_endpoint_strict
/-- info: 'StochasticToDeterministicLatents.Binary.feasible_row_endpoint_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.feasible_row_endpoint_strict

assert_no_sorry StochasticToDeterministicLatents.Binary.feasibilityEndpointCoefficients_positive
/-- info: 'StochasticToDeterministicLatents.Binary.feasibilityEndpointCoefficients_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.feasibilityEndpointCoefficients_positive

assert_no_sorry StochasticToDeterministicLatents.Binary.contactParameter_bestResponse
/-- info: 'StochasticToDeterministicLatents.Binary.contactParameter_bestResponse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactParameter_bestResponse

assert_no_sorry StochasticToDeterministicLatents.Binary.contactParameter_injective
/-- info: 'StochasticToDeterministicLatents.Binary.contactParameter_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactParameter_injective

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_rowMarginal_eq_coefficient_cube
/-- info: 'StochasticToDeterministicLatents.Binary.contact_rowMarginal_eq_coefficient_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_rowMarginal_eq_coefficient_cube

assert_no_sorry StochasticToDeterministicLatents.Binary.distinctContacts_haveDistinctKernelNodes
/-- info: 'StochasticToDeterministicLatents.Binary.distinctContacts_haveDistinctKernelNodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.distinctContacts_haveDistinctKernelNodes

assert_no_sorry StochasticToDeterministicLatents.Binary.positiveRoot_square_dvd
/-- info: 'StochasticToDeterministicLatents.Binary.positiveRoot_square_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.positiveRoot_square_dvd

assert_no_sorry StochasticToDeterministicLatents.Binary.threePositiveDoubleRoots_impossible
/-- info: 'StochasticToDeterministicLatents.Binary.threePositiveDoubleRoots_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.threePositiveDoubleRoots_impossible

assert_no_sorry StochasticToDeterministicLatents.Binary.twoContactPolynomial_factorization
/-- info: 'StochasticToDeterministicLatents.Binary.twoContactPolynomial_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoContactPolynomial_factorization

assert_no_sorry StochasticToDeterministicLatents.Binary.twoNode_hankel_identity
/-- info: 'StochasticToDeterministicLatents.Binary.twoNode_hankel_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoNode_hankel_identity

assert_no_sorry StochasticToDeterministicLatents.Binary.factor_hankel_normalForm
/-- info: 'StochasticToDeterministicLatents.Binary.factor_hankel_normalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.factor_hankel_normalForm

assert_no_sorry StochasticToDeterministicLatents.Binary.symmetric_bestResponse_swaps_roots
/-- info: 'StochasticToDeterministicLatents.Binary.symmetric_bestResponse_swaps_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.symmetric_bestResponse_swaps_roots

assert_no_sorry StochasticToDeterministicLatents.Binary.twoNode_recurrence_unique
/-- info: 'StochasticToDeterministicLatents.Binary.twoNode_recurrence_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoNode_recurrence_unique

assert_no_sorry StochasticToDeterministicLatents.Binary.twoContact_momentIdentities
/-- info: 'StochasticToDeterministicLatents.Binary.twoContact_momentIdentities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoContact_momentIdentities

assert_no_sorry StochasticToDeterministicLatents.Binary.positiveTwoCube_decomposition_unique
/-- info: 'StochasticToDeterministicLatents.Binary.positiveTwoCube_decomposition_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.positiveTwoCube_decomposition_unique

assert_no_sorry StochasticToDeterministicLatents.Binary.symmetricKernel_reconstruction
/-- info: 'StochasticToDeterministicLatents.Binary.symmetricKernel_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.symmetricKernel_reconstruction

assert_no_sorry StochasticToDeterministicLatents.Binary.transposePair_canOrientOffDiagonal
/-- info: 'StochasticToDeterministicLatents.Binary.transposePair_canOrientOffDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.transposePair_canOrientOffDiagonal

assert_no_sorry StochasticToDeterministicLatents.Binary.feasible_pushforwardAlongChart
/-- info: 'StochasticToDeterministicLatents.Binary.feasible_pushforwardAlongChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.feasible_pushforwardAlongChart

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_pushforwardAlongChart
/-- info: 'StochasticToDeterministicLatents.Binary.contact_pushforwardAlongChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_pushforwardAlongChart

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_transposeOf_symmetricKernel
/-- info: 'StochasticToDeterministicLatents.Binary.contact_transposeOf_symmetricKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_transposeOf_symmetricKernel

assert_no_sorry StochasticToDeterministicLatents.Binary.feasibilityPolynomial_eval
/-- info: 'StochasticToDeterministicLatents.Binary.feasibilityPolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.feasibilityPolynomial_eval

assert_no_sorry StochasticToDeterministicLatents.Binary.rowCubeParameter_swapColumns
/-- info: 'StochasticToDeterministicLatents.Binary.rowCubeParameter_swapColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.rowCubeParameter_swapColumns

assert_no_sorry StochasticToDeterministicLatents.Binary.bestResponse_quotient
/-- info: 'StochasticToDeterministicLatents.Binary.bestResponse_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.bestResponse_quotient

assert_no_sorry StochasticToDeterministicLatents.Binary.transposeNormalFormInputs_of_conditions
/-- info: 'StochasticToDeterministicLatents.Binary.transposeNormalFormInputs_of_conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.transposeNormalFormInputs_of_conditions

assert_no_sorry StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm_of_inputs
/-- info: 'StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm_of_inputs

assert_no_sorry StochasticToDeterministicLatents.Binary.allNormalFormConditions
/-- info: 'StochasticToDeterministicLatents.Binary.allNormalFormConditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.allNormalFormConditions

assert_no_sorry StochasticToDeterministicLatents.Binary.transposeNormalFormInputs_hold
/-- info: 'StochasticToDeterministicLatents.Binary.transposeNormalFormInputs_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.transposeNormalFormInputs_hold

assert_no_sorry StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm
/-- info: 'StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selectedOptimizerNormalForm

/-! ## Binary.CatalogRecovery -/

assert_no_sorry StochasticToDeterministicLatents.Binary.catalog_eq_zeroSupportForm
/-- info: 'StochasticToDeterministicLatents.Binary.catalog_eq_zeroSupportForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.catalog_eq_zeroSupportForm

assert_no_sorry StochasticToDeterministicLatents.Binary.selector_eq_zeroSupportForm
/-- info: 'StochasticToDeterministicLatents.Binary.selector_eq_zeroSupportForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selector_eq_zeroSupportForm

assert_no_sorry StochasticToDeterministicLatents.Binary.canonicalizeRealCode_singleton_of_pos
/-- info: 'StochasticToDeterministicLatents.Binary.canonicalizeRealCode_singleton_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.canonicalizeRealCode_singleton_of_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_canonicalizeRealCode_singleton_of_pos
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_canonicalizeRealCode_singleton_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_canonicalizeRealCode_singleton_of_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.constantCode_mem_catalog
/-- info: 'StochasticToDeterministicLatents.Binary.constantCode_mem_catalog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.constantCode_mem_catalog

assert_no_sorry StochasticToDeterministicLatents.Binary.canonicalized_activeSingleton_mem_catalog
/-- info: 'StochasticToDeterministicLatents.Binary.canonicalized_activeSingleton_mem_catalog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.canonicalized_activeSingleton_mem_catalog

assert_no_sorry StochasticToDeterministicLatents.Binary.activeCell_mem_activeEndpointOrbit
/-- info: 'StochasticToDeterministicLatents.Binary.activeCell_mem_activeEndpointOrbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.activeCell_mem_activeEndpointOrbit

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_activeCell_of_activeEndpointOrbit_nonempty
/-- info: 'StochasticToDeterministicLatents.Binary.exists_activeCell_of_activeEndpointOrbit_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_activeCell_of_activeEndpointOrbit_nonempty

assert_no_sorry StochasticToDeterministicLatents.Binary.activeEndpointOrbit_pushforward
/-- info: 'StochasticToDeterministicLatents.Binary.activeEndpointOrbit_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.activeEndpointOrbit_pushforward

assert_no_sorry StochasticToDeterministicLatents.Binary.halfPrior_transpose_joint_eq_reindex
/-- info: 'StochasticToDeterministicLatents.Binary.halfPrior_transpose_joint_eq_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.halfPrior_transpose_joint_eq_reindex

assert_no_sorry StochasticToDeterministicLatents.Binary.halfPrior_singleton10_w3Cost_eq_singleton01
/-- info: 'StochasticToDeterministicLatents.Binary.halfPrior_singleton10_w3Cost_eq_singleton01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.halfPrior_singleton10_w3Cost_eq_singleton01

assert_no_sorry StochasticToDeterministicLatents.Binary.w3Cost_eq_of_jointPresentation
/-- info: 'StochasticToDeterministicLatents.Binary.w3Cost_eq_of_jointPresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3Cost_eq_of_jointPresentation

assert_no_sorry StochasticToDeterministicLatents.Binary.w3_eq_of_jointPresentation
/-- info: 'StochasticToDeterministicLatents.Binary.w3_eq_of_jointPresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3_eq_of_jointPresentation

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_catalogCode_of_transposeChartPresentation
/-- info: 'StochasticToDeterministicLatents.Binary.exists_catalogCode_of_transposeChartPresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_catalogCode_of_transposeChartPresentation

assert_no_sorry StochasticToDeterministicLatents.Binary.QuotientPresentation.joint_eq_reindex
/-- info: 'StochasticToDeterministicLatents.Binary.QuotientPresentation.joint_eq_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.QuotientPresentation.joint_eq_reindex

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.diagonalProduct_lt_offDiagonalProduct
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.diagonalProduct_lt_offDiagonalProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.diagonalProduct_lt_offDiagonalProduct

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_catalogCode_of_contactPresentation
/-- info: 'StochasticToDeterministicLatents.Binary.exists_catalogCode_of_contactPresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_catalogCode_of_contactPresentation

/-! ## Binary.NormalForm -/

assert_no_sorry StochasticToDeterministicLatents.Binary.chartTableSymmetry_agreesWithCellEquiv
/-- info: 'StochasticToDeterministicLatents.Binary.chartTableSymmetry_agreesWithCellEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.chartTableSymmetry_agreesWithCellEquiv

assert_no_sorry StochasticToDeterministicLatents.Binary.antiDiagonalSymmetry_commutes_transpose
/-- info: 'StochasticToDeterministicLatents.Binary.antiDiagonalSymmetry_commutes_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.antiDiagonalSymmetry_commutes_transpose

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_antiDiagonal_transpose
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_antiDiagonal_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_antiDiagonal_transpose

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_antiDiagonal_tableOfEntries
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_antiDiagonal_tableOfEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_antiDiagonal_tableOfEntries

assert_no_sorry StochasticToDeterministicLatents.Binary.contactK0_pos
/-- info: 'StochasticToDeterministicLatents.Binary.contactK0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactK0_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.contactR_pos
/-- info: 'StochasticToDeterministicLatents.Binary.contactR_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactR_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.contactX_pos_lt_one
/-- info: 'StochasticToDeterministicLatents.Binary.contactX_pos_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactX_pos_lt_one

assert_no_sorry StochasticToDeterministicLatents.Binary.contactX_sq
/-- info: 'StochasticToDeterministicLatents.Binary.contactX_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactX_sq

assert_no_sorry StochasticToDeterministicLatents.Binary.contactX_pow_four
/-- info: 'StochasticToDeterministicLatents.Binary.contactX_pow_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactX_pow_four

assert_no_sorry StochasticToDeterministicLatents.Binary.contactA0_pos
/-- info: 'StochasticToDeterministicLatents.Binary.contactA0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactA0_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.contactD0_pos
/-- info: 'StochasticToDeterministicLatents.Binary.contactD0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactD0_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_root_identity
/-- info: 'StochasticToDeterministicLatents.Binary.contact_root_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_root_identity

assert_no_sorry StochasticToDeterministicLatents.Binary.contactA0_le_contactD0_iff
/-- info: 'StochasticToDeterministicLatents.Binary.contactA0_le_contactD0_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactA0_le_contactD0_iff

assert_no_sorry StochasticToDeterministicLatents.Binary.contactD0_lt_contactA0_iff
/-- info: 'StochasticToDeterministicLatents.Binary.contactD0_lt_contactA0_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactD0_lt_contactA0_iff

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_twoContactRootKernelModel
/-- info: 'StochasticToDeterministicLatents.Binary.exists_twoContactRootKernelModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_twoContactRootKernelModel

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_eq_rootLaw
/-- info: 'StochasticToDeterministicLatents.Binary.contact_eq_rootLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_eq_rootLaw

assert_no_sorry StochasticToDeterministicLatents.Binary.rootLaw_eq_normalizedContactTable
/-- info: 'StochasticToDeterministicLatents.Binary.rootLaw_eq_normalizedContactTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.rootLaw_eq_normalizedContactTable

assert_no_sorry StochasticToDeterministicLatents.Binary.chartCandidate_rootLaw
/-- info: 'StochasticToDeterministicLatents.Binary.chartCandidate_rootLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.chartCandidate_rootLaw

assert_no_sorry StochasticToDeterministicLatents.Binary.rowCubeParameter_lt_of_transpose_strictOffDiagonal
/-- info: 'StochasticToDeterministicLatents.Binary.rowCubeParameter_lt_of_transpose_strictOffDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.rowCubeParameter_lt_of_transpose_strictOffDiagonal

assert_no_sorry StochasticToDeterministicLatents.Binary.rootLaw_transpose
/-- info: 'StochasticToDeterministicLatents.Binary.rootLaw_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.rootLaw_transpose

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_swapColumns_involutive
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_swapColumns_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_swapColumns_involutive

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_chartTableSymmetry_zero
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_chartTableSymmetry_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_chartTableSymmetry_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.pushforward_refl
/-- info: 'StochasticToDeterministicLatents.Binary.pushforward_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pushforward_refl

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_orientedChartChoice
/-- info: 'StochasticToDeterministicLatents.Binary.exists_orientedChartChoice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_orientedChartChoice

assert_no_sorry StochasticToDeterministicLatents.Binary.chartCandidate_hasContactRoots
/-- info: 'StochasticToDeterministicLatents.Binary.chartCandidate_hasContactRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.chartCandidate_hasContactRoots

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_orientedTransposeChartWithRoots
/-- info: 'StochasticToDeterministicLatents.Binary.exists_orientedTransposeChartWithRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_orientedTransposeChartWithRoots

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_orientedTransposeChartWithRootsAndJoint
/-- info: 'StochasticToDeterministicLatents.Binary.exists_orientedTransposeChartWithRootsAndJoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_orientedTransposeChartWithRootsAndJoint

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_contactPresentation_of_orientedPacket
/-- info: 'StochasticToDeterministicLatents.Binary.exists_contactPresentation_of_orientedPacket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_contactPresentation_of_orientedPacket

assert_no_sorry StochasticToDeterministicLatents.Binary.candidatePresentation
/-- info: 'StochasticToDeterministicLatents.Binary.candidatePresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.candidatePresentation

assert_no_sorry StochasticToDeterministicLatents.Binary.w3_eq_zero_of_subsingleton
/-- info: 'StochasticToDeterministicLatents.Binary.w3_eq_zero_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.w3_eq_zero_of_subsingleton

assert_no_sorry StochasticToDeterministicLatents.Binary.quotientSeedSetup_optimal_and_w3_eq_zero_of_card_eq_one
/-- info: 'StochasticToDeterministicLatents.Binary.quotientSeedSetup_optimal_and_w3_eq_zero_of_card_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.quotientSeedSetup_optimal_and_w3_eq_zero_of_card_eq_one

assert_no_sorry StochasticToDeterministicLatents.Binary.selectedOptimizer_zeroOrContactPresentation
/-- info: 'StochasticToDeterministicLatents.Binary.selectedOptimizer_zeroOrContactPresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.selectedOptimizer_zeroOrContactPresentation

/-! ## SparseLimit -/

assert_no_sorry StochasticToDeterministicLatents.T_le_mul_tau_of_forall_fullSupport
/-- info: 'StochasticToDeterministicLatents.T_le_mul_tau_of_forall_fullSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.T_le_mul_tau_of_forall_fullSupport

/-! ## Binary.ScalarEstimates -/

assert_no_sorry StochasticToDeterministicLatents.Binary.oddLogPartialSum_le_logRatio
/-- info: 'StochasticToDeterministicLatents.Binary.oddLogPartialSum_le_logRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.oddLogPartialSum_le_logRatio

assert_no_sorry StochasticToDeterministicLatents.Binary.logRatio_le_oddLogPartialSum_add_remainder
/-- info: 'StochasticToDeterministicLatents.Binary.logRatio_le_oddLogPartialSum_add_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.logRatio_le_oddLogPartialSum_add_remainder

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_contactDenominator
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_contactDenominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_contactDenominator

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_contactMidpoint
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_contactMidpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_contactMidpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_remainingLogFactor
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_remainingLogFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_remainingLogFactor

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingRangeDerivativeLedger
/-- info: 'StochasticToDeterministicLatents.Binary.remainingRangeDerivativeLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingRangeDerivativeLedger

assert_no_sorry StochasticToDeterministicLatents.Binary.contactMidpointDerivative_pos
/-- info: 'StochasticToDeterministicLatents.Binary.contactMidpointDerivative_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactMidpointDerivative_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingDerivativeNumerator_pos
/-- info: 'StochasticToDeterministicLatents.Binary.remainingDerivativeNumerator_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingDerivativeNumerator_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingDerivativeDenominator_pos
/-- info: 'StochasticToDeterministicLatents.Binary.remainingDerivativeDenominator_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingDerivativeDenominator_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingLogDifference_strictAntiOn
/-- info: 'StochasticToDeterministicLatents.Binary.remainingLogDifference_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingLogDifference_strictAntiOn

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingRangeProduct_ge_min_endpoints
/-- info: 'StochasticToDeterministicLatents.Binary.remainingRangeProduct_ge_min_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingRangeProduct_ge_min_endpoints

assert_no_sorry StochasticToDeterministicLatents.Binary.atanhLog_pos_on_unitInterval
/-- info: 'StochasticToDeterministicLatents.Binary.atanhLog_pos_on_unitInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.atanhLog_pos_on_unitInterval

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_atanhLog
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_atanhLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_atanhLog

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_atanhEndpointGap
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_atanhEndpointGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_atanhEndpointGap

assert_no_sorry StochasticToDeterministicLatents.Binary.atanhEndpointGap_concaveOn
/-- info: 'StochasticToDeterministicLatents.Binary.atanhEndpointGap_concaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.atanhEndpointGap_concaveOn

assert_no_sorry StochasticToDeterministicLatents.Binary.atanhEndpointGap_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.atanhEndpointGap_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.atanhEndpointGap_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.atanhLog_ratio_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.atanhLog_ratio_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.atanhLog_ratio_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingGap_eq_prior_factorization
/-- info: 'StochasticToDeterministicLatents.Binary.mixingGap_eq_prior_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingGap_eq_prior_factorization

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingGap_nonnegative
/-- info: 'StochasticToDeterministicLatents.Binary.mixingGap_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingGap_nonnegative

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingTerm_zero
/-- info: 'StochasticToDeterministicLatents.Binary.mixingTerm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingTerm_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_mixingTerm
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_mixingTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_mixingTerm

assert_no_sorry StochasticToDeterministicLatents.Binary.shifted_product_sub_eq_mixingGap
/-- info: 'StochasticToDeterministicLatents.Binary.shifted_product_sub_eq_mixingGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.shifted_product_sub_eq_mixingGap

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingSlope_nonnegative
/-- info: 'StochasticToDeterministicLatents.Binary.mixingSlope_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingSlope_nonnegative

assert_no_sorry StochasticToDeterministicLatents.Binary.continuous_mixingTerm
/-- info: 'StochasticToDeterministicLatents.Binary.continuous_mixingTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.continuous_mixingTerm

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingSlope_eq_log_product_ratio
/-- info: 'StochasticToDeterministicLatents.Binary.mixingSlope_eq_log_product_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingSlope_eq_log_product_ratio

assert_no_sorry StochasticToDeterministicLatents.Binary.mixing_product_ratio_eq_one_add
/-- info: 'StochasticToDeterministicLatents.Binary.mixing_product_ratio_eq_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixing_product_ratio_eq_one_add

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingSlope_antitone
/-- info: 'StochasticToDeterministicLatents.Binary.mixingSlope_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingSlope_antitone

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingTerm_concave
/-- info: 'StochasticToDeterministicLatents.Binary.mixingTerm_concave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingTerm_concave

assert_no_sorry StochasticToDeterministicLatents.Binary.offDiagonalLoss_le_mixingSum
/-- info: 'StochasticToDeterministicLatents.Binary.offDiagonalLoss_le_mixingSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.offDiagonalLoss_le_mixingSum

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingKernelBelow_zero
/-- info: 'StochasticToDeterministicLatents.Binary.mixingKernelBelow_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingKernelBelow_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingKernelTotal_nonnegative
/-- info: 'StochasticToDeterministicLatents.Binary.mixingKernelTotal_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingKernelTotal_nonnegative

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingTerm_eq_integral_kernel
/-- info: 'StochasticToDeterministicLatents.Binary.mixingTerm_eq_integral_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingTerm_eq_integral_kernel

assert_no_sorry StochasticToDeterministicLatents.Binary.mixtureMass_sum_eq_one_add_r
/-- info: 'StochasticToDeterministicLatents.Binary.mixtureMass_sum_eq_one_add_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixtureMass_sum_eq_one_add_r

assert_no_sorry StochasticToDeterministicLatents.Binary.tendsto_mixingTerm_atTop
/-- info: 'StochasticToDeterministicLatents.Binary.tendsto_mixingTerm_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.tendsto_mixingTerm_atTop

assert_no_sorry StochasticToDeterministicLatents.Binary.observableInfo_eq_r_log_r_sub
/-- info: 'StochasticToDeterministicLatents.Binary.observableInfo_eq_r_log_r_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.observableInfo_eq_r_log_r_sub

assert_no_sorry StochasticToDeterministicLatents.Binary.integrableOn_mixingSlope_Ioi
/-- info: 'StochasticToDeterministicLatents.Binary.integrableOn_mixingSlope_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.integrableOn_mixingSlope_Ioi

assert_no_sorry StochasticToDeterministicLatents.Binary.observableInfo_eq_integral_kernel
/-- info: 'StochasticToDeterministicLatents.Binary.observableInfo_eq_integral_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.observableInfo_eq_integral_kernel

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_eq_sum_logs
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_eq_sum_logs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_eq_sum_logs

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_le_left_log
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_le_left_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_le_left_log

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_unit_lower
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_unit_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_unit_lower

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_cubic_upper
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_cubic_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_cubic_upper

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingSlopeKernel_eq_log_sum
/-- info: 'StochasticToDeterministicLatents.Binary.mixingSlopeKernel_eq_log_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingSlopeKernel_eq_log_sum

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingSlopeKernel_convex
/-- info: 'StochasticToDeterministicLatents.Binary.mixingSlopeKernel_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingSlopeKernel_convex

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_eq_mass_mul_binEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_eq_mass_mul_binEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_eq_mass_mul_binEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_superadditive
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_superadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_superadditive

assert_no_sorry StochasticToDeterministicLatents.Binary.contactEntropyGap_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.contactEntropyGap_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactEntropyGap_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.smallPriorRawEnvelope_eq_scaled
/-- info: 'StochasticToDeterministicLatents.Binary.smallPriorRawEnvelope_eq_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.smallPriorRawEnvelope_eq_scaled

assert_no_sorry StochasticToDeterministicLatents.Binary.smallPriorCubicEnvelope
/-- info: 'StochasticToDeterministicLatents.Binary.smallPriorCubicEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.smallPriorCubicEnvelope

assert_no_sorry StochasticToDeterministicLatents.Binary.smallPriorRationalPart_lower
/-- info: 'StochasticToDeterministicLatents.Binary.smallPriorRationalPart_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.smallPriorRationalPart_lower

assert_no_sorry StochasticToDeterministicLatents.Binary.log_eleven_upper
/-- info: 'StochasticToDeterministicLatents.Binary.log_eleven_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_eleven_upper

assert_no_sorry StochasticToDeterministicLatents.Binary.smallPriorEnvelopeExpression_lower
/-- info: 'StochasticToDeterministicLatents.Binary.smallPriorEnvelopeExpression_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.smallPriorEnvelopeExpression_lower

assert_no_sorry StochasticToDeterministicLatents.Binary.smallPriorExactLedger
/-- info: 'StochasticToDeterministicLatents.Binary.smallPriorExactLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.smallPriorExactLedger

assert_no_sorry StochasticToDeterministicLatents.Binary.nine_mul_pow_eleven_le_sum_range_fifteen
/-- info: 'StochasticToDeterministicLatents.Binary.nine_mul_pow_eleven_le_sum_range_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.nine_mul_pow_eleven_le_sum_range_fifteen

assert_no_sorry StochasticToDeterministicLatents.Binary.fourthPowerCapture_integer_margin
/-- info: 'StochasticToDeterministicLatents.Binary.fourthPowerCapture_integer_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.fourthPowerCapture_integer_margin

assert_no_sorry StochasticToDeterministicLatents.Binary.log_two_gt_693147_div_million
/-- info: 'StochasticToDeterministicLatents.Binary.log_two_gt_693147_div_million' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_two_gt_693147_div_million

assert_no_sorry StochasticToDeterministicLatents.Binary.log_109_div_100_gt_86177_div_million
/-- info: 'StochasticToDeterministicLatents.Binary.log_109_div_100_gt_86177_div_million' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_109_div_100_gt_86177_div_million

assert_no_sorry StochasticToDeterministicLatents.Binary.log_9_div_100_gt_neg_2407950_div_million
/-- info: 'StochasticToDeterministicLatents.Binary.log_9_div_100_gt_neg_2407950_div_million' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_9_div_100_gt_neg_2407950_div_million

assert_no_sorry StochasticToDeterministicLatents.Binary.log_10981_div_10000_lt_93582_div_million
/-- info: 'StochasticToDeterministicLatents.Binary.log_10981_div_10000_lt_93582_div_million' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_10981_div_10000_lt_93582_div_million

assert_no_sorry StochasticToDeterministicLatents.Binary.log_10081_div_10000_lt_8068_div_million
/-- info: 'StochasticToDeterministicLatents.Binary.log_10081_div_10000_lt_8068_div_million' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_10081_div_10000_lt_8068_div_million

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_balancedEdgeScalarReward
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_balancedEdgeScalarReward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_balancedEdgeScalarReward

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedEdgeDerivative_neg
/-- info: 'StochasticToDeterministicLatents.Binary.balancedEdgeDerivative_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedEdgeDerivative_neg

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedEdgeScalarReward_at_endpoint
/-- info: 'StochasticToDeterministicLatents.Binary.balancedEdgeScalarReward_at_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedEdgeScalarReward_at_endpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedEdgeExactLedger
/-- info: 'StochasticToDeterministicLatents.Binary.balancedEdgeExactLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedEdgeExactLedger

assert_no_sorry StochasticToDeterministicLatents.Binary.freeLowerMixtureMass_eq_e
/-- info: 'StochasticToDeterministicLatents.Binary.freeLowerMixtureMass_eq_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeLowerMixtureMass_eq_e

assert_no_sorry StochasticToDeterministicLatents.Binary.freeUpperMixtureMass_eq_ell
/-- info: 'StochasticToDeterministicLatents.Binary.freeUpperMixtureMass_eq_ell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeUpperMixtureMass_eq_ell

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixingTerm_eq_mixingTerm
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixingTerm_eq_mixingTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixingTerm_eq_mixingTerm

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixingTerm_eq_offDiagonalLoss
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixingTerm_eq_offDiagonalLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixingTerm_eq_offDiagonalLoss

assert_no_sorry StochasticToDeterministicLatents.Binary.highArmEntropy_eq_highConditionalEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.highArmEntropy_eq_highConditionalEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.highArmEntropy_eq_highConditionalEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.positivePhaseTwoFifthsGateLedger
/-- info: 'StochasticToDeterministicLatents.Binary.positivePhaseTwoFifthsGateLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.positivePhaseTwoFifthsGateLedger

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedSeamEndpointLogLedger
/-- info: 'StochasticToDeterministicLatents.Binary.balancedSeamEndpointLogLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedSeamEndpointLogLedger

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamEndpointLedger
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamEndpointLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamEndpointLedger

/-! ## Binary.Reduction -/

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.codeReward_le_max_chartCodeRewards
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.codeReward_le_max_chartCodeRewards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.codeReward_le_max_chartCodeRewards

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.w3Cost_phaseSelector_le_w3Cost
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.w3Cost_phaseSelector_le_w3Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.w3Cost_phaseSelector_le_w3Cost

assert_no_sorry StochasticToDeterministicLatents.Binary.TransposeChart.min_chartCodes_le_w3Cost
/-- info: 'StochasticToDeterministicLatents.Binary.TransposeChart.min_chartCodes_le_w3Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.TransposeChart.min_chartCodes_le_w3Cost

/-! ## Binary.FactorNine.NonpositivePhase -/

assert_no_sorry StochasticToDeterministicLatents.Binary.integral_Ioi_equal_pole_formula
/-- info: 'StochasticToDeterministicLatents.Binary.integral_Ioi_equal_pole_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.integral_Ioi_equal_pole_formula

assert_no_sorry StochasticToDeterministicLatents.Binary.integral_Ioi_strict_poles_formula
/-- info: 'StochasticToDeterministicLatents.Binary.integral_Ioi_strict_poles_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.integral_Ioi_strict_poles_formula

assert_no_sorry StochasticToDeterministicLatents.Binary.integral_Ioc_equal_pole_formula
/-- info: 'StochasticToDeterministicLatents.Binary.integral_Ioc_equal_pole_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.integral_Ioc_equal_pole_formula

assert_no_sorry StochasticToDeterministicLatents.Binary.integral_Ioc_strict_poles_formula
/-- info: 'StochasticToDeterministicLatents.Binary.integral_Ioc_strict_poles_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.integral_Ioc_strict_poles_formula

assert_no_sorry StochasticToDeterministicLatents.Binary.integral_rationalKernel_le_sixteen_mul_integral
/-- info: 'StochasticToDeterministicLatents.Binary.integral_rationalKernel_le_sixteen_mul_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.integral_rationalKernel_le_sixteen_mul_integral

assert_no_sorry StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_contact
/-- info: 'StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_contact

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.contactMidpoint_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.contactMidpoint_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.contactMidpoint_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.contactMidpoint_contact
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.contactMidpoint_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.contactMidpoint_contact

assert_no_sorry StochasticToDeterministicLatents.Binary.exposedPhaseReward_strictAntiOn
/-- info: 'StochasticToDeterministicLatents.Binary.exposedPhaseReward_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exposedPhaseReward_strictAntiOn

assert_no_sorry StochasticToDeterministicLatents.Binary.movingContactEndpoint_lowMass
/-- info: 'StochasticToDeterministicLatents.Binary.movingContactEndpoint_lowMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.movingContactEndpoint_lowMass

assert_no_sorry StochasticToDeterministicLatents.Binary.movingContactEndpoint_midpoint
/-- info: 'StochasticToDeterministicLatents.Binary.movingContactEndpoint_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.movingContactEndpoint_midpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.contactMidpoint_linear_square
/-- info: 'StochasticToDeterministicLatents.Binary.contactMidpoint_linear_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactMidpoint_linear_square

assert_no_sorry StochasticToDeterministicLatents.Binary.contact_linear_square_le_at_midpoint
/-- info: 'StochasticToDeterministicLatents.Binary.contact_linear_square_le_at_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contact_linear_square_le_at_midpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_movingContactEndpoint
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_movingContactEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_movingContactEndpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.movingContactEndpoint_deriv_le_neg_one
/-- info: 'StochasticToDeterministicLatents.Binary.movingContactEndpoint_deriv_le_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.movingContactEndpoint_deriv_le_neg_one

assert_no_sorry StochasticToDeterministicLatents.Binary.movingEndpoint_kernel_identity
/-- info: 'StochasticToDeterministicLatents.Binary.movingEndpoint_kernel_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.movingEndpoint_kernel_identity

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingKernel_rectangle_integrable
/-- info: 'StochasticToDeterministicLatents.Binary.mixingKernel_rectangle_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingKernel_rectangle_integrable

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_mixingKernelBelow
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_mixingKernelBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_mixingKernelBelow

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingKernelBelow_mono_of_pos
/-- info: 'StochasticToDeterministicLatents.Binary.mixingKernelBelow_mono_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingKernelBelow_mono_of_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.two_mul_mixingKernelBelow_midpoint_le_endpoints
/-- info: 'StochasticToDeterministicLatents.Binary.two_mul_mixingKernelBelow_midpoint_le_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.two_mul_mixingKernelBelow_midpoint_le_endpoints

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_midpointMixing_le_mixingSum
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_midpointMixing_le_mixingSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_midpointMixing_le_mixingSum

assert_no_sorry StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_y_eq_edgeReward
/-- info: 'StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_y_eq_edgeReward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_y_eq_edgeReward

assert_no_sorry StochasticToDeterministicLatents.Binary.strictConcaveOn_edgeReward_prior
/-- info: 'StochasticToDeterministicLatents.Binary.strictConcaveOn_edgeReward_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.strictConcaveOn_edgeReward_prior

assert_no_sorry StochasticToDeterministicLatents.Binary.edgeReward_half_eq_balancedEdgeScalarReward
/-- info: 'StochasticToDeterministicLatents.Binary.edgeReward_half_eq_balancedEdgeScalarReward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.edgeReward_half_eq_balancedEdgeScalarReward

assert_no_sorry StochasticToDeterministicLatents.Binary.edgeReward_half_pos_of_le_nine_hundredths
/-- info: 'StochasticToDeterministicLatents.Binary.edgeReward_half_pos_of_le_nine_hundredths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.edgeReward_half_pos_of_le_nine_hundredths

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.prior_lt_ten_mul_r_of_phaseReward_nonpos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.prior_lt_ten_mul_r_of_phaseReward_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.prior_lt_ten_mul_r_of_phaseReward_nonpos

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingRangeProduct_one_half_capture
/-- info: 'StochasticToDeterministicLatents.Binary.remainingRangeProduct_one_half_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingRangeProduct_one_half_capture

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingRangeProduct_three_tenths_capture
/-- info: 'StochasticToDeterministicLatents.Binary.remainingRangeProduct_three_tenths_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingRangeProduct_three_tenths_capture

assert_no_sorry StochasticToDeterministicLatents.Binary.balanced_captureObservableInfo_le_log_two
/-- info: 'StochasticToDeterministicLatents.Binary.balanced_captureObservableInfo_le_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balanced_captureObservableInfo_le_log_two

assert_no_sorry StochasticToDeterministicLatents.Binary.sixteenFoldCaptureGap_zero
/-- info: 'StochasticToDeterministicLatents.Binary.sixteenFoldCaptureGap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.sixteenFoldCaptureGap_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.balanced_cube_le_nine_mul_contactMidpoint_pow_four
/-- info: 'StochasticToDeterministicLatents.Binary.balanced_cube_le_nine_mul_contactMidpoint_pow_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balanced_cube_le_nine_mul_contactMidpoint_pow_four

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingRangeProduct_le_balanced_midpointMixing
/-- info: 'StochasticToDeterministicLatents.Binary.remainingRangeProduct_le_balanced_midpointMixing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingRangeProduct_le_balanced_midpointMixing

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_sixteenFoldCaptureGap
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_sixteenFoldCaptureGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_sixteenFoldCaptureGap

assert_no_sorry StochasticToDeterministicLatents.Binary.sixteenFoldCaptureGap_ge_min_endpoints
/-- info: 'StochasticToDeterministicLatents.Binary.sixteenFoldCaptureGap_ge_min_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.sixteenFoldCaptureGap_ge_min_endpoints

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_contact_le
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_contact_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_contact_le

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_le_contact
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_le_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_le_contact

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_eight_mul_mixingSum_of_phaseReward_nonpos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_eight_mul_mixingSum_of_phaseReward_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_le_eight_mul_mixingSum_of_phaseReward_nonpos

/-! ## Positive phase and conditional chart cost -/

assert_no_sorry StochasticToDeterministicLatents.Binary.contactRatio_substitution_add_fourthPower
/-- info: 'StochasticToDeterministicLatents.Binary.contactRatio_substitution_add_fourthPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactRatio_substitution_add_fourthPower

assert_no_sorry StochasticToDeterministicLatents.Binary.contactRatio_substitution_add_one
/-- info: 'StochasticToDeterministicLatents.Binary.contactRatio_substitution_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactRatio_substitution_add_one

assert_no_sorry StochasticToDeterministicLatents.Binary.contactRatio_substitution_kernel
/-- info: 'StochasticToDeterministicLatents.Binary.contactRatio_substitution_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactRatio_substitution_kernel

assert_no_sorry StochasticToDeterministicLatents.Binary.contactRatio_substitution
/-- info: 'StochasticToDeterministicLatents.Binary.contactRatio_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.contactRatio_substitution

assert_no_sorry StochasticToDeterministicLatents.Binary.inv_square_le_contactRatio
/-- info: 'StochasticToDeterministicLatents.Binary.inv_square_le_contactRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.inv_square_le_contactRatio

assert_no_sorry StochasticToDeterministicLatents.Binary.smallLog_le_bridgeDerivative
/-- info: 'StochasticToDeterministicLatents.Binary.smallLog_le_bridgeDerivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.smallLog_le_bridgeDerivative

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixture_shifted_product
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixture_shifted_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixture_shifted_product

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixture_product_ratio_eq_one_add
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixture_product_ratio_eq_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixture_product_ratio_eq_one_add

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_fourthPower_shift
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_fourthPower_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_fourthPower_shift

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_one_shift
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_one_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_pairEntropy_one_shift

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_proxy_contactSum
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_proxy_contactSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_proxy_contactSum

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_priorLogPayment
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_priorLogPayment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_priorLogPayment

assert_no_sorry StochasticToDeterministicLatents.Binary.priorLogPayment_concave
/-- info: 'StochasticToDeterministicLatents.Binary.priorLogPayment_concave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.priorLogPayment_concave

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_priorLogPayment_balanced
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_priorLogPayment_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_priorLogPayment_balanced

assert_no_sorry StochasticToDeterministicLatents.Binary.priorLogPayment_balanced_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.priorLogPayment_balanced_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.priorLogPayment_balanced_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.priorLogPayment_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.priorLogPayment_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.priorLogPayment_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.priorLog_le_three_halves_mul_bridgeDerivative
/-- info: 'StochasticToDeterministicLatents.Binary.priorLog_le_three_halves_mul_bridgeDerivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.priorLog_le_three_halves_mul_bridgeDerivative

assert_no_sorry StochasticToDeterministicLatents.Binary.strictProxy_monotoneInContactMass
/-- info: 'StochasticToDeterministicLatents.Binary.strictProxy_monotoneInContactMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.strictProxy_monotoneInContactMass

assert_no_sorry StochasticToDeterministicLatents.Binary.highArmEntropy_affineInPrior
/-- info: 'StochasticToDeterministicLatents.Binary.highArmEntropy_affineInPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.highArmEntropy_affineInPrior

assert_no_sorry StochasticToDeterministicLatents.Binary.highArmEntropy_convexInPrior
/-- info: 'StochasticToDeterministicLatents.Binary.highArmEntropy_convexInPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.highArmEntropy_convexInPrior

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_freeMixingTerm_prior
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_freeMixingTerm_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_freeMixingTerm_prior

assert_no_sorry StochasticToDeterministicLatents.Binary.log_add_div_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.log_add_div_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.log_add_div_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixingTerm_priorDerivative_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixingTerm_priorDerivative_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixingTerm_priorDerivative_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixingTerm_concaveInPrior
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixingTerm_concaveInPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixingTerm_concaveInPrior

assert_no_sorry StochasticToDeterministicLatents.Binary.strictProxy_concaveInPrior
/-- info: 'StochasticToDeterministicLatents.Binary.strictProxy_concaveInPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.strictProxy_concaveInPrior

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_contactMidpoint_le_s
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_contactMidpoint_le_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.two_mul_contactMidpoint_le_s

assert_no_sorry StochasticToDeterministicLatents.Binary.strictProxy_geMinAtSeamEndpoints
/-- info: 'StochasticToDeterministicLatents.Binary.strictProxy_geMinAtSeamEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.strictProxy_geMinAtSeamEndpoints

assert_no_sorry StochasticToDeterministicLatents.Binary.pairEntropy_scale
/-- info: 'StochasticToDeterministicLatents.Binary.pairEntropy_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.pairEntropy_scale

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryEntropyJensenGap_eq_pairEntropy
/-- info: 'StochasticToDeterministicLatents.Binary.binaryEntropyJensenGap_eq_pairEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryEntropyJensenGap_eq_pairEntropy

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryEntropyJensenGap_binaryChannel_le
/-- info: 'StochasticToDeterministicLatents.Binary.binaryEntropyJensenGap_binaryChannel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryEntropyJensenGap_binaryChannel_le

assert_no_sorry StochasticToDeterministicLatents.Binary.scalarSingletonReward_binaryChannel_le
/-- info: 'StochasticToDeterministicLatents.Binary.scalarSingletonReward_binaryChannel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.scalarSingletonReward_binaryChannel_le

assert_no_sorry StochasticToDeterministicLatents.Binary.binEntropy_sub_mul_le_log_one_add_exp_neg
/-- info: 'StochasticToDeterministicLatents.Binary.binEntropy_sub_mul_le_log_one_add_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binEntropy_sub_mul_le_log_one_add_exp_neg

assert_no_sorry StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_equalMass_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_equalMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_equalMass_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_equalMass_eq_scaled_reward
/-- info: 'StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_equalMass_eq_scaled_reward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exposedPhaseReward_at_equalMass_eq_scaled_reward

assert_no_sorry StochasticToDeterministicLatents.Binary.seamLowerPosterior_monotoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.seamLowerPosterior_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamLowerPosterior_monotoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.seamUpperPosterior_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.seamUpperPosterior_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamUpperPosterior_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.seamLowerPosterior_bounds
/-- info: 'StochasticToDeterministicLatents.Binary.seamLowerPosterior_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamLowerPosterior_bounds

assert_no_sorry StochasticToDeterministicLatents.Binary.seamUpperPosterior_bounds
/-- info: 'StochasticToDeterministicLatents.Binary.seamUpperPosterior_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamUpperPosterior_bounds

assert_no_sorry StochasticToDeterministicLatents.Binary.seamConditionalEntropy_comparison
/-- info: 'StochasticToDeterministicLatents.Binary.seamConditionalEntropy_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamConditionalEntropy_comparison

assert_no_sorry StochasticToDeterministicLatents.Binary.seamPosterior_gap_pos
/-- info: 'StochasticToDeterministicLatents.Binary.seamPosterior_gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamPosterior_gap_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.twoFifthsPosterior_gap_pos
/-- info: 'StochasticToDeterministicLatents.Binary.twoFifthsPosterior_gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.twoFifthsPosterior_gap_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.seamLowerPosterior_div_gap
/-- info: 'StochasticToDeterministicLatents.Binary.seamLowerPosterior_div_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamLowerPosterior_div_gap

assert_no_sorry StochasticToDeterministicLatents.Binary.seamUpperComplement_div_gap
/-- info: 'StochasticToDeterministicLatents.Binary.seamUpperComplement_div_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamUpperComplement_div_gap

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryChannel_mem_Icc_of_twoFifths_le
/-- info: 'StochasticToDeterministicLatents.Binary.binaryChannel_mem_Icc_of_twoFifths_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryChannel_mem_Icc_of_twoFifths_le

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryChannel_twoFifthsLowerPosterior
/-- info: 'StochasticToDeterministicLatents.Binary.binaryChannel_twoFifthsLowerPosterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryChannel_twoFifthsLowerPosterior

assert_no_sorry StochasticToDeterministicLatents.Binary.binaryChannel_twoFifthsUpperPosterior
/-- info: 'StochasticToDeterministicLatents.Binary.binaryChannel_twoFifthsUpperPosterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binaryChannel_twoFifthsUpperPosterior

assert_no_sorry StochasticToDeterministicLatents.Binary.binEntropy_twoFifthsLowerPosterior_gt
/-- info: 'StochasticToDeterministicLatents.Binary.binEntropy_twoFifthsLowerPosterior_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binEntropy_twoFifthsLowerPosterior_gt

assert_no_sorry StochasticToDeterministicLatents.Binary.binEntropy_twoFifthsUpperPosterior_gt
/-- info: 'StochasticToDeterministicLatents.Binary.binEntropy_twoFifthsUpperPosterior_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.binEntropy_twoFifthsUpperPosterior_gt

assert_no_sorry StochasticToDeterministicLatents.Binary.singletonReward_twoFifthsSeam_neg
/-- info: 'StochasticToDeterministicLatents.Binary.singletonReward_twoFifthsSeam_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.singletonReward_twoFifthsSeam_neg

assert_no_sorry StochasticToDeterministicLatents.Binary.seamReward_neg
/-- info: 'StochasticToDeterministicLatents.Binary.seamReward_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamReward_neg

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.x_lt_two_fifths_of_phaseReward_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.x_lt_two_fifths_of_phaseReward_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.x_lt_two_fifths_of_phaseReward_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.freePriorPhaseReward_at_chart
/-- info: 'StochasticToDeterministicLatents.Binary.freePriorPhaseReward_at_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freePriorPhaseReward_at_chart

assert_no_sorry StochasticToDeterministicLatents.Binary.freePriorPhaseReward_strictConcaveOn
/-- info: 'StochasticToDeterministicLatents.Binary.freePriorPhaseReward_strictConcaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freePriorPhaseReward_strictConcaveOn

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_freePriorPhaseReward_zero
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_freePriorPhaseReward_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_freePriorPhaseReward_zero

assert_no_sorry StochasticToDeterministicLatents.Binary.freePriorPhaseReward_le_tangent
/-- info: 'StochasticToDeterministicLatents.Binary.freePriorPhaseReward_le_tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freePriorPhaseReward_le_tangent

assert_no_sorry StochasticToDeterministicLatents.Binary.r_mul_log_le_pairEntropy_low
/-- info: 'StochasticToDeterministicLatents.Binary.r_mul_log_le_pairEntropy_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.r_mul_log_le_pairEntropy_low

assert_no_sorry StochasticToDeterministicLatents.Binary.r_mul_log_le_pairEntropy_high
/-- info: 'StochasticToDeterministicLatents.Binary.r_mul_log_le_pairEntropy_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.r_mul_log_le_pairEntropy_high

assert_no_sorry StochasticToDeterministicLatents.Binary.phaseRewardPriorTangent_neg_of_prior_le_three_mul_r
/-- info: 'StochasticToDeterministicLatents.Binary.phaseRewardPriorTangent_neg_of_prior_le_three_mul_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.phaseRewardPriorTangent_neg_of_prior_le_three_mul_r

assert_no_sorry StochasticToDeterministicLatents.Binary.phaseReward_neg_of_prior_le_three_mul_r
/-- info: 'StochasticToDeterministicLatents.Binary.phaseReward_neg_of_prior_le_three_mul_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.phaseReward_neg_of_prior_le_three_mul_r

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.three_mul_r_lt_pi_of_phaseReward_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.three_mul_r_lt_pi_of_phaseReward_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.three_mul_r_lt_pi_of_phaseReward_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.positivePhaseSlack_eq_three_mul_proxy_add_remainders
/-- info: 'StochasticToDeterministicLatents.Binary.positivePhaseSlack_eq_three_mul_proxy_add_remainders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.positivePhaseSlack_eq_three_mul_proxy_add_remainders

assert_no_sorry StochasticToDeterministicLatents.Binary.three_mul_proxy_le_positivePhaseSlack
/-- info: 'StochasticToDeterministicLatents.Binary.three_mul_proxy_le_positivePhaseSlack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.three_mul_proxy_le_positivePhaseSlack

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.strictFactorEight_of_seam_pos
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.strictFactorEight_of_seam_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.strictFactorEight_of_seam_pos

/-! ## Seam endpoints and unconditional chart cost -/

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingTerm_eq_integral_mixingSlope
/-- info: 'StochasticToDeterministicLatents.Binary.mixingTerm_eq_integral_mixingSlope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingTerm_eq_integral_mixingSlope

assert_no_sorry StochasticToDeterministicLatents.Binary.bridgeDerivative_at_balancedMidpoint
/-- info: 'StochasticToDeterministicLatents.Binary.bridgeDerivative_at_balancedMidpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.bridgeDerivative_at_balancedMidpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.fourthPower_div_contactMidpoint
/-- info: 'StochasticToDeterministicLatents.Binary.fourthPower_div_contactMidpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.fourthPower_div_contactMidpoint

assert_no_sorry StochasticToDeterministicLatents.Binary.two_mul_contactMidpoint_div_fourthPower
/-- info: 'StochasticToDeterministicLatents.Binary.two_mul_contactMidpoint_div_fourthPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.two_mul_contactMidpoint_div_fourthPower

assert_no_sorry StochasticToDeterministicLatents.Binary.seamNorm_div_contactMidpoint_eq_exp_remainingLogFactor
/-- info: 'StochasticToDeterministicLatents.Binary.seamNorm_div_contactMidpoint_eq_exp_remainingLogFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.seamNorm_div_contactMidpoint_eq_exp_remainingLogFactor

assert_no_sorry StochasticToDeterministicLatents.Binary.bridge_ge_midpoint_payment_at_balancedSeam
/-- info: 'StochasticToDeterministicLatents.Binary.bridge_ge_midpoint_payment_at_balancedSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.bridge_ge_midpoint_payment_at_balancedSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.highArmEntropy_le_at_balancedSeam
/-- info: 'StochasticToDeterministicLatents.Binary.highArmEntropy_le_at_balancedSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.highArmEntropy_le_at_balancedSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedSeamEntropyEnvelope_identity
/-- info: 'StochasticToDeterministicLatents.Binary.balancedSeamEntropyEnvelope_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedSeamEntropyEnvelope_identity

assert_no_sorry StochasticToDeterministicLatents.Binary.proxy_ge_at_balancedSeam
/-- info: 'StochasticToDeterministicLatents.Binary.proxy_ge_at_balancedSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.proxy_ge_at_balancedSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedSeamScalar_eq
/-- info: 'StochasticToDeterministicLatents.Binary.balancedSeamScalar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedSeamScalar_eq

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_balancedSeamScalar
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_balancedSeamScalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_balancedSeamScalar

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedSeamScalarDerivative_neg
/-- info: 'StochasticToDeterministicLatents.Binary.balancedSeamScalarDerivative_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedSeamScalarDerivative_neg

assert_no_sorry StochasticToDeterministicLatents.Binary.balancedSeamScalar_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.balancedSeamScalar_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.balancedSeamScalar_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.remainingLogFactor_pos_on_seam
/-- info: 'StochasticToDeterministicLatents.Binary.remainingLogFactor_pos_on_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.remainingLogFactor_pos_on_seam

assert_no_sorry StochasticToDeterministicLatents.Binary.proxy_pos_at_balancedSeam
/-- info: 'StochasticToDeterministicLatents.Binary.proxy_pos_at_balancedSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.proxy_pos_at_balancedSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamPolynomial_pos
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamPolynomial_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamPolynomial_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamMixingMargin_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamMixingMargin_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamMixingMargin_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamMixingMargin_pos
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamMixingMargin_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamMixingMargin_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.mixingGap_ge_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.mixingGap_ge_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.mixingGap_ge_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.highArmEntropy_le_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.highArmEntropy_le_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.highArmEntropy_le_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.bridgeDerivative_ge_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.bridgeDerivative_ge_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.bridgeDerivative_ge_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_scaled_lowPriorSeamIntegral
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_scaled_lowPriorSeamIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_scaled_lowPriorSeamIntegral

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_freeMixingTerm_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_freeMixingTerm_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_freeMixingTerm_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.freeMixingTerm_ge_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.freeMixingTerm_ge_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.freeMixingTerm_ge_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.proxy_ge_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.proxy_ge_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.proxy_ge_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_eq
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_eq

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamIntegral
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamIntegral

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_eq_assoc
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_eq_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_eq_assoc

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamEntropyEnvelope
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamEntropyEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamEntropyEnvelope

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_derivative_ge
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_derivative_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_derivative_ge

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_derivative_term_ge
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_derivative_term_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_derivative_term_ge

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_seamWidthRatio
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_seamWidthRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_seamWidthRatio

assert_no_sorry StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamGap
/-- info: 'StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.hasDerivAt_lowPriorSeamGap

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamGap_antitoneOn
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamGap_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamGap_antitoneOn

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_panel_lower
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_panel_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_panel_lower

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_twoFifths_lower
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_twoFifths_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamIntegral_twoFifths_lower

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_twoFifths_upper
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_twoFifths_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamEntropyEnvelope_twoFifths_upper

assert_no_sorry StochasticToDeterministicLatents.Binary.lowPriorSeamGap_twoFifths_pos
/-- info: 'StochasticToDeterministicLatents.Binary.lowPriorSeamGap_twoFifths_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.lowPriorSeamGap_twoFifths_pos

assert_no_sorry StochasticToDeterministicLatents.Binary.proxy_pos_at_lowPriorSeam
/-- info: 'StochasticToDeterministicLatents.Binary.proxy_pos_at_lowPriorSeam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.proxy_pos_at_lowPriorSeam

assert_no_sorry StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_phaseReward_nonneg
/-- info: 'StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_phaseReward_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_phaseReward_nonneg

assert_no_sorry StochasticToDeterministicLatents.Binary.ContactChart.strictFactorEight
/-- info: 'StochasticToDeterministicLatents.Binary.ContactChart.strictFactorEight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.ContactChart.strictFactorEight

/-! ## Binary factor nine -/

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_optimalLatent_w3_le_eight_of_fullSupport
/-- info: 'StochasticToDeterministicLatents.Binary.exists_optimalLatent_w3_le_eight_of_fullSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_optimalLatent_w3_le_eight_of_fullSupport

assert_no_sorry StochasticToDeterministicLatents.Binary.detScore_selector_le_nine_mul_tau_of_fullSupport
/-- info: 'StochasticToDeterministicLatents.Binary.detScore_selector_le_nine_mul_tau_of_fullSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.detScore_selector_le_nine_mul_tau_of_fullSupport

assert_no_sorry StochasticToDeterministicLatents.Binary.T_le_nine_mul_tau
/-- info: 'StochasticToDeterministicLatents.Binary.T_le_nine_mul_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.T_le_nine_mul_tau

assert_no_sorry StochasticToDeterministicLatents.Binary.exists_code_detScore_le_nine_mul_tau
/-- info: 'StochasticToDeterministicLatents.Binary.exists_code_detScore_le_nine_mul_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StochasticToDeterministicLatents.Binary.exists_code_detScore_le_nine_mul_tau
