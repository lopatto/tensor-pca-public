-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.PhysicalPressureLimitReductionKernel
public import TensorPCA.NonRSSphericalGroundExpectedUpperProofs
public import TensorPCA.PureSliceGroundLimitProofs
public import TensorPCA.RSGroundStateProofs
/-! Reduction from finite-temperature pressure lower bounds on the interior nonRS
domain. Physical uppers, pure/RS/pole cases, finite-law decomposition and centered
concentration are imported. The result is conditional on the pressure input; the
principal declaration is assembled separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.PhysicalPressureLimitReduction
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
open PhysicalPressureGroundReduction
noncomputable section
universe u

theorem sliceGroundLimit_interior_of_finitePressure (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1) (hpressure : FinitePressureLower k m) :
    GroundState.SliceGroundLimit k m := by
  have hm : m ∈ Icc (-1 : ℝ) 1 := ⟨(abs_lt.mp hm1).1.le, (abs_lt.mp hm1).2.le⟩
  exact sliceGroundLimit_of_finitePressure_and_upper k hk hm hpressure
    (fun eps heps ↦ NonRSSphericalGroundExpectedUpperProofs.eventual_expectedSliceGround_succ_le_variationalValue_add
      k hk hm0 hm1 heps)

theorem sliceGroundLimit_of_nonRSFinitePressure (hpressure : NonRSFinitePressureLower)
    (k : ℕ) (hk : 3 ≤ k) (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.SliceGroundLimit k m := by
  by_cases hm0 : m = 0
  · subst m
    exact PureSliceGroundLimitProofs.sliceGroundLimit_zero k hk
  by_cases hlarge : Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m|
  · exact RSGroundStateProofs.sliceGroundLimit_rs k hk m hm hlarge
  have hsmall : |m| < Real.sqrt (1-1/((k : ℝ)-1)) := lt_of_not_ge hlarge
  have hpos : 0 < |m| := abs_pos.mpr hm0
  have hm1 : |m| < 1 := hsmall.trans_le (rsCutoff_le_one k hk)
  exact sliceGroundLimit_interior_of_finitePressure k hk hpos hm1
    (hpressure k hk m hm hpos hsmall)

/-- Expected and almost-sure constrained limits under arbitrary coupling across
dimensions, conditional on finite-temperature pressure lower data.
-/
theorem constrainedLimit_of_nonRSFinitePressure (hpressure : NonRSFinitePressureLower) :
    Statements.ConstrainedLimit.{u} := by
  intro k hk lam hlam m hm
  have hg := sliceGroundLimit_of_nonRSFinitePressure hpressure k hk m hm
  have hs := SliceDecompositionProofs.sliceDecomposition k lam hm
  refine ⟨Reduction.constrained_mean_at hg hs, ?_⟩
  intro Omega _ mu _ E
  exact (Reduction.constrained_at E hg hs
    (MaximumProofs.sampleConstrainedMaximum_centered_ae E lam m (abs_le.mpr hm))).2


end
end TensorPCA.NonRSLowerProofs.PhysicalPressureLimitReduction
