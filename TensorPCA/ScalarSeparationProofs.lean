-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarValueProofs

/-! Continuity and strict separation of the maximum-likelihood scalar value. -/
@[expose] public section
namespace TensorPCA.ScalarSeparationProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs ScalarBranchProofs ScalarValueProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem mleValue_eq_branch_piecewise (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    Scalar.mleValue k lam = if lam ≤ Scalar.lambdaC k then Scalar.gs k else branchEnergy k lam := by
  unfold Scalar.mleValue
  by_cases hle : lam ≤ Scalar.lambdaC k
  · rw [ite_eq_left hle, ite_eq_left hle]
  · rw [ite_eq_right hle, ite_eq_right hle]
    exact supercriticalValue_eq_branchEnergy k hk (lt_of_not_ge hle)

theorem continuousAt_mleValue_critical (k : ℕ) (hk : 3 ≤ k) :
    ContinuousAt (Scalar.mleValue k) (Scalar.lambdaC k) := by
  have hE : Tendsto (branchEnergy k) (𝓝 (Scalar.lambdaC k)) (𝓝 (Scalar.gs k)) := by
    rw [← branchEnergy_critical k hk]
    exact (hasDerivAt_branchEnergy k hk (lambdaS_lt_lambdaC k hk)).continuousAt
  have hpoint : Scalar.mleValue k (Scalar.lambdaC k) = Scalar.gs k := by simp [Scalar.mleValue]
  change Tendsto (Scalar.mleValue k) _ (𝓝 _)
  rw [hpoint]
  convert (tendsto_const_nhds (x := Scalar.gs k)).if' hE using 1
  funext lam
  exact mleValue_eq_branch_piecewise k hk lam

theorem continuous_mleValue (k : ℕ) (hk : 3 ≤ k) : Continuous (Scalar.mleValue k) := by
  apply continuous_iff_continuousAt.mpr
  intro lam
  by_cases heq : lam = Scalar.lambdaC k
  · rw [heq]
    exact continuousAt_mleValue_critical k hk
  · by_cases hlt : lam < Scalar.lambdaC k
    · apply (continuousAt_const : ContinuousAt (fun _t : ℝ => Scalar.gs k) lam).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [Scalar.mleValue, ite_eq_left ht.le]
    · have hgt : Scalar.lambdaC k < lam := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      exact (valueDerivative k hk ((lambdaC_pos k hk).trans hgt) heq).continuousAt

/-- Strict value separation on and above the statistical threshold. -/
theorem strictMonoOn_mleValue (k : ℕ) (hk : 3 ≤ k) :
    StrictMonoOn (Scalar.mleValue k) (Ici (Scalar.lambdaC k)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (continuous_mleValue k hk).continuousOn
  intro lam hlam
  have hgt : Scalar.lambdaC k < lam := by simpa only [interior_Ici, mem_Ioi] using hlam
  have hpos := ((selectionLaws k hk).2.2.2.2.1 lam hgt).2.1
  rw [(valueDerivative k hk ((lambdaC_pos k hk).trans hgt) (ne_of_gt hgt)).deriv]
  exact pow_pos (Real.sqrt_pos.mpr hpos) _

theorem gs_lt_mleValue (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) : Scalar.gs k < Scalar.mleValue k lam := by
  have hh := strictMonoOn_mleValue k hk (show Scalar.lambdaC k ∈ Ici (Scalar.lambdaC k) from le_rfl)
    (show lam ∈ Ici (Scalar.lambdaC k) from hlam.le) hlam
  simpa only [Scalar.mleValue, ite_eq_left le_rfl] using hh

end
end TensorPCA.ScalarSeparationProofs
