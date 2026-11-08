-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GroundUpperProofs
public import TensorPCA.RSVariationalProof

/-! The literal slice process vanishes at overlaps -1 and 1. Its finite mean and variational value therefore agree there without a physical
spin-glass formula. -/
@[expose] public section
namespace TensorPCA.SliceGroundEndpointsProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

lemma sliceFeature_eq_zero_of_sq_eq_one {N : ℕ} (k : ℕ) {m : ℝ}
    (hm : m^2=1) (x : Model.Vector N) : GroundState.sliceFeature k m x=0 := by
  ext i
  simp [GroundState.sliceFeature,hm]

lemma expectedSliceGround_eq_zero_of_sq_eq_one {N : ℕ} (hN : 0<N) (k : ℕ)
    {m : ℝ} (hm : m^2=1) : GroundState.expectedSliceGround N k m=0 := by
  have hnonempty := Geometry.unitSphere_nonempty hN
  unfold GroundState.expectedSliceGround
  simp only [sliceFeature_eq_zero_of_sq_eq_one k hm,inner_zero_left]
  rw [hnonempty.image_const]
  simp

lemma xiSlice_eq_zero_of_sq_eq_one (k : ℕ) {m : ℝ} (hm : m^2=1) :
    Scalar.xiSlice k m=(fun _ => (0 : ℝ)) := by
  funext t
  unfold Scalar.xiSlice
  rw [show m^(2*k)=(m^2)^k by rw [pow_mul],hm]
  simp

lemma variationalValue_eq_zero_of_sq_eq_one (k : ℕ) {m : ℝ} (hm : m^2=1) :
    Scalar.variationalValue (Scalar.xiSlice k m) 0=0 := by
  rw [xiSlice_eq_zero_of_sq_eq_one k hm]
  have hfinite : GroundState.FiniteNonnegativeCovariance (fun _ : ℝ => 0) :=
    ⟨0,(fun _ => 0),(by simp),(by simp)⟩
  simpa using RSVariationalProof.generalRSVariationalLaw
    (fun _ : ℝ => 0) 0 hfinite (le_refl 0) (by simp)

/-- Actual endpoint ground limits, including all positive dimensions and all
natural tensor degrees. No interior-overlap physical formula is an input. -/
theorem sliceGroundLimit_of_sq_eq_one (k : ℕ) {m : ℝ} (hm : m^2=1) :
    GroundState.SliceGroundLimit k m := by
  unfold GroundState.SliceGroundLimit
  have hpoint (n : ℕ) : GroundState.expectedSliceGround (n+1) k m=0 :=
    expectedSliceGround_eq_zero_of_sq_eq_one (by omega) k hm
  simpa only [hpoint,variationalValue_eq_zero_of_sq_eq_one k hm] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end
end TensorPCA.SliceGroundEndpointsProofs
