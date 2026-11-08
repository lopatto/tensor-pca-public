-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GroundUpperProofs

/-! The slice mean is even in the overlap. The Gaussian coefficients
may change signs; equality follows from their exact increment covariance,
without assuming an unproved symmetry of a physical ground-state limit. -/
@[expose] public section
namespace TensorPCA.SliceGroundSymmetryProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

lemma xiSlice_abs (k : ℕ) (m : ℝ) : Scalar.xiSlice k |m|=Scalar.xiSlice k m := by
  funext t
  unfold Scalar.xiSlice
  rw [show |m|^(2*k)=(|m|^2)^k by rw [pow_mul],
    show m^(2*k)=(m^2)^k by rw [pow_mul],sq_abs]

lemma sliceFeature_increment_abs_eq {N k : ℕ} {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) {x y : Model.Vector N}
    (hx : x ∈ Model.unitSphere N) (hy : y ∈ Model.unitSphere N) :
    ‖GroundState.sliceFeature k |m| x-GroundState.sliceFeature k |m| y‖ =
      ‖GroundState.sliceFeature k m x-GroundState.sliceFeature k m y‖ := by
  have hma : |m| ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [abs_nonneg m],abs_le.mpr hm⟩
  have hpow : |m|^(2*k)=m^(2*k) := by rw [pow_mul,pow_mul,sq_abs]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real,norm_sub_sq_real,
    GroundUpperProofs.sliceFeature_norm_sq hma hx,GroundUpperProofs.sliceFeature_norm_sq hma hy,
    GroundUpperProofs.sliceFeature_norm_sq hm hx,GroundUpperProofs.sliceFeature_norm_sq hm hy,
    GroundUpperProofs.sliceFeature_inner hma,GroundUpperProofs.sliceFeature_inner hm,hpow,xiSlice_abs]

/-- Exact finite mean symmetry of the independently defined Gaussian slice. -/
theorem expectedSliceGround_abs {N k : ℕ} (hN : 0<N) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.expectedSliceGround N k |m|=GroundState.expectedSliceGround N k m := by
  let : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  let : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  let a : Model.unitSphere N → GroundState.Disorder N k :=
    fun x => GroundState.sliceFeature k |m| x
  let b : Model.unitSphere N → GroundState.Disorder N k :=
    fun x => GroundState.sliceFeature k m x
  have ha : Continuous a :=
    (GroundUpperProofs.continuous_sliceFeature N k |m|).comp continuous_subtype_val
  have hb : Continuous b :=
    (GroundUpperProofs.continuous_sliceFeature N k m).comp continuous_subtype_val
  have hinc (x y : Model.unitSphere N) : ‖a x-a y‖=‖b x-b y‖ :=
    sliceFeature_increment_abs_eq hm x.property y.property
  have H := le_antisymm
    (GaussianMaximumComparisonProofs.expected_supremum_comparison a b ha hb (fun x y => (hinc x y).le))
    (GaussianMaximumComparisonProofs.expected_supremum_comparison b a hb ha (fun x y => (hinc x y).ge))
  have hsup (r : ℝ) (g : GroundState.Disorder N k) :
      sSup ((fun x => inner ℝ (GroundState.sliceFeature k r x) g) '' Model.unitSphere N) =
        ⨆ x : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k r x) g := by
    rw [iSup,Set.image_eq_range]
  unfold GroundState.expectedSliceGround
  simp_rw [hsup]
  rw [integral_div,integral_div]
  exact congrArg (fun z : ℝ => z/(N : ℝ)) H

/-- A positive-overlap physical formula transports to signed overlap. -/
theorem sliceGroundLimit_abs_iff (k : ℕ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.SliceGroundLimit k |m| ↔ GroundState.SliceGroundLimit k m := by
  unfold GroundState.SliceGroundLimit
  have hpoint (n : ℕ) : GroundState.expectedSliceGround (n+1) k |m|=
      GroundState.expectedSliceGround (n+1) k m := expectedSliceGround_abs (by omega) hm
  simp only [hpoint,xiSlice_abs]

end
end TensorPCA.SliceGroundSymmetryProofs
