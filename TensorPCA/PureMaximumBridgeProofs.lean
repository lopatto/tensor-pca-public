-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumExpectedUpperProofs
public import TensorPCA.SliceDecompositionProofs
public import TensorPCA.PureVariationalProofs

/-! Exact finite normalization between the physical pure null maximum and the
independently represented zero-overlap mixture ground process. This proves no
physical ground-state limit; it transports such a limit when available. -/
@[expose] public section
namespace TensorPCA.PureMaximumBridgeProofs
open MeasureTheory ProbabilityTheory Set Filter SliceDecompositionProofs
open scoped Topology RealInnerProductSpace
noncomputable section

theorem pure_feature_increment_eq {N k : ℕ} (hN : 0 < N)
    {x y : Model.Vector N} (hx : x ∈ Model.unitSphere N) (hy : y ∈ Model.unitSphere N) :
    ‖Model.feature k x-Model.feature k y‖ =
      ‖(Real.sqrt N)⁻¹ • GroundState.sliceFeature k 0 x-
        (Real.sqrt N)⁻¹ • GroundState.sliceFeature k 0 y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real,Geometry.feature_unit_norm x hx,Geometry.feature_unit_norm y hy,
    Geometry.feature_inner,scaled_slice_increment_sq hN (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hx hy]
  norm_num
  ring

theorem expected_pure_supremum_eq {N k : ℕ} (hN : 0 < N) :
    (∫ w : Model.Tensor N k, (⨆ u : Model.unitSphere N,
      inner ℝ (Model.feature k u) w) ∂stdGaussian (Model.Tensor N k)) =
      ∫ g : GroundState.Disorder N k, (⨆ u : Model.unitSphere N,
        inner ℝ ((Real.sqrt N)⁻¹ • GroundState.sliceFeature k 0 u) g)
          ∂stdGaussian (GroundState.Disorder N k) := by
  have : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  have : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  have hu : Continuous (fun u : Model.unitSphere N ↦ (u : Model.Vector N)) := continuous_subtype_val
  exact expected_supremum_eq_of_increment_eq _ _ ((Model.continuous_feature N k).comp hu)
    ((continuous_const_smul ((Real.sqrt N)⁻¹)).comp ((GroundUpperProofs.continuous_sliceFeature N k 0).comp hu))
    (fun u v ↦ pure_feature_increment_eq hN u.property v.property)

/-- The physical pure null baseline and actual zero-overlap mixture maximum
have exactly the same expectation in every positive dimension. -/
theorem expectedMaximum_zero_eq_expectedSliceGround {N k : ℕ} (hN : 0 < N) :
    Model.expectedMaximum N k 0 = GroundState.expectedSliceGround N k 0 := by
  obtain ⟨x,hx⟩ := Geometry.unitSphere_nonempty hN
  rw [MaximumProofs.expectedMaximum_eq_fixed_direction hN 0 x hx]
  simp only [zero_mul,zero_smul,zero_add]
  unfold Model.normalizedMaximum Model.noiseLaw GroundState.expectedSliceGround
  have hsup (w : Model.Tensor N k) :
      sSup (Model.score w '' Model.unitSphere N) =
        ⨆ u : Model.unitSphere N, inner ℝ (Model.feature k u) w := by
    rw [iSup,Set.image_eq_range]
    rfl
  have hsupG (g : GroundState.Disorder N k) :
      sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k 0 x) g) '' Model.unitSphere N) =
        ⨆ u : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k 0 u) g := by
    rw [iSup,Set.image_eq_range]
  simp_rw [hsup,hsupG]
  rw [integral_div,integral_div,expected_pure_supremum_eq hN]
  simp_rw [scaled_slice_supremum hN 0]
  rw [integral_const_mul]
  have hsq : Real.sqrt (N : ℝ)*Real.sqrt N = N := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  calc
    _ = (∫ g : GroundState.Disorder N k,
        (⨆ u : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k 0 u) g)
          ∂stdGaussian (GroundState.Disorder N k))/(Real.sqrt N*Real.sqrt N) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hsq]

/-- An independently represented pure ground-state limit transports to the null MLE baseline, with the separately proved scalar value. -/
theorem expectedMaximum_zero_tendsto_of_ground (k : ℕ) (hk : 3 ≤ k)
    (hground : GroundState.SliceGroundLimit k 0) :
    Tendsto (fun n : ℕ ↦ Model.expectedMaximum (n+1) k 0) atTop (𝓝 (Scalar.gs k)) := by
  have H : Tendsto (fun n : ℕ ↦ Model.expectedMaximum (n+1) k 0) atTop
      (𝓝 (Scalar.variationalValue (Scalar.xiSlice k 0) 0)) := by
    apply hground.congr'
    exact Eventually.of_forall (fun n ↦ (expectedMaximum_zero_eq_expectedSliceGround (k := k) (Nat.succ_pos n)).symm)
  simpa only [PureVariationalProofs.pure_variationalValue_xiSlice_zero k hk] using H

/-- Expected-MLE upper comparison with Bayesian and pure-ground hypotheses. -/
theorem expectedMaximum_limsup_upper_of_values_and_ground (k : ℕ) (hk : 2 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence (k+1))
    (hground : GroundState.SliceGroundLimit (k+1) 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    limsup (fun n : ℕ ↦ Model.expectedMaximum (n+1) (k+1) lam) atTop ≤
      Scalar.mleValue (k+1) lam :=
  MaximumExpectedUpperProofs.expectedMaximum_limsup_upper_of_values_and_baseline k hk hvalues
    (expectedMaximum_zero_tendsto_of_ground (k+1) (by omega) hground) hlam

end
end TensorPCA.PureMaximumBridgeProofs
