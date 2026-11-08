-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSZeroTemperatureComparison
public import TensorPCA.GroundUpperProofs
public import TensorPCA.GaussianSpinInterpolationProofs
/-! Finite slice pressure and its lower-ground reduction. The proof parameter is a
finite-temperature pressure lower bound, rather than a ground-state limit. This
module exports conditional reductions.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.PhysicalPressureGroundReduction
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
open FiniteCSZeroTemperature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal disorder-averaged spherical log partition, divided by beta*N.
The feature and disorder are exactly those of GroundState.expectedSliceGround. -/
def expectedSlicePressure (N k : ℕ) (m beta : ℝ) : ℝ :=
  (∫ g : GroundState.Disorder N k,
    Real.log (∫ x : Model.Vector N, Real.exp (beta*inner ℝ (GroundState.sliceFeature k m x) g)
      ∂Model.spherePrior N) ∂stdGaussian (GroundState.Disorder N k))/(beta*(N : ℝ))

private def sliceLinear (N k : ℕ) (m : ℝ) (x : Model.Vector N) :
    GroundState.Disorder N k →L[ℝ] ℝ := innerSL ℝ (GroundState.sliceFeature k m x)

private theorem sliceLinear_continuous (N k : ℕ) (m : ℝ) : Continuous (sliceLinear N k m) :=
  (innerSL ℝ).continuous.comp (GroundUpperProofs.continuous_sliceFeature N k m)

private theorem sliceLinear_bound {N : ℕ} (hN : 0 < N) (k : ℕ) (m : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Model.unitSphere N, ‖sliceLinear N k m x‖ ≤ K := by
  classical
  letI : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  letI : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  obtain ⟨K, hK, hBound⟩ := GaussianCompactMaximum.exists_feature_bound
    (fun x : Model.unitSphere N ↦ sliceLinear N k m x)
    ((sliceLinear_continuous N k m).comp continuous_subtype_val)
  exact ⟨K, hK, fun x hx ↦ hBound ⟨x, hx⟩⟩

private theorem logPartition_eq (N k : ℕ) (m beta : ℝ) (g : GroundState.Disorder N k) :
    GaussianSpinInterpolation.logPartition (Model.spherePrior N) (sliceLinear N k m) (beta • g) =
      Real.log (∫ x : Model.Vector N, Real.exp (beta*inner ℝ (GroundState.sliceFeature k m x) g)
        ∂Model.spherePrior N) := by
  unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    GaussianSpinInterpolation.weight sliceLinear
  simp only [one_mul, innerSL_apply_apply, inner_smul_right]

theorem sliceLogPartition_integrable {N : ℕ} (hN : 0 < N) (k : ℕ) (m beta : ℝ) :
    Integrable (fun g : GroundState.Disorder N k ↦
      Real.log (∫ x : Model.Vector N, Real.exp (beta*inner ℝ (GroundState.sliceFeature k m x) g)
        ∂Model.spherePrior N)) (stdGaussian (GroundState.Disorder N k)) := by
  classical
  obtain ⟨K, hK, hBound⟩ := sliceLinear_bound hN k m
  have hb : ∀ᵐ x ∂Model.spherePrior N, ‖sliceLinear N k m x‖ ≤ K :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx ↦ hBound x hx)
  have H := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable
    (Model.spherePrior N) (sliceLinear N k m) (sliceLinear_continuous N k m).measurable hK hb beta
  simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge, logPartition_eq] using H

theorem sliceLogPartition_le_supremum {N : ℕ} (hN : 0 < N) (k : ℕ) (m : ℝ)
    {beta : ℝ} (hbeta : 0 < beta) (g : GroundState.Disorder N k) :
    Real.log (∫ x : Model.Vector N, Real.exp (beta*inner ℝ (GroundState.sliceFeature k m x) g)
      ∂Model.spherePrior N) ≤
      beta*sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) := by
  classical
  letI : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  obtain ⟨K, hK, hBound⟩ := sliceLinear_bound hN k m
  have hb : ∀ᵐ x ∂Model.spherePrior N, ‖sliceLinear N k m x‖ ≤ K :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx ↦ hBound x hx)
  have hInt := GaussianSpinInterpolation.weight_integrable (Model.spherePrior N) (fun _ ↦ 1)
    (sliceLinear N k m) measurable_const (sliceLinear_continuous N k m).measurable
    (C := (1 : ℝ)) (K := K)
    (hb.mono (fun x hx ↦ ⟨by norm_num, hx⟩)) (beta • g)
  have hi : Integrable (fun x : Model.Vector N ↦
      Real.exp (beta*inner ℝ (GroundState.sliceFeature k m x) g)) (Model.spherePrior N) := by
    change Integrable (fun x ↦ 1*Real.exp (sliceLinear N k m x (beta • g)))
      (Model.spherePrior N) at hInt
    simpa only [one_mul, sliceLinear,
      innerSL_apply_apply, inner_smul_right] using hInt
  have hsup : BddAbove (range (fun x : Model.unitSphere N ↦
      inner ℝ (GroundState.sliceFeature k m x) g)) :=
    GaussianCompactMaximum.field_bddAbove (fun x : Model.unitSphere N ↦ sliceLinear N k m x)
      (fun x ↦ hBound x x.property) g
  have heq : sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) =
      ⨆ x : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k m x) g := by
    rw [iSup, Set.image_eq_range]
  have H := integral_mono_ae hi (integrable_const
    (Real.exp (beta*(⨆ x : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k m x) g))))
    ((Geometry.spherePrior_norm_ae hN).mono (fun x hx ↦
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_ciSup hsup ⟨x, hx⟩) hbeta.le)))
  simp only [integral_const, probReal_univ, one_smul] at H
  have hLog := Real.log_le_log (integral_exp_pos hi) H
  rw [Real.log_exp] at hLog
  rwa [heq]

theorem expectedSlicePressure_le_expectedSliceGround {N : ℕ} (hN : 0 < N)
    (k : ℕ) (m : ℝ) {beta : ℝ} (hbeta : 0 < beta) :
    expectedSlicePressure N k m beta ≤ GroundState.expectedSliceGround N k m := by
  classical
  letI : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  letI : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  let a : Model.unitSphere N → GroundState.Disorder N k :=
    fun x ↦ GroundState.sliceFeature k m x
  have ha : Continuous a :=
    (GroundUpperProofs.continuous_sliceFeature N k m).comp continuous_subtype_val
  have hsup (g : GroundState.Disorder N k) :
      sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) =
        ⨆ x : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k m x) g := by
    rw [iSup, Set.image_eq_range]
  have hInt := GaussianMaximumComparisonProofs.supremum_integrable a ha
  have H := integral_mono (sliceLogPartition_integrable hN k m beta) (hInt.const_mul beta)
    (fun g ↦ by simpa only [hsup, a] using sliceLogPartition_le_supremum hN k m hbeta g)
  rw [integral_const_mul] at H
  unfold expectedSlicePressure GroundState.expectedSliceGround
  simp_rw [hsup]
  rw [integral_div]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ (mul_pos hbeta hNr)).mpr
  convert H using 1 <;> dsimp [a] <;> field_simp [hNr.ne'] <;> ring

/-- Finite-temperature pressure input, with beta fixed before N. No pressure limit or
uniformity in beta is required.
-/
def FinitePressureLower (k : ℕ) (m : ℝ) : Prop :=
  ∀ beta : ℝ, 0 < beta → ∀ eta : ℝ, 0 < eta →
    ∀ᶠ n : ℕ in atTop, (FiniteCS.rawValue k beta m).toReal/2-eta ≤
      expectedSlicePressure (n+1) k m beta

theorem eventually_expectedSliceGround_lower_of_finitePressure (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (hpressure : FinitePressureLower k m)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, Scalar.variationalValue (Scalar.xiSlice k m) 0-eps ≤
      GroundState.expectedSliceGround (n+1) k m := by
  obtain ⟨beta, hbeta, hError⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((tendsto_uniform_error (deriv (Scalar.xiSlice k m) 1)).eventually (Iio_mem_nhds heps))).exists
  have hZeroT := variational_le_rawValue_uniform_error k hk hbeta hm
  filter_upwards [hpressure beta hbeta (eps/2) (half_pos heps)] with n hn
  have hUpper := expectedSlicePressure_le_expectedSliceGround (by omega : 0 < n+1) k m hbeta
  nlinarith


end
end TensorPCA.NonRSLowerProofs.PhysicalPressureGroundReduction
