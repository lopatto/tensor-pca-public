-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedASSLower
public import TensorPCA.NonRSLowerProofs.FiniteCavityASSLower
public import TensorPCA.NonRSLowerProofs.GaussianFeatureIncrementComparison

/-! The normalized pressure perturbation cost. This is separate from the fixed-M
perturbation-compatible increment already proved.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationPressureBudget
open MeasureTheory ProbabilityTheory Set Filter GaussianSpinInterpolation
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison GaussianFeatureIncrementComparison
open FiniteCavityPerturbedFields FiniteCavityPerturbedASSLower FiniteCavityASSLower
open FiniteCavityCompensationJointPressure FiniteCavityPerturbationReference
open FiniteCavityReferenceRestriction FinitePerturbationScaleAsymptotics
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem norm_fst_le_sumJoin {I J : Type*} [Fintype I] [Fintype J]
    (a : EuclideanSpace ℝ I) (b : EuclideanSpace ℝ J) : ‖a‖≤‖sumJoin (a,b)‖ := by
  have hs : ‖sumJoin (a,b)‖^2=‖a‖^2+‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq,sumJoin_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith only [hs,norm_nonneg a,norm_nonneg (sumJoin (a,b)),sq_nonneg ‖b‖]

theorem pressure_perturbation_bounds {N k K : ℕ} (hN : 0<N) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) :
    0≤expectedLogPerturbedSlicePartition N k K mu beta v a-expectedLogSlicePartition N k mu beta ∧
      expectedLogPerturbedSlicePartition N k K mu beta v a-expectedLogSlicePartition N k mu beta≤4*v^2 := by
  let f := fun x : Model.Vector N => beta • GroundState.sliceFeature k mu x
  let p := perturbedSliceFeature N k K mu beta v a
  have hf := ((GroundUpperProofs.continuous_sliceFeature N k mu).const_smul beta).measurable
  have hp := (perturbedSliceFeature_continuous N k K mu beta v a).measurable
  have hbf : ∀ᵐ x∂Model.spherePrior N,‖f x‖≤|beta| *Real.sqrt (N : ℝ) :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx => thermal_sliceFeature_unit_bound hmu beta hx)
  have hbp : ∀ᵐ x∂Model.spherePrior N,‖p x‖≤|beta| *Real.sqrt (N : ℝ)+2*|v| :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx => perturbedSliceFeature_unit_bound hmu beta v a ha hx)
  have hinc (x y : Model.Vector N) : ‖f x-f y‖≤‖p x-p y‖ := by
    change ‖f x-f y‖≤‖sumJoin (f x,feature (coefficients v a) x)-sumJoin (f y,feature (coefficients v a) y)‖
    rw [← map_sub]
    exact norm_fst_le_sumJoin _ _
  have hLow := expected_logPartition_le_of_increment_le (Model.spherePrior N) f p hf hp
    (by positivity) (by positivity) hbf hbp hinc
  have hxy (x y : Model.Vector N) (hx : ‖x‖=1) (hy : ‖y‖=1) :
      |inner ℝ (p x) (p y)-inner ℝ (f x) (f y)|≤4*v^2 := by
    change |inner ℝ (sumJoin (f x,feature (coefficients v a) x))
      (sumJoin (f y,feature (coefficients v a) y))-inner ℝ (f x) (f y)|≤_
    rw [sumJoin_inner,add_sub_cancel_left]
    calc
      _ ≤ ‖feature (coefficients v a) x‖*‖feature (coefficients v a) y‖ := abs_real_inner_le_norm _ _
      _ ≤ (2*|v|)*(2*|v|) := mul_le_mul (perturbationFeature_unit_norm_le v a ha hx)
        (perturbationFeature_unit_norm_le v a ha hy) (norm_nonneg _) (by positivity)
      _ = _ := by nlinarith only [sq_abs v]
  have hDiag : ∀ᵐ x∂Model.spherePrior N,|inner ℝ (p x) (p x)-inner ℝ (f x) (f x)|≤4*v^2 :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx => hxy x x hx hx)
  have hPair : ∀ᵐ z∂(Model.spherePrior N).prod (Model.spherePrior N),
      |inner ℝ (p z.1) (p z.2)-inner ℝ (f z.1) (f z.2)|≤4*v^2 := by
    have hx : ∀ᵐ z∂(Model.spherePrior N).prod (Model.spherePrior N),‖z.1‖=1 :=
      Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
    have hy : ∀ᵐ z∂(Model.spherePrior N).prod (Model.spherePrior N),‖z.2‖=1 :=
      Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hN)
    filter_upwards [hx,hy] with z hx hy
    exact hxy z.1 z.2 hx hy
  have hAbs := expected_logPartition_abs_sub_le (Model.spherePrior N) p f hp hf
    (by positivity) (by positivity) hbp hbf hDiag hPair
  change expectedLogSlicePartition N k mu beta≤expectedLogPerturbedSlicePartition N k K mu beta v a at hLow
  change |expectedLogPerturbedSlicePartition N k K mu beta v a-expectedLogSlicePartition N k mu beta|≤_ at hAbs
  constructor
  · linarith only [hLow]
  · have H := (abs_le.mp hAbs).2
    linarith only [H]

theorem normalized_pressure_perturbation_cost (k K : ℕ) {mu gamma : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (hgamma0 : 0<gamma) (hgamma1 : gamma<1/2) (beta : ℝ)
    {eps : ℝ} (heps : 0<eps) :
    ∀ᶠ N : ℕ in atTop,∀a : Fin K→ℝ,(∀p,|a p|≤2) →
      |expectedLogPerturbedSlicePartition N k K mu beta ((N : ℝ)^gamma) a/(N : ℝ)-
        expectedLogSlicePartition N k mu beta/(N : ℝ)|≤eps := by
  have hA0 : 0<2*gamma := by linarith only [hgamma0]
  have hA1 : 2*gamma<1 := by linarith only [hgamma1]
  have hLimit : Tendsto (fun N : ℕ => 4*((N : ℝ)^gamma)^2/(N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have H := (rpow_shift_div_dimension_tendsto_zero 0 hA0 hA1).const_mul 4
    convert H using 1
    · funext N
      rw [square_rpow_natCast]
      simp only [Nat.add_zero]
      ring
    · norm_num
  filter_upwards [eventually_gt_atTop (0 : ℕ),hLimit.eventually (gt_mem_nhds heps)] with N hN hSmall
  intro a ha
  have H := pressure_perturbation_bounds (k := k) hN hmu beta ((N : ℝ)^gamma) a ha
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  rw [← sub_div,abs_div,abs_of_pos hn,abs_of_nonneg H.1]
  exact (div_le_div_of_nonneg_right H.2 hn.le).trans hSmall.le

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationPressureBudget
