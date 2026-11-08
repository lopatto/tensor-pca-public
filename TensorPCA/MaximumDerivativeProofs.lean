-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.MleEstimatorProofs
public import TensorPCA.MaximumProofs
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of sample and expected likelihood maxima at each
fixed deterministic strength. The null set may depend on that strength. -/

@[expose] public section
namespace TensorPCA.MaximumDerivativeProofs
open Set Filter MeasureTheory ProbabilityTheory GaussianMaximumProofs MleSelectorProofs
  MleEstimatorProofs
open scoped Topology RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem supportValue_tensorImage (N k : ℕ) (y : Model.Tensor N k) :
    supportValue (tensorImage N k) (fun _ ↦ 0) y =
      sSup (Model.score y '' Model.unitSphere N) := by
  unfold supportValue tensorImage
  congr 1
  ext a
  constructor
  · rintro ⟨T, ⟨x, hx, rfl⟩, heq⟩
    exact ⟨x, hx, by simpa only [add_zero, Model.score] using heq⟩
  · rintro ⟨x, hx, heq⟩
    exact ⟨Model.feature k x, mem_image_of_mem _ hx,
      by simpa only [add_zero, Model.score] using heq⟩

theorem supportValue_hasFDerivAt_canonicalTensor {N k : ℕ} (hN : 0 < N)
    {y : Model.Tensor N k}
    (hd : DifferentiableAt ℝ (supportValue (tensorImage N k) (fun _ ↦ 0)) y) :
    HasFDerivAt (supportValue (tensorImage N k) (fun _ ↦ 0))
      (innerSL ℝ (canonicalTensor N k hN y)) y := by
  have hK := tensorImage_isCompact N k
  have hne : (tensorImage N k).Nonempty := (Geometry.unitSphere_nonempty hN).image _
  obtain ⟨T, hT, hmax, _⟩ := supportValue_attained hK hne
    (continuousOn_const (c := (0 : ℝ))) y
  have hgrad := supportGradient_eq_of_maximizer hK hne
    (continuousOn_const (c := (0 : ℝ))) hT hmax hd
  have hcan : canonicalTensor N k hN y = T := by
    unfold canonicalTensor compactSelector
    rw [hgrad]
    exact ite_eq_left hT
  have hderiv := derivative_eq_of_maximizer hK hne
    (continuousOn_const (c := (0 : ℝ))) hT hmax hd.hasFDerivAt
  simpa only [hcan, hderiv] using hd.hasFDerivAt

theorem strengthMaximum_lipschitz {N k : ℕ} (hN : 0 < N) (x : Model.Vector N)
    (hx : x ∈ Model.unitSphere N) (w : Model.Tensor N k) :
    LipschitzWith 1 (fun lam : ℝ ↦ Model.normalizedMaximum (Model.observation lam (x, w))) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  apply LipschitzWith.of_le_add_mul 1
  intro a b
  have hnorm : ‖Model.observation a (x, w)-Model.observation b (x, w)‖ =
      |a-b| *Real.sqrt N := by
    rw [Model.observation, Model.observation, add_sub_add_right_eq_sub, ← sub_smul,
      ← sub_mul, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), Geometry.feature_unit_norm x hx, mul_one]
  calc
    Model.normalizedMaximum (Model.observation a (x, w)) ≤
      (sSup (Model.score (Model.observation b (x, w)) '' Model.unitSphere N)+
        ‖Model.observation a (x, w)-Model.observation b (x, w)‖)/Real.sqrt N :=
      div_le_div_of_nonneg_right (Geometry.score_sup_compare hN _ _) hs.le
    _ = Model.normalizedMaximum (Model.observation b (x, w))+1*dist a b := by
      rw [hnorm, Model.normalizedMaximum, add_div, Real.dist_eq]
      field_simp [hs.ne']

theorem sampleMaximum_hasDerivAt {N : ℕ} (hN : 0 < N) (k : ℕ) (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N (k+1))
    (hd : DifferentiableAt ℝ (supportValue (tensorImage N (k+1)) (fun _ ↦ 0))
      (Model.observation lam z)) :
    HasDerivAt (fun u : ℝ ↦ Model.normalizedMaximum (Model.observation u z))
      ((inner ℝ (vectorSelector N k hN (Model.observation lam z)) z.1)^(k+1)) lam := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hobs : HasDerivAt (fun u : ℝ ↦ Model.observation u z)
      (Real.sqrt N • Model.feature (k+1) z.1) lam := by
    simpa only [Model.observation, one_mul, id_eq] using
      (((hasDerivAt_id lam).mul_const (Real.sqrt N)).smul_const
        (Model.feature (k+1) z.1)).add_const z.2
  have hchain := (supportValue_hasFDerivAt_canonicalTensor hN hd).comp_hasDerivAt lam hobs
  have hdiv := hchain.div_const (Real.sqrt N)
  have hvalue : innerSL ℝ (canonicalTensor N (k+1) hN (Model.observation lam z))
      (Real.sqrt N • Model.feature (k+1) z.1)/Real.sqrt N =
      (inner ℝ (vectorSelector N k hN (Model.observation lam z)) z.1)^(k+1) := by
    rw [innerSL_apply_apply, inner_smul_right,
      ← (vectorSelector_spec N k hN (Model.observation lam z)).2, Geometry.feature_inner]
    field_simp [hs.ne']
  have hfun : (fun u : ℝ ↦ Model.normalizedMaximum (Model.observation u z)) =
      (fun u : ℝ ↦ supportValue (tensorImage N (k+1)) (fun _ ↦ 0)
        (Model.observation u z)/Real.sqrt N) := by
    funext u
    rw [Model.normalizedMaximum, supportValue_tensorImage]
  rw [hfun]
  simpa only [Function.comp_def, hvalue] using hdiv

theorem ae_sampleMaximum_hasDerivAt {N : ℕ} (hN : 0 < N) (k : ℕ) (lam : ℝ) :
    ∀ᵐ z ∂Model.experimentLaw N (k+1),
      HasDerivAt (fun u : ℝ ↦ Model.normalizedMaximum (Model.observation u z))
        ((inner ℝ (vectorSelector N k hN (Model.observation lam z)) z.1)^(k+1)) lam := by
  have hK := tensorImage_isCompact N (k+1)
  have hne : (tensorImage N (k+1)).Nonempty := (Geometry.unitSphere_nonempty hN).image _
  obtain ⟨M, hLip⟩ := supportValue_lipschitz hK hne (continuousOn_const (c := (0 : ℝ)))
  have hd : ∀ᵐ y ∂Model.observationLaw N (k+1) lam,
      DifferentiableAt ℝ (supportValue (tensorImage N (k+1)) (fun _ ↦ 0)) y :=
    (observationLaw_absolutelyContinuous_volume N (k+1) lam).ae_le hLip.ae_differentiableAt
  have hmp : MeasurePreserving (Model.observation lam)
      (Model.experimentLaw N (k+1)) (Model.observationLaw N (k+1) lam) :=
    ⟨Model.measurable_observation N (k+1) lam, rfl⟩
  exact (hmp.quasiMeasurePreserving.ae hd).mono (fun z hz ↦ sampleMaximum_hasDerivAt hN k lam z hz)


def selectedSlope (N k : ℕ) (hN : 0 < N) (lam : ℝ) : ℝ :=
  ∫ z : Model.Vector N × Model.Tensor N (k+1),
    (inner ℝ (vectorSelector N k hN (Model.observation lam z)) z.1)^(k+1)
      ∂Model.experimentLaw N (k+1)

theorem selectedOverlap_measurable (N k : ℕ) (hN : 0 < N) (lam : ℝ) :
    Measurable (fun z : Model.Vector N × Model.Tensor N (k+1) ↦
      (inner ℝ (vectorSelector N k hN (Model.observation lam z)) z.1)^(k+1)) := by
  have hs := (vectorSelector_measurable N k hN).comp
    (Model.measurable_observation N (k+1) lam)
  exact (continuous_inner.measurable.comp (hs.prodMk measurable_fst)).pow_const (k+1)

theorem expectedMaximum_hasDerivAt {N : ℕ} (hN : 0 < N) (k : ℕ) (lam : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Model.expectedMaximum N (k+1) u) (selectedSlope N k hN lam) lam := by
  have hmeas : ∀ᶠ u in 𝓝 lam, AEStronglyMeasurable
      (fun z : Model.Vector N × Model.Tensor N (k+1) ↦
        Model.normalizedMaximum (Model.observation u z)) (Model.experimentLaw N (k+1)) := by
    apply Filter.Eventually.of_forall
    intro u
    exact ((Geometry.normalizedMaximum_lipschitz (k := k+1) hN).continuous.measurable.comp
      (Model.measurable_observation N (k+1) u)).aestronglyMeasurable
  have hunit : ∀ᵐ z ∂Model.experimentLaw N (k+1), z.1 ∈ Model.unitSphere N :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hone : Real.nnabs (1 : ℝ) = (1 : ℝ≥0) := by ext; norm_num
  have hlip : ∀ᵐ z ∂Model.experimentLaw N (k+1),
      LipschitzOnWith (Real.nnabs (1 : ℝ))
        (fun u : ℝ ↦ Model.normalizedMaximum (Model.observation u z)) univ := by
    filter_upwards [hunit] with z hz
    rcases z with ⟨x, w⟩
    rw [hone]
    exact (strengthMaximum_lipschitz hN x hz w).lipschitzOnWith
  have H := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := Model.experimentLaw N (k+1)) (s := (univ : Set ℝ)) (x₀ := lam)
    (F := fun u (z : Model.Vector N × Model.Tensor N (k+1)) ↦
      Model.normalizedMaximum (Model.observation u z))
    (F' := fun z ↦ (inner ℝ (vectorSelector N k hN (Model.observation lam z)) z.1)^(k+1))
    (bound := fun _ ↦ (1 : ℝ)) (Filter.univ_mem) hmeas
    (MaximumProofs.plantedMaximum_integrable hN lam)
    (selectedOverlap_measurable N k hN lam).aestronglyMeasurable
    hlip (integrable_const 1) (ae_sampleMaximum_hasDerivAt hN k lam)
  simpa only [Model.expectedMaximum, selectedSlope] using H.2

theorem expectedMaximum_lipschitz {N k : ℕ} (hN : 0 < N) :
    LipschitzWith 1 (Model.expectedMaximum N k) := by
  apply LipschitzWith.of_le_add_mul 1
  intro a b
  have hunit : ∀ᵐ z ∂Model.experimentLaw N k, z.1 ∈ Model.unitSphere N :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hle : ∀ᵐ z ∂Model.experimentLaw N k,
      Model.normalizedMaximum (Model.observation a z) ≤
        Model.normalizedMaximum (Model.observation b z)+dist a b := by
    filter_upwards [hunit] with z hz
    simpa only [NNReal.coe_one, one_mul] using
      (strengthMaximum_lipschitz hN z.1 hz z.2).le_add_mul a b
  change (∫ z, Model.normalizedMaximum (Model.observation a z) ∂Model.experimentLaw N k) ≤
    (∫ z, Model.normalizedMaximum (Model.observation b z) ∂Model.experimentLaw N k)+1*dist a b
  calc
    _ ≤ ∫ z, Model.normalizedMaximum (Model.observation b z)+dist a b
        ∂Model.experimentLaw N k :=
      integral_mono_ae (MaximumProofs.plantedMaximum_integrable hN a)
        ((MaximumProofs.plantedMaximum_integrable hN b).add (integrable_const _)) hle
    _ = _ := by rw [integral_add (MaximumProofs.plantedMaximum_integrable hN b)
      (integrable_const _)]; simp


theorem selectedSlope_measurable (N k : ℕ) (hN : 0 < N) :
    Measurable (selectedSlope N k hN) := by
  convert measurable_deriv (fun u : ℝ ↦ Model.expectedMaximum N (k+1) u) using 1
  funext u
  exact (expectedMaximum_hasDerivAt hN k u).deriv.symm

theorem selectedSlope_abs_le_one (N k : ℕ) (hN : 0 < N) (lam : ℝ) :
    |selectedSlope N k hN lam| ≤ 1 := by
  have h := norm_deriv_le_of_lipschitz (x₀ := lam)
    (expectedMaximum_lipschitz (k := k+1) hN)
  rw [(expectedMaximum_hasDerivAt hN k lam).deriv] at h
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using h

theorem selectedSlope_intervalIntegrable (N k : ℕ) (hN : 0 < N) (a b : ℝ) :
    IntervalIntegrable (selectedSlope N k hN) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume a b).mono_fun
  · exact (selectedSlope_measurable N k hN).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u ↦ by
      simpa only [Real.norm_eq_abs, abs_one] using selectedSlope_abs_le_one N k hN u)

/-- The finite-N expected-maximum identity, obtained from the actual signed
MLE overlap derivative. The derivative integrand is Borel and bounded by1. -/
theorem expectedMaximum_integral_identity (N k : ℕ) (hN : 0 < N) (a b : ℝ) :
    Model.expectedMaximum N (k+1) b = Model.expectedMaximum N (k+1) a+
      ∫ u in a..b, selectedSlope N k hN u := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun u _ ↦ expectedMaximum_hasDerivAt hN k u) (selectedSlope_intervalIntegrable N k hN a b)
  linarith


/-- The selected derivative equals the signed overlap moment of the actual
fair-sign MLE, so the finite estimator bounds apply to this same integrand. -/
theorem selectedSlope_eq_fairEstimator (N k : ℕ) (hN : 0 < N) (lam : ℝ) :
    selectedSlope N k hN lam =
      ∫ z : (Model.Vector N × Model.Tensor N (k+1)) × Bool,
        (inner ℝ (fairEstimator N k hN (Model.observation lam z.1) z.2) z.1.1)^(k+1)
          ∂(Model.experimentLaw N (k+1)).prod fairSeed := by
  have hfun : (fun z : (Model.Vector N × Model.Tensor N (k+1)) × Bool ↦
      (inner ℝ (fairEstimator N k hN (Model.observation lam z.1) z.2) z.1.1)^(k+1)) =
      (fun z ↦ (inner ℝ (vectorSelector N k hN (Model.observation lam z.1)) z.1.1)^(k+1)) := by
    funext z
    rw [← Geometry.feature_inner, ← Geometry.feature_inner,
      fairEstimator_feature N k hN (Model.observation lam z.1) z.2]
  rw [hfun]
  have hmp := measurePreserving_fst
    (μ := Model.experimentLaw N (k+1)) (ν := fairSeed)
  simpa only [selectedSlope, hmp.map_eq] using
    integral_map (μ := (Model.experimentLaw N (k+1)).prod fairSeed)
      hmp.measurable.aemeasurable (selectedOverlap_measurable N k hN lam).aestronglyMeasurable

end
end TensorPCA.MaximumDerivativeProofs
