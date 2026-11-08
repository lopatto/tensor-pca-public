-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianDensityProofs
public import TensorPCA.PosteriorProofs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The concrete bounded spherical Gaussian channel

The likelihood weight below is exactly the integrand of the model's likelihood ratio. Bounds use the proved almost sure unit norm of the feature.
They introduce no finite-support or Gaussian-prior approximation.
-/
@[expose] public section

namespace TensorPCA.GaussianChannelProofs

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Transport a density through a measurable equivalence. Adapted verbatim
from the Apache-2.0 source GaussianRegressionDensity.lean at the immutable pin
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GaussianRegressionDensity.lean
-/
theorem map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable]
  calc
    _ = ∫⁻ x, f x * g (e x) ∂μ := by
      simpa only [Function.comp_apply, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul μ hf (hg.comp e.measurable))
    _ = ∫⁻ x, f (e.symm (e x)) * g (e x) ∂μ := by simp
    _ = ∫⁻ y, f (e.symm y) * g y ∂μ.map e :=
      (lintegral_map ((hf.comp e.symm.measurable).mul hg) e.measurable).symm
    _ = _ := by
      simpa only [Function.comp_apply, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul (μ.map e) (hf.comp e.symm.measurable) hg).symm

section GaussianTranslation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_density_shift (z y : E) :
    GaussianDensityProofs.density (y - z) = GaussianDensityProofs.density y *
      Real.exp (inner ℝ z y - ‖z‖ ^ 2 / 2) := by
  have he : -(1 / 2 : ℝ) * ‖y - z‖ ^ 2 =
      -(1 / 2 : ℝ) * ‖y‖ ^ 2 + (inner ℝ z y - ‖z‖ ^ 2 / 2) := by
    rw [norm_sub_sq_real, real_inner_comm y z]
    ring
  unfold GaussianDensityProofs.density
  rw [he, Real.exp_add]
  ring

/-- Exact finite-dimensional Gaussian translation density, without a separate
Cameron--Martin assumption. -/
theorem stdGaussian_map_add_eq_withDensity (z : E) :
    (stdGaussian E).map (fun y ↦ z + y) =
      (stdGaussian E).withDensity
        (fun y ↦ ENNReal.ofReal (Real.exp (inner ℝ z y - ‖z‖ ^ 2 / 2))) := by
  have hf := GaussianDensityProofs.density_continuous (E := E).measurable.ennreal_ofReal
  have hg : Measurable (fun y : E ↦ ENNReal.ofReal (Real.exp (inner ℝ z y - ‖z‖ ^ 2 / 2))) :=
    by fun_prop
  have hm := map_withDensity_equiv (MeasurableEquiv.addLeft z) (volume : Measure E)
    (fun y ↦ ENNReal.ofReal (GaussianDensityProofs.density y)) hf
  simp only [MeasurableEquiv.coe_addLeft, map_add_left_eq_self] at hm
  rw [GaussianDensityProofs.stdGaussian_eq_withDensity, hm, ← withDensity_mul volume hf hg]
  congr 1
  funext y
  simp only [Function.comp_apply, Pi.mul_apply, MeasurableEquiv.symm_addLeft,
    MeasurableEquiv.coe_addLeft]
  rw [← ENNReal.ofReal_mul (GaussianDensityProofs.density_pos y).le]
  congr 1
  simpa only [sub_eq_add_neg, add_comm] using gaussian_density_shift z y

end GaussianTranslation

noncomputable def likelihoodWeight (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k)
    (x : Model.Vector N) : ℝ :=
  Real.exp (lam * Real.sqrt N * Model.score y x - N * lam ^ 2 / 2)

theorem likelihoodRatio_eq_integral_weight (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) :
    Model.likelihoodRatio N k lam y = ∫ x, likelihoodWeight N k lam y x ∂Model.spherePrior N := rfl

theorem continuous_likelihoodWeight (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) :
    Continuous (likelihoodWeight N k lam y) := by
  have hc : Continuous (fun x : Model.Vector N ↦ Model.score y x) :=
    (Model.continuous_feature N k).inner continuous_const
  exact Real.continuous_exp.comp ((continuous_const.mul hc).sub continuous_const)

theorem likelihoodWeight_pos (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) (x : Model.Vector N) :
    0 < likelihoodWeight N k lam y x := Real.exp_pos _

theorem score_abs_le_ae {N k : ℕ} (hN : 0 < N) (y : Model.Tensor N k) :
    ∀ᵐ x ∂Model.spherePrior N, |Model.score y x| ≤ ‖y‖ := by
  filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
  have hfeature := Geometry.feature_unit_norm (k := k) x hx
  simpa only [Model.score, hfeature, one_mul] using
    abs_real_inner_le_norm (Model.feature k x) y

theorem likelihoodWeight_le_ae {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    ∀ᵐ x ∂Model.spherePrior N, likelihoodWeight N k lam y x ≤
      Real.exp (|lam * Real.sqrt N| * ‖y‖ - N * lam ^ 2 / 2) := by
  filter_upwards [score_abs_le_ae hN y] with x hx
  apply Real.exp_le_exp.mpr
  apply sub_le_sub_right
  calc
    lam * Real.sqrt N * Model.score y x ≤ |lam * Real.sqrt N * Model.score y x| := le_abs_self _
    _ = |lam * Real.sqrt N| * |Model.score y x| := abs_mul _ _
    _ ≤ |lam * Real.sqrt N| * ‖y‖ := mul_le_mul_of_nonneg_left hx (abs_nonneg _)

theorem integrable_likelihoodWeight {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    Integrable (likelihoodWeight N k lam y) (Model.spherePrior N) := by
  apply (integrable_const (Real.exp (|lam * Real.sqrt N| * ‖y‖ - N * lam ^ 2 / 2))).mono'
    (continuous_likelihoodWeight N k lam y).measurable.aestronglyMeasurable
  filter_upwards [likelihoodWeight_le_ae hN lam y] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (likelihoodWeight_pos N k lam y x)] using hx

theorem likelihoodRatio_pos {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    0 < Model.likelihoodRatio N k lam y :=
  integral_exp_pos (integrable_likelihoodWeight hN lam y)

theorem likelihoodRatio_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    Model.likelihoodRatio N k lam y ≤
      Real.exp (|lam * Real.sqrt N| * ‖y‖ - N * lam ^ 2 / 2) := by
  rw [likelihoodRatio_eq_integral_weight]
  simpa using integral_mono_ae (integrable_likelihoodWeight hN lam y)
    (integrable_const _) (likelihoodWeight_le_ae hN lam y)

theorem likelihoodWeight_lower_ae {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    ∀ᵐ x ∂Model.spherePrior N,
      Real.exp (-|lam * Real.sqrt N| * ‖y‖ - N * lam ^ 2 / 2) ≤ likelihoodWeight N k lam y x := by
  filter_upwards [score_abs_le_ae hN y] with x hx
  apply Real.exp_le_exp.mpr
  apply sub_le_sub_right
  have h := neg_le_abs (lam * Real.sqrt N * Model.score y x)
  have hb : |lam * Real.sqrt N * Model.score y x| ≤ |lam * Real.sqrt N| * ‖y‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  nlinarith

theorem likelihoodRatio_lower {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    Real.exp (-|lam * Real.sqrt N| * ‖y‖ - N * lam ^ 2 / 2) ≤
      Model.likelihoodRatio N k lam y := by
  rw [likelihoodRatio_eq_integral_weight]
  simpa using integral_mono_ae (integrable_const _)
    (integrable_likelihoodWeight hN lam y) (likelihoodWeight_lower_ae hN lam y)

theorem hasDerivAt_likelihoodWeight (N k : ℕ) (lam : ℝ)
    (y : Model.Tensor N k) (x : Model.Vector N) :
    HasDerivAt (fun t ↦ likelihoodWeight N k t y x)
      (likelihoodWeight N k lam y x * (Real.sqrt N * Model.score y x - N * lam)) lam := by
  have hl := (hasDerivAt_id lam).mul_const (Real.sqrt N * Model.score y x)
  have hq := ((hasDerivAt_pow 2 lam).const_mul (N : ℝ)).div_const 2
  convert (hl.sub hq).exp using 1
  · funext t
    dsimp [likelihoodWeight]
    congr 1
    ring
  · dsimp [likelihoodWeight]
    congr 1
    · congr 1
      ring
    · ring

theorem continuous_joint_likelihoodWeight (N k : ℕ) (lam : ℝ) :
    Continuous (fun z : Model.Vector N × Model.Tensor N k ↦ likelihoodWeight N k lam z.2 z.1) := by
  have hc : Continuous (fun z : Model.Vector N × Model.Tensor N k ↦ Model.score z.2 z.1) :=
    ((Model.continuous_feature N k).comp continuous_fst).inner continuous_snd
  exact Real.continuous_exp.comp ((continuous_const.mul hc).sub continuous_const)

/-- The translated noise likelihood has the manuscript's constant correction
precisely when the planted feature has unit norm. -/
theorem noiseLaw_map_observation {N k : ℕ} (lam : ℝ) (x : Model.Vector N) (hx : ‖x‖ = 1) :
    (Model.noiseLaw N k).map (fun w ↦ Model.observation lam (x, w)) =
      (Model.noiseLaw N k).withDensity
        (fun y ↦ ENNReal.ofReal (likelihoodWeight N k lam y x)) := by
  have hfeature := Geometry.feature_unit_norm (k := k) x hx
  change (stdGaussian (Model.Tensor N k)).map
      (fun w ↦ (lam * Real.sqrt N) • Model.feature k x + w) =
    (stdGaussian (Model.Tensor N k)).withDensity
      (fun y ↦ ENNReal.ofReal (likelihoodWeight N k lam y x))
  rw [stdGaussian_map_add_eq_withDensity]
  congr 1
  funext y
  dsimp [likelihoodWeight, Model.score]
  congr 2
  rw [real_inner_smul_left, norm_smul, hfeature, mul_one]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

theorem measurable_likelihoodRatio (N k : ℕ) (lam : ℝ) :
    Measurable (Model.likelihoodRatio N k lam) := by
  have hm : StronglyMeasurable (fun z : Model.Tensor N k × Model.Vector N ↦
      likelihoodWeight N k lam z.1 z.2) :=
    ((continuous_joint_likelihoodWeight N k lam).comp continuous_swap).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := Model.spherePrior N)).measurable

/-- The actual joint planted vector and observed tensor law has the exact
Gaussian likelihood weight relative to the unplanted product law. -/
theorem jointObservation_map_eq_withDensity {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (Model.experimentLaw N k).map (fun z ↦ (z.1, Model.observation lam z)) =
      (Model.experimentLaw N k).withDensity
        (fun z ↦ ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1)) := by
  have hObs : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      (z.1, Model.observation lam z)) := measurable_fst.prodMk (Model.measurable_observation N k lam)
  have hWeight : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1)) :=
    (continuous_joint_likelihoodWeight N k lam).measurable.ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hObs, lintegral_withDensity_eq_lintegral_mul _ hWeight hg]
  change (∫⁻ z, g (z.1, Model.observation lam z)
      ∂(Model.spherePrior N).prod (Model.noiseLaw N k)) =
    ∫⁻ z, ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1) * g z
      ∂(Model.spherePrior N).prod (Model.noiseLaw N k)
  rw [lintegral_prod
      (fun z : Model.Vector N × Model.Tensor N k ↦ g (z.1, Model.observation lam z))
      (hg.comp hObs).aemeasurable,
    lintegral_prod (fun z : Model.Vector N × Model.Tensor N k ↦
      ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1) * g z) (hWeight.mul hg).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
  have hFix : Measurable (fun w : Model.Tensor N k ↦ Model.observation lam (x, w)) :=
    (Model.measurable_observation N k lam).comp (measurable_const.prodMk measurable_id)
  have hgFix : Measurable (fun y : Model.Tensor N k ↦ g (x, y)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ y, g (x, y) ∂(Model.noiseLaw N k).map (fun w ↦ Model.observation lam (x, w)) :=
      (lintegral_map hgFix hFix).symm
    _ = ∫⁻ y, g (x, y) ∂(Model.noiseLaw N k).withDensity
        (fun y ↦ ENNReal.ofReal (likelihoodWeight N k lam y x)) := by
      rw [noiseLaw_map_observation lam x hx]
    _ = _ := lintegral_withDensity_eq_lintegral_mul _
      (hWeight.comp (measurable_const.prodMk measurable_id)) hgFix

/-- The manuscript's actual likelihood ratio is the density of its actual
observation law relative to standard Gaussian noise. -/
theorem observationLaw_eq_withDensity {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Model.observationLaw N k lam = (Model.noiseLaw N k).withDensity
      (fun y ↦ ENNReal.ofReal (Model.likelihoodRatio N k lam y)) := by
  have hObs : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      (z.1, Model.observation lam z)) := measurable_fst.prodMk (Model.measurable_observation N k lam)
  have hWeight : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1)) :=
    (continuous_joint_likelihoodWeight N k lam).measurable.ennreal_ofReal
  have hMap : Model.observationLaw N k lam =
      ((Model.experimentLaw N k).map (fun z ↦ (z.1, Model.observation lam z))).map Prod.snd := by
    rw [Measure.map_map measurable_snd hObs]
    rfl
  apply Measure.ext_of_lintegral
  intro g hg
  rw [hMap, jointObservation_map_eq_withDensity hN lam, lintegral_map hg measurable_snd,
    lintegral_withDensity_eq_lintegral_mul
      (g := fun z : Model.Vector N × Model.Tensor N k ↦ g z.2) _ hWeight (hg.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_likelihoodRatio N k lam).ennreal_ofReal hg]
  change (∫⁻ z, ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1) * g z.2
      ∂(Model.spherePrior N).prod (Model.noiseLaw N k)) = _
  rw [lintegral_prod_symm (fun z : Model.Vector N × Model.Tensor N k ↦
    ENNReal.ofReal (likelihoodWeight N k lam z.2 z.1) * g z.2)
      (hWeight.mul (hg.comp measurable_snd)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with y
  rw [lintegral_mul_const (g y) (continuous_likelihoodWeight N k lam y).measurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_likelihoodWeight hN lam y)
      (Filter.Eventually.of_forall fun x ↦ (likelihoodWeight_pos N k lam y x).le)]
  rfl

theorem lintegral_likelihoodRatio_eq_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Model.likelihoodRatio N k lam y) ∂Model.noiseLaw N k) = 1 := by
  calc
    _ = ((Model.noiseLaw N k).withDensity
        (fun y ↦ ENNReal.ofReal (Model.likelihoodRatio N k lam y))) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = (Model.observationLaw N k lam) Set.univ :=
      congrArg (fun μ : Measure (Model.Tensor N k) ↦ μ Set.univ)
        (observationLaw_eq_withDensity hN lam).symm
    _ = 1 := measure_univ

theorem integrable_likelihoodRatio {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (Model.likelihoodRatio N k lam) (Model.noiseLaw N k) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_likelihoodRatio N k lam).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ (likelihoodRatio_pos hN lam y).le)).mp
  rw [lintegral_likelihoodRatio_eq_one hN lam]
  exact ENNReal.one_ne_top

theorem integral_likelihoodRatio_eq_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ y, Model.likelihoodRatio N k lam y ∂Model.noiseLaw N k) = 1 := by
  apply ENNReal.ofReal_eq_one.mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_likelihoodRatio hN lam)
      (Filter.Eventually.of_forall fun y ↦ (likelihoodRatio_pos hN lam y).le),
    lintegral_likelihoodRatio_eq_one hN lam]


end TensorPCA.GaussianChannelProofs
