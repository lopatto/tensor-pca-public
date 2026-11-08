-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PosteriorDensityProofs
public import TensorPCA.GaussianSpinInterpolationProofs
public import TensorPCA.Statistical

/-!
# Finite spherical Gaussian-channel calculus

The shared bounded Gibbs calculus is specialized to the tensor feature.
The physical normalization is N; the Gaussian coefficient space has N^k ordered
coordinates. These dimensions are kept distinct throughout.
-/
@[expose] public section

namespace TensorPCA.FiniteIMMSEProofs

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable def featureField (N k : ℕ) (x : Model.Vector N) : Model.Tensor N k →L[ℝ] ℝ :=
  innerSL ℝ (Model.feature k x)

theorem continuous_featureField (N k : ℕ) : Continuous (featureField N k) := by
  unfold featureField
  exact (innerSL ℝ).continuous.comp (Model.continuous_feature N k)

theorem featureField_apply {N k : ℕ} (x : Model.Vector N) (y : Model.Tensor N k) :
    featureField N k x y = Model.score y x := rfl

theorem featureField_norm_le_ae {N k : ℕ} (hN : 0 < N) :
    ∀ᵐ x ∂Model.spherePrior N, ‖featureField N k x‖ ≤ 1 := by
  filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
  simp only [featureField, innerSL_apply_norm, Geometry.feature_unit_norm (k := k) x hx, le_refl]

theorem likelihoodRatio_eq_baseMoment (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) :
    Model.likelihoodRatio N k lam y = Real.exp (-(N : ℝ) * lam ^ 2 / 2) *
      GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ ↦ 1) (featureField N k)
        ((lam * Real.sqrt N) • y) := by
  rw [GaussianChannelProofs.likelihoodRatio_eq_integral_weight]
  simp only [GaussianSpinInterpolation.moment, GaussianSpinInterpolation.weight, one_mul,
    featureField, innerSL_apply_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  unfold GaussianChannelProofs.likelihoodWeight
  rw [← Real.exp_add]
  congr 1
  simp only [real_inner_smul_right, Model.score]
  ring

theorem log_likelihoodRatio_eq_basePartition {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) :
    Real.log (Model.likelihoodRatio N k lam y) = -(N : ℝ) * lam ^ 2 / 2 +
      GaussianSpinInterpolation.logPartition (Model.spherePrior N) (featureField N k)
        ((lam * Real.sqrt N) • y) := by
  have hz := GaussianSpinInterpolation.moment_one_pos (Model.spherePrior N) (featureField N k)
    (continuous_featureField N k).measurable (featureField_norm_le_ae hN) ((lam * Real.sqrt N) • y)
  rw [likelihoodRatio_eq_baseMoment, Real.log_mul (Real.exp_ne_zero _) hz.ne', Real.log_exp]
  rfl

theorem scaled_observation_eq {N k : ℕ} (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) :
    (lam * Real.sqrt N) • Model.observation lam z =
      ((N : ℝ) * lam ^ 2) • Model.feature k z.1 + (lam * Real.sqrt N) • z.2 := by
  simp only [Model.observation, smul_add, smul_smul]
  rw [show (lam * Real.sqrt N) * (lam * Real.sqrt N) = (N : ℝ) * lam ^ 2 by
    calc
      _ = lam ^ 2 * (Real.sqrt N) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring]

theorem hasDerivAt_scaled_observation {N k : ℕ} (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) :
    HasDerivAt (fun t ↦ (t * Real.sqrt N) • Model.observation t z)
      ((2 * (N : ℝ) * lam) • Model.feature k z.1 + Real.sqrt N • z.2) lam := by
  simp_rw [scaled_observation_eq]
  have hq := ((hasDerivAt_pow 2 lam).const_mul (N : ℝ)).smul_const (Model.feature k z.1)
  have hl := ((hasDerivAt_id lam).mul_const (Real.sqrt N)).smul_const z.2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hq.fun_add hl

/-- Exact derivative along the actual planted observation path. The quadratic
signal contribution and the likelihood normalizer are both differentiated. -/
theorem hasDerivAt_planted_logLikelihood {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) :
    HasDerivAt (fun t ↦ Real.log (Model.likelihoodRatio N k t (Model.observation t z)))
      (GaussianSpinInterpolation.score (Model.spherePrior N) (featureField N k)
          ((lam * Real.sqrt N) • Model.observation lam z)
          ((2 * (N : ℝ) * lam) • Model.feature k z.1 + Real.sqrt N • z.2) - (N : ℝ) * lam) lam := by
  have hp := (GaussianSpinInterpolation.logPartition_hasFDerivAt (Model.spherePrior N)
    (featureField N k) (continuous_featureField N k).measurable zero_le_one
    (featureField_norm_le_ae hN) ((lam * Real.sqrt N) • Model.observation lam z)).comp_hasDerivAt
      lam (hasDerivAt_scaled_observation lam z)
  have hq := ((hasDerivAt_pow 2 lam).const_mul (N : ℝ)).div_const 2
  convert hp.sub hq using 1
  · funext t
    rw [log_likelihoodRatio_eq_basePartition hN t (Model.observation t z)]
    simp only [Pi.sub_apply, Function.comp_apply]
    ring
  · simp
    ring

noncomputable def plantedLogDerivative (N k : ℕ) (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) : ℝ :=
  GaussianSpinInterpolation.score (Model.spherePrior N) (featureField N k)
    ((lam * Real.sqrt N) • Model.observation lam z)
    ((2 * (N : ℝ) * lam) • Model.feature k z.1 + Real.sqrt N • z.2) - (N : ℝ) * lam

theorem continuous_scaled_observation (N k : ℕ) (lam : ℝ) :
    Continuous (fun z : Model.Vector N × Model.Tensor N k ↦
      (lam * Real.sqrt N) • Model.observation lam z) := by
  simp_rw [scaled_observation_eq]
  exact (((Model.continuous_feature N k).comp continuous_fst).const_smul ((N : ℝ) * lam ^ 2)).add
    (continuous_snd.const_smul (lam * Real.sqrt N))

theorem continuous_planted_logLikelihood {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Continuous (fun z : Model.Vector N × Model.Tensor N k ↦
      Real.log (Model.likelihoodRatio N k lam (Model.observation lam z))) := by
  simp_rw [log_likelihoodRatio_eq_basePartition hN]
  exact continuous_const.add
    ((GaussianSpinInterpolation.logPartition_contDiff (Model.spherePrior N)
      (featureField N k) (continuous_featureField N k).measurable zero_le_one
      (featureField_norm_le_ae hN)).continuous.comp (continuous_scaled_observation N k lam))

theorem continuous_plantedLogDerivative {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Continuous (plantedLogDerivative N k lam) := by
  have hc := GaussianSpinInterpolation.score_continuous (Model.spherePrior N)
    (featureField N k) (continuous_featureField N k).measurable zero_le_one
    (featureField_norm_le_ae hN)
  exact ((hc.comp (continuous_scaled_observation N k lam)).clm_apply
    ((((Model.continuous_feature N k).comp continuous_fst).const_smul (2 * (N : ℝ) * lam)).add
      (continuous_snd.const_smul (Real.sqrt N)))).sub continuous_const

theorem integrable_noise_norm (N k : ℕ) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦ ‖z.2‖)
      (Model.experimentLaw N k) := by
  have hn := GaussianSpinInterpolation.gaussian_norm_integrable (ι := Fin k → Fin N)
  rw [GaussianConcentrationBridge.standardGaussianMeasure_bridge] at hn
  exact hn.comp_snd (Model.spherePrior N)

theorem norm_scaled_observation_le {N k : ℕ} (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) (hz : ‖Model.feature k z.1‖ = 1) :
    ‖(lam * Real.sqrt N) • Model.observation lam z‖ ≤
      (N : ℝ) * lam ^ 2 + |lam * Real.sqrt N| * ‖z.2‖ := by
  rw [scaled_observation_eq]
  calc
    _ ≤ ‖((N : ℝ) * lam ^ 2) • Model.feature k z.1‖ +
        ‖(lam * Real.sqrt N) • z.2‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul, hz]

theorem integrable_planted_logLikelihood {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦
      Real.log (Model.likelihoodRatio N k lam (Model.observation lam z)))
      (Model.experimentLaw N k) := by
  apply ((integrable_const ((N : ℝ) * lam ^ 2 / 2 + (N : ℝ) * lam ^ 2)).add
    ((integrable_noise_norm N k).const_mul |lam * Real.sqrt N|)).mono'
      (continuous_planted_logLikelihood hN lam).aestronglyMeasurable
  filter_upwards [PosteriorProofs.latent_norm_ae hN] with z hz
  rw [Real.norm_eq_abs, log_likelihoodRatio_eq_basePartition hN]
  calc
    _ ≤ |-(N : ℝ) * lam ^ 2 / 2| +
        |GaussianSpinInterpolation.logPartition (Model.spherePrior N) (featureField N k)
          ((lam * Real.sqrt N) • Model.observation lam z)| := abs_add_le _ _
    _ ≤ (N : ℝ) * lam ^ 2 / 2 + ‖(lam * Real.sqrt N) • Model.observation lam z‖ := by
      have hb := GaussianSpinInterpolation.abs_logPartition_le (Model.spherePrior N)
        (featureField N k) (continuous_featureField N k).measurable
        (featureField_norm_le_ae hN) ((lam * Real.sqrt N) • Model.observation lam z)
      have hq : 0 ≤ (N : ℝ) * lam ^ 2 / 2 := by positivity
      rw [neg_mul, neg_div, abs_neg, abs_of_nonneg hq]
      exact add_le_add le_rfl (by simpa only [one_mul] using hb)
    _ ≤ _ := by
      have hb := norm_scaled_observation_le lam z hz
      dsimp
      linarith

theorem norm_plantedLogDerivative_le {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) (hz : ‖Model.feature k z.1‖ = 1) :
    ‖plantedLogDerivative N k lam z‖ ≤
      3 * (N : ℝ) * |lam| + Real.sqrt N * ‖z.2‖ := by
  have hs := GaussianSpinInterpolation.norm_score_le (Model.spherePrior N)
    (featureField N k) (continuous_featureField N k).measurable zero_le_one
    (featureField_norm_le_ae hN) ((lam * Real.sqrt N) • Model.observation lam z)
  unfold plantedLogDerivative
  calc
    _ ≤ ‖GaussianSpinInterpolation.score (Model.spherePrior N) (featureField N k)
        ((lam * Real.sqrt N) • Model.observation lam z)
        ((2 * (N : ℝ) * lam) • Model.feature k z.1 + Real.sqrt N • z.2)‖ + ‖(N : ℝ) * lam‖ :=
      norm_sub_le _ _
    _ ≤ ‖(2 * (N : ℝ) * lam) • Model.feature k z.1 + Real.sqrt N • z.2‖ + ‖(N : ℝ) * lam‖ := by
      apply add_le_add _ le_rfl
      exact ((GaussianSpinInterpolation.score (Model.spherePrior N) (featureField N k)
        ((lam * Real.sqrt N) • Model.observation lam z)).le_opNorm _).trans
        (by simpa using mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    _ ≤ ‖(2 * (N : ℝ) * lam) • Model.feature k z.1‖ + ‖Real.sqrt N • z.2‖ + ‖(N : ℝ) * lam‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by
      simp only [norm_smul, hz, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N), abs_of_nonneg (Real.sqrt_nonneg N), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring

/-- Differentiation under the actual product experiment law is justified by a
single integrable Gaussian norm bound, uniform on a neighborhood of λ. -/
theorem hasDerivAt_integral_planted_logLikelihood {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    HasDerivAt (fun t ↦ ∫ z, Real.log (Model.likelihoodRatio N k t (Model.observation t z))
      ∂Model.experimentLaw N k)
      (∫ z, plantedLogDerivative N k lam z ∂Model.experimentLaw N k) lam := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Model.experimentLaw N k) (s := Metric.ball lam 1)
    (F' := plantedLogDerivative N k)
    (bound := fun z ↦ 3 * (N : ℝ) * (|lam| + 1) + Real.sqrt N * ‖z.2‖)
    (Metric.ball_mem_nhds lam zero_lt_one)
    (.of_forall fun t ↦ (continuous_planted_logLikelihood hN t).aestronglyMeasurable)
    (integrable_planted_logLikelihood hN lam)
    (continuous_plantedLogDerivative hN lam).aestronglyMeasurable ?_
    ((integrable_const _).add ((integrable_noise_norm N k).const_mul (Real.sqrt N)))
    (.of_forall fun z t _ ↦ hasDerivAt_planted_logLikelihood hN t z)).2
  filter_upwards [PosteriorProofs.latent_norm_ae hN] with z hz t ht
  apply (norm_plantedLogDerivative_le hN t z hz).trans
  have ht' := GaussianSpinInterpolation.norm_le_of_mem_ball ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht'
  exact add_le_add (mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ 3 * (N : ℝ))) le_rfl

theorem integrable_baseTensor_integrand {N k : ℕ} (hN : 0 < N) (w : Model.Tensor N k) :
    Integrable (fun x ↦ Real.exp (featureField N k x w) • Model.feature k x)
      (Model.spherePrior N) := by
  have hc : Continuous (fun x ↦ Real.exp (featureField N k x w) • Model.feature k x) :=
    (Real.continuous_exp.comp ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (continuous_featureField N k))).smul (Model.continuous_feature N k)
  apply (integrable_const (Real.exp ‖w‖)).mono' hc.aestronglyMeasurable
  filter_upwards [Geometry.spherePrior_norm_ae hN, featureField_norm_le_ae (k := k) hN] with x hx hL
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (featureField N k x w)),
    Geometry.feature_unit_norm (k := k) x hx, mul_one]
  apply Real.exp_le_exp.mpr
  have hh := ((featureField N k x).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg w))
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, one_mul] using hh)

theorem momentDerivative_eq_innerSL {N k : ℕ} (hN : 0 < N) (w : Model.Tensor N k) :
    GaussianSpinInterpolation.momentDerivative (Model.spherePrior N) (fun _ ↦ 1)
      (featureField N k) w = innerSL ℝ
        (∫ x, Real.exp (featureField N k x w) • Model.feature k x ∂Model.spherePrior N) := by
  rw [← (innerSL ℝ).integral_comp_comm (integrable_baseTensor_integrand hN w)]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simp only [GaussianSpinInterpolation.weightDerivative, GaussianSpinInterpolation.weight,
      one_mul, map_smul, featureField]

theorem gibbsTensorNumerator_eq_base {N k : ℕ} (lam : ℝ) (y : Model.Tensor N k) :
    PosteriorDensityProofs.gibbsTensorNumerator N k lam y = Real.exp (-(N : ℝ) * lam ^ 2 / 2) •
      (∫ x, Real.exp (featureField N k x ((lam * Real.sqrt N) • y)) • Model.feature k x
        ∂Model.spherePrior N) := by
  rw [← integral_smul]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    dsimp only
    rw [smul_smul, ← Real.exp_add]
    congr 1
    simp only [GaussianChannelProofs.likelihoodWeight, featureField, innerSL_apply_apply,
      real_inner_smul_right, Model.score]
    congr 1
    ring

/-- The shared Gibbs score is exactly the Riesz functional of the concrete
posterior mean, including its likelihood normalization. -/
theorem score_eq_innerSL_gibbsTensorMean {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) :
    GaussianSpinInterpolation.score (Model.spherePrior N) (featureField N k)
      ((lam * Real.sqrt N) • y) = innerSL ℝ (PosteriorDensityProofs.gibbsTensorMean N k lam y) := by
  rw [GaussianSpinInterpolation.score, momentDerivative_eq_innerSL hN,
    PosteriorDensityProofs.gibbsTensorMean, gibbsTensorNumerator_eq_base,
    likelihoodRatio_eq_baseMoment, smul_smul, map_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _), mul_one]

theorem score_apply_eq_expectation {N k : ℕ} (hN : 0 < N) (w d : Model.Tensor N k) :
    GaussianSpinInterpolation.score (Model.spherePrior N) (featureField N k) w d =
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ featureField N k x d) (featureField N k) w := by
  have hb : ∀ᵐ x ∂Model.spherePrior N, |(1 : ℝ)| ≤ 1 ∧ ‖featureField N k x‖ ≤ 1 :=
    (featureField_norm_le_ae hN).mono fun x hx ↦ ⟨by norm_num, hx⟩
  rw [GaussianSpinInterpolation.score, smul_apply,
    GaussianSpinInterpolation.momentDerivative_apply (Model.spherePrior N) (fun _ ↦ 1)
      (featureField N k) measurable_const (continuous_featureField N k).measurable hb]
  simp only [one_mul, smul_eq_mul, GaussianSpinInterpolation.expectation, div_eq_mul_inv, mul_comm]

/-- Gaussian integration by parts for a bounded spin observable evaluated on
an arbitrary affine Gaussian input. The gradient bound is proved from Gibbs
covariance; it is not an extra assumption on the channel. -/
theorem gaussian_affine_expectation_ibp {N k : ℕ} (hN : 0 < N)
    (rho : Model.Vector N → ℝ) (hrho : Measurable rho) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂Model.spherePrior N, |rho x| ≤ C)
    (b d : Model.Tensor N k) (s : ℝ) :
    (∫ w, inner ℝ d w * GaussianSpinInterpolation.expectation (Model.spherePrior N) rho
        (featureField N k) (b + s • w) ∂Model.noiseLaw N k) =
      ∫ w, s * GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N) rho
        (featureField N k) (b + s • w) d ∂Model.noiseLaw N k := by
  have hbound : ∀ᵐ x ∂Model.spherePrior N, |rho x| ≤ C ∧ ‖featureField N k x‖ ≤ 1 :=
    hb.and (featureField_norm_le_ae hN)
  let g : Model.Tensor N k → ℝ := fun w ↦ GaussianSpinInterpolation.expectation
    (Model.spherePrior N) rho (featureField N k) (b + s • w)
  have hg : ContDiff ℝ 1 g :=
    (GaussianSpinInterpolation.expectation_contDiff (Model.spherePrior N) rho (featureField N k)
      hrho (continuous_featureField N k).measurable hC zero_le_one hbound).comp
      (contDiff_const.add (contDiff_id.const_smul s))
  have hd (w : Model.Tensor N k) : HasFDerivAt g
      (s • GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N) rho
        (featureField N k) (b + s • w)) w := by
    have he := GaussianSpinInterpolation.expectation_hasFDerivAt (Model.spherePrior N) rho
      (featureField N k) hrho (continuous_featureField N k).measurable hC zero_le_one hbound
      (b + s • w)
    convert he.comp w (((hasFDerivAt_id w).const_smul s).const_add b) using 1
    · rfl
    · ext v
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]
  have hgrad (w : Model.Tensor N k) : ‖gradient g w‖ ≤ |s| * (2 * C) := by
    rw [gradient, (hd w).fderiv, (InnerProductSpace.toDual ℝ (Model.Tensor N k)).symm.norm_map,
      norm_smul, Real.norm_eq_abs]
    have he := GaussianSpinInterpolation.norm_expectationDerivative_le (Model.spherePrior N) rho
      (featureField N k) hrho (continuous_featureField N k).measurable hC zero_le_one hbound
      (b + s • w)
    exact mul_le_mul_of_nonneg_left (by simpa only [mul_one] using he) (abs_nonneg s)
  have hi := SYK.gaussian_ibp g d hg (max C (|s| * (2 * C))) 0
    (fun w ↦ by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact (GaussianSpinInterpolation.norm_expectation_le (Model.spherePrior N) rho
        (featureField N k) hrho (continuous_featureField N k).measurable hC hbound
        (b + s • w)).trans (le_max_left _ _))
    (fun w ↦ by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact (hgrad w).trans (le_max_right _ _))
  rw [GaussianConcentrationBridge.standardGaussianMeasure_bridge] at hi
  change (∫ w, inner ℝ d w * g w ∂stdGaussian (Model.Tensor N k)) = _
  rw [hi]
  apply integral_congr_ae
  exact .of_forall fun w ↦ by
    change inner ℝ d (gradient g w) = _
    rw [real_inner_comm, gradient, (hd w).fderiv, InnerProductSpace.toDual_symm_apply, smul_apply,
      smul_eq_mul]


end TensorPCA.FiniteIMMSEProofs
