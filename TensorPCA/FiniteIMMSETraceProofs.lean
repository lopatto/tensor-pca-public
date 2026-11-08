-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteIMMSEProofs
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Finite Gaussian-channel covariance trace

The coordinate trace uses the ordered tensor coordinates. The unit norm
of the planted feature reduces the first Gibbs second moment exactly to one.
-/
@[expose] public section

namespace TensorPCA.FiniteIMMSETraceProofs

open MeasureTheory ProbabilityTheory FiniteIMMSEProofs
open scoped ENNReal RealInnerProductSpace

noncomputable def coordinateObservable (N k : ℕ) (i : Fin k → Fin N) (x : Model.Vector N) : ℝ :=
  featureField N k x (EuclideanSpace.single i 1)

theorem continuous_coordinateObservable (N k : ℕ) (i : Fin k → Fin N) :
    Continuous (coordinateObservable N k i) :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.comp
    (continuous_featureField N k)

theorem coordinateObservable_abs_le_ae {N k : ℕ} (hN : 0 < N) (i : Fin k → Fin N) :
    ∀ᵐ x ∂Model.spherePrior N, |coordinateObservable N k i x| ≤ 1 := by
  filter_upwards [featureField_norm_le_ae (k := k) hN] with x hx
  have hh := (featureField N k x).le_opNorm (EuclideanSpace.single i 1)
  have he : ‖(EuclideanSpace.single i 1 : Model.Tensor N k)‖ = 1 := by simp
  rw [Real.norm_eq_abs, he, mul_one] at hh
  exact hh.trans hx

theorem sum_coordinateObservable_sq {N k : ℕ} (x : Model.Vector N) :
    ∑ i : Fin k → Fin N, coordinateObservable N k i x ^ 2 = ‖Model.feature k x‖ ^ 2 := by
  classical
  simpa only [coordinateObservable, featureField, innerSL_apply_apply,
    EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin k → Fin N) ℝ).sum_sq_inner_left (Model.feature k x)

theorem sum_expectation_coordinate_sq {N k : ℕ} (hN : 0 < N) (w : Model.Tensor N k) :
    ∑ i : Fin k → Fin N, GaussianSpinInterpolation.expectation (Model.spherePrior N)
      (fun x ↦ coordinateObservable N k i x ^ 2) (featureField N k) w = 1 := by
  classical
  let mu := GaussianSpinInterpolation.gibbsMeasure (Model.spherePrior N) (featureField N k) w
  have hAC : mu ≪ Model.spherePrior N :=
    GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous _ _ _
  have : IsProbabilityMeasure mu := GaussianSpinInterpolation.gibbsMeasure_probability
    (Model.spherePrior N) (featureField N k) (continuous_featureField N k).measurable
    (featureField_norm_le_ae hN) w
  have hi (i : Fin k → Fin N) : Integrable (fun x ↦ coordinateObservable N k i x ^ 2) mu := by
    apply (integrable_const (1 : ℝ)).mono'
      ((continuous_coordinateObservable N k i).pow 2).aestronglyMeasurable
    filter_upwards [(coordinateObservable_abs_le_ae hN i).filter_mono hAC.ae_le] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change coordinateObservable N k i x ^ 2 ≤ 1
    nlinarith [abs_nonneg (coordinateObservable N k i x), sq_abs (coordinateObservable N k i x)]
  simp_rw [← GaussianSpinInterpolation.integral_gibbsMeasure (Model.spherePrior N)
    (featureField N k) (continuous_featureField N k).measurable (featureField_norm_le_ae hN) w]
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
  calc
    _ = ∫ x, (1 : ℝ) ∂mu := by
      apply integral_congr_ae
      filter_upwards [(Geometry.spherePrior_norm_ae hN).filter_mono hAC.ae_le] with x hx
      simp only [sum_coordinateObservable_sq,
        Geometry.feature_unit_norm (k := k) x hx, one_pow]
    _ = 1 := by simp

theorem expectation_coordinate_eq_inner_mean {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) (i : Fin k → Fin N) :
    GaussianSpinInterpolation.expectation (Model.spherePrior N) (coordinateObservable N k i)
      (featureField N k) ((lam * Real.sqrt N) • y) =
      inner ℝ (PosteriorDensityProofs.gibbsTensorMean N k lam y) (EuclideanSpace.single i 1) := by
  unfold coordinateObservable
  rw [← score_apply_eq_expectation hN, score_eq_innerSL_gibbsTensorMean hN]
  rfl

theorem sum_expectationDerivative_coordinate {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) :
    ∑ i : Fin k → Fin N, GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k) ((lam * Real.sqrt N) • y)
      (EuclideanSpace.single i 1) = 1 - ‖PosteriorDensityProofs.gibbsTensorMean N k lam y‖ ^ 2 := by
  classical
  have he (i : Fin k → Fin N) :
      GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N)
        (coordinateObservable N k i) (featureField N k) ((lam * Real.sqrt N) • y)
        (EuclideanSpace.single i 1) =
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ coordinateObservable N k i x ^ 2) (featureField N k) ((lam * Real.sqrt N) • y) -
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (coordinateObservable N k i) (featureField N k) ((lam * Real.sqrt N) • y) ^ 2 := by
    have hh := GaussianSpinInterpolation.expectationDerivative_apply
        (Model.spherePrior N) (coordinateObservable N k i) (featureField N k)
        (continuous_coordinateObservable N k i).measurable (continuous_featureField N k).measurable
        ((coordinateObservable_abs_le_ae hN i).and (featureField_norm_le_ae hN))
        ((lam * Real.sqrt N) • y) (EuclideanSpace.single i 1)
    unfold coordinateObservable at hh ⊢
    simpa only [pow_two] using hh
  simp_rw [he]
  rw [Finset.sum_sub_distrib, sum_expectation_coordinate_sq hN]
  congr 1
  simp_rw [expectation_coordinate_eq_inner_mean hN]
  simpa only [EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin k → Fin N) ℝ).sum_sq_inner_left
      (PosteriorDensityProofs.gibbsTensorMean N k lam y)

theorem continuous_coordinate_expectationDerivative {N k : ℕ} (hN : 0 < N)
    (i : Fin k → Fin N) :
    Continuous (GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k)) := by
  have hb := (coordinateObservable_abs_le_ae hN i).and (featureField_norm_le_ae (k := k) hN)
  convert (GaussianSpinInterpolation.expectation_contDiff (Model.spherePrior N)
    (coordinateObservable N k i) (featureField N k) (continuous_coordinateObservable N k i).measurable
    (continuous_featureField N k).measurable zero_le_one zero_le_one hb).continuous_fderiv
      (by norm_num) using 1
  funext w
  exact (GaussianSpinInterpolation.expectation_hasFDerivAt (Model.spherePrior N)
    (coordinateObservable N k i) (featureField N k) (continuous_coordinateObservable N k i).measurable
    (continuous_featureField N k).measurable zero_le_one zero_le_one hb w).fderiv.symm

theorem integrable_gaussian_coordinate_response {N k : ℕ} (hN : 0 < N)
    (b : Model.Tensor N k) (s : ℝ) (i : Fin k → Fin N) :
    Integrable (fun w ↦ w i * GaussianSpinInterpolation.expectation (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k) (b + s • w)) (Model.noiseLaw N k) := by
  have hb := (coordinateObservable_abs_le_ae hN i).and (featureField_norm_le_ae (k := k) hN)
  have hc : Continuous (fun w : Model.Tensor N k ↦ w i *
      GaussianSpinInterpolation.expectation (Model.spherePrior N) (coordinateObservable N k i)
        (featureField N k) (b + s • w)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin k → Fin N ↦ ℝ) i).mul
    ((GaussianSpinInterpolation.expectation_contDiff (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k) (continuous_coordinateObservable N k i).measurable
      (continuous_featureField N k).measurable zero_le_one zero_le_one hb).continuous.comp
      (continuous_const.add (continuous_id.const_smul s)))
  have hn := GaussianSpinInterpolation.gaussian_norm_integrable (ι := Fin k → Fin N)
  rw [GaussianConcentrationBridge.standardGaussianMeasure_bridge] at hn
  apply hn.mono' hc.aestronglyMeasurable
  exact .of_forall fun w ↦ by
    rw [norm_mul]
    have he := GaussianSpinInterpolation.norm_expectation_le (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k) (continuous_coordinateObservable N k i).measurable
      (continuous_featureField N k).measurable zero_le_one hb (b + s • w)
    simpa only [mul_one] using mul_le_mul (PiLp.norm_apply_le w i) he (norm_nonneg _) (norm_nonneg _)

theorem integrable_gaussian_coordinate_derivative {N k : ℕ} (hN : 0 < N)
    (b : Model.Tensor N k) (s : ℝ) (i : Fin k → Fin N) :
    Integrable (fun w ↦ GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k) (b + s • w) (EuclideanSpace.single i 1))
      (Model.noiseLaw N k) := by
  have hc : Continuous (fun w : Model.Tensor N k ↦
      GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N)
        (coordinateObservable N k i) (featureField N k) (b + s • w) (EuclideanSpace.single i 1)) :=
    ((continuous_coordinate_expectationDerivative hN i).comp
    (continuous_const.add (continuous_id.const_smul s))).clm_apply continuous_const
  apply (integrable_const (2 : ℝ)).mono' hc.aestronglyMeasurable
  exact .of_forall fun w ↦ by
    have hh := (GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N)
      (coordinateObservable N k i) (featureField N k) (b + s • w)).le_opNorm (EuclideanSpace.single i 1)
    have he : ‖(EuclideanSpace.single i 1 : Model.Tensor N k)‖ = 1 := by simp
    rw [he, mul_one] at hh
    have hbound := GaussianSpinInterpolation.norm_expectationDerivative_le
      (Model.spherePrior N) (coordinateObservable N k i) (featureField N k)
      (continuous_coordinateObservable N k i).measurable (continuous_featureField N k).measurable
      zero_le_one zero_le_one
      ((coordinateObservable_abs_le_ae hN i).and (featureField_norm_le_ae hN)) (b + s • w)
    exact hh.trans (by simpa using hbound)

/-- The finite Gaussian score identity at any planted vector, before averaging
over that vector. The spin prior in the posterior remains the actual sphere law. -/
theorem integral_noise_inner_mean {N k : ℕ} (hN : 0 < N) (lam : ℝ) (x : Model.Vector N) :
    (∫ w, inner ℝ (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam (x, w))) w
      ∂Model.noiseLaw N k) =
    (lam * Real.sqrt N) * ∫ w,
      (1 - ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam (x, w))‖ ^ 2)
      ∂Model.noiseLaw N k := by
  classical
  let s := lam * Real.sqrt N
  let b := ((N : ℝ) * lam ^ 2) • Model.feature k x
  have harg (w : Model.Tensor N k) :
      s • Model.observation lam (x, w) = b + s • w := scaled_observation_eq lam (x, w)
  have hi (i : Fin k → Fin N) : Integrable (fun w ↦ w i *
      GaussianSpinInterpolation.expectation (Model.spherePrior N) (coordinateObservable N k i)
        (featureField N k) (s • Model.observation lam (x, w))) (Model.noiseLaw N k) := by
    simp_rw [harg]
    exact integrable_gaussian_coordinate_response hN b s i
  have hd (i : Fin k → Fin N) : Integrable (fun w ↦ s *
      GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N) (coordinateObservable N k i)
        (featureField N k) (s • Model.observation lam (x, w)) (EuclideanSpace.single i 1))
        (Model.noiseLaw N k) := by
    simp_rw [harg]
    exact (integrable_gaussian_coordinate_derivative hN b s i).const_mul s
  calc
    _ = ∫ w, ∑ i : Fin k → Fin N, w i *
        GaussianSpinInterpolation.expectation (Model.spherePrior N) (coordinateObservable N k i)
          (featureField N k) (s • Model.observation lam (x, w)) ∂Model.noiseLaw N k := by
      apply integral_congr_ae
      exact .of_forall fun w ↦ by
        dsimp only
        rw [← innerSL_apply_apply, ← score_eq_innerSL_gibbsTensorMean hN]
        exact GaussianSpinInterpolation.score_eq_coordinate_sum (Model.spherePrior N)
          (featureField N k) (continuous_featureField N k).measurable (featureField_norm_le_ae hN)
          (s • Model.observation lam (x, w)) w
    _ = ∑ i : Fin k → Fin N, ∫ w, w i *
        GaussianSpinInterpolation.expectation (Model.spherePrior N) (coordinateObservable N k i)
          (featureField N k) (s • Model.observation lam (x, w)) ∂Model.noiseLaw N k :=
      integral_finsetSum Finset.univ (fun i _ ↦ hi i)
    _ = ∑ i : Fin k → Fin N, ∫ w, s *
        GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N) (coordinateObservable N k i)
          (featureField N k) (s • Model.observation lam (x, w)) (EuclideanSpace.single i 1)
            ∂Model.noiseLaw N k := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [harg]
      simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
        gaussian_affine_expectation_ibp hN (coordinateObservable N k i)
          (continuous_coordinateObservable N k i).measurable zero_le_one
          (coordinateObservable_abs_le_ae hN i) b (EuclideanSpace.single i 1) s
    _ = ∫ w, ∑ i : Fin k → Fin N, s *
        GaussianSpinInterpolation.expectationDerivative (Model.spherePrior N) (coordinateObservable N k i)
          (featureField N k) (s • Model.observation lam (x, w)) (EuclideanSpace.single i 1)
            ∂Model.noiseLaw N k := (integral_finsetSum Finset.univ (fun i _ ↦ hd i)).symm
    _ = ∫ w, s * (1 -
        ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam (x, w))‖ ^ 2)
            ∂Model.noiseLaw N k := by
      apply integral_congr_ae
      exact .of_forall fun w ↦ by
        dsimp only
        rw [← Finset.mul_sum, sum_expectationDerivative_coordinate hN]
    _ = _ := integral_const_mul s _

theorem integrable_mean_norm_sq {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦
      ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)‖ ^ 2)
      (Model.experimentLaw N k) := by
  apply (PosteriorProofs.integrable_posterior_norm_sq hN lam).congr
  filter_upwards [PosteriorDensityProofs.gibbsTensorMean_ae_eq_posteriorTensor hN lam] with z hz
  rw [hz]

theorem integrable_latent_inner_mean {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦
      inner ℝ (Model.feature k z.1)
        (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)))
      (Model.experimentLaw N k) := by
  apply (PosteriorProofs.integrable_latent_inner_posterior hN lam).congr
  filter_upwards [PosteriorDensityProofs.gibbsTensorMean_ae_eq_posteriorTensor hN lam] with z hz
  rw [hz]

theorem integral_mean_norm_sq {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)‖ ^ 2
      ∂Model.experimentLaw N k) =
      ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k := by
  apply integral_congr_ae
  filter_upwards [PosteriorDensityProofs.gibbsTensorMean_ae_eq_posteriorTensor hN lam] with z hz
  rw [hz]

theorem integral_latent_inner_mean {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, inner ℝ (Model.feature k z.1)
      (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z))
      ∂Model.experimentLaw N k) =
      ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k := by
  rw [← PosteriorProofs.integral_latent_inner_posterior hN lam]
  apply integral_congr_ae
  filter_upwards [PosteriorDensityProofs.gibbsTensorMean_ae_eq_posteriorTensor hN lam] with z hz
  rw [hz]

theorem integrable_noise_inner_mean {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦
      inner ℝ (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)) z.2)
      (Model.experimentLaw N k) := by
  have hm : AEStronglyMeasurable (fun z : Model.Vector N × Model.Tensor N k ↦
      PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z))
        (Model.experimentLaw N k) :=
    ((PosteriorDensityProofs.measurable_gibbsTensorMean N k lam).comp
    (Model.measurable_observation N k lam)).aestronglyMeasurable
  apply (integrable_noise_norm N k).mono' (hm.inner measurable_snd.aestronglyMeasurable)
  exact .of_forall fun z ↦ by
    have hb := mul_le_mul_of_nonneg_right
      (PosteriorDensityProofs.norm_gibbsTensorMean_le_one hN lam (Model.observation lam z))
      (norm_nonneg z.2)
    exact (norm_inner_le_norm _ _).trans (by simpa only [one_mul] using hb)

theorem integral_experiment_noise_inner_mean {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, inner ℝ (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)) z.2
      ∂Model.experimentLaw N k) =
    (lam * Real.sqrt N) * (1 -
      ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k) := by
  change (∫ z, inner ℝ (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)) z.2
    ∂(Model.spherePrior N).prod (Model.noiseLaw N k)) = _
  rw [integral_prod _ (integrable_noise_inner_mean (k := k) hN lam)]
  simp_rw [integral_noise_inner_mean hN lam]
  rw [integral_const_mul, ← integral_prod _ ((integrable_const (1 : ℝ)).sub'
    (integrable_mean_norm_sq (k := k) hN lam))]
  change (lam * Real.sqrt N) * (∫ z, 1 -
    ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)‖ ^ 2
      ∂Model.experimentLaw N k) = _
  rw [integral_sub (integrable_const (1 : ℝ)) (integrable_mean_norm_sq (k := k) hN lam),
    integral_mean_norm_sq hN lam]
  simp

theorem plantedLogDerivative_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (z : Model.Vector N × Model.Tensor N k) :
    plantedLogDerivative N k lam z =
      (2 * (N : ℝ) * lam) * inner ℝ (Model.feature k z.1)
        (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)) +
      Real.sqrt N * inner ℝ
        (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)) z.2 - (N : ℝ) * lam := by
  rw [plantedLogDerivative, score_eq_innerSL_gibbsTensorMean hN]
  simp only [innerSL_apply_apply, inner_add_right, real_inner_smul_right, real_inner_comm]

/-- The planted Gaussian path derivative reduces exactly to the actual
posterior second moment. No asymptotic assertion is used. -/
theorem integral_plantedLogDerivative {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, plantedLogDerivative N k lam z ∂Model.experimentLaw N k) =
      (N : ℝ) * lam * (1 - Model.tensorMMSE N k lam) := by
  simp_rw [plantedLogDerivative_eq hN]
  rw [integral_sub
    (((integrable_latent_inner_mean (k := k) hN lam).const_mul (2 * (N : ℝ) * lam)).fun_add
      ((integrable_noise_inner_mean (k := k) hN lam).const_mul (Real.sqrt N))) (integrable_const ((N : ℝ) * lam)),
    integral_add ((integrable_latent_inner_mean (k := k) hN lam).const_mul (2 * (N : ℝ) * lam))
      ((integrable_noise_inner_mean (k := k) hN lam).const_mul (Real.sqrt N)),
    integral_const_mul, integral_const_mul, integral_latent_inner_mean hN lam,
    integral_experiment_noise_inner_mean hN lam,
    PosteriorProofs.tensorMMSE_eq_one_sub_posterior_secondMoment hN lam]
  simp only [integral_const, probReal_univ, one_smul, sub_sub_cancel]
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  ring_nf
  rw [hs]
  ring

theorem hasDerivAt_integral_planted_logLikelihood_mmse {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    HasDerivAt (fun t ↦ ∫ z, Real.log (Model.likelihoodRatio N k t (Model.observation t z))
      ∂Model.experimentLaw N k) ((N : ℝ) * lam * (1 - Model.tensorMMSE N k lam)) lam := by
  simpa only [integral_plantedLogDerivative hN lam] using
    hasDerivAt_integral_planted_logLikelihood hN lam

/-- Finite I-MMSE with the manuscript's squared-strength parameter and physical
normalization, for the actual spherical channel. -/
theorem hasDerivAt_sphericalBayesFreeEnergy {N k : ℕ} (hN : 0 < N) {lam : ℝ}
    (hlam : 0 < lam) :
    HasDerivAt (Statistical.sphericalBayesFreeEnergy N k)
      ((1 / 2 : ℝ) * (1 - Model.tensorMMSE N k lam)) (lam ^ 2) := by
  have hsqrt : Real.sqrt (lam ^ 2) = lam := Real.sqrt_sq hlam.le
  have hp : HasDerivAt
      (fun t ↦ ∫ z, Real.log (Model.likelihoodRatio N k t (Model.observation t z))
        ∂Model.experimentLaw N k)
      ((N : ℝ) * lam * (1 - Model.tensorMMSE N k lam)) (Real.sqrt (lam ^ 2)) := by
    rw [hsqrt]
    exact hasDerivAt_integral_planted_logLikelihood_mmse hN lam
  have hc := (hp.comp (lam ^ 2) (Real.hasDerivAt_sqrt (sq_pos_of_pos hlam).ne')).div_const (N : ℝ)
  convert hc using 1
  · rfl
  · rw [hsqrt]
    have hNne : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    field_simp [hNne, hlam.ne']

theorem finiteIMMSE (k : ℕ) {lam : ℝ} (hlam : 0 < lam) : Statistical.FiniteIMMSE k lam := by
  intro n
  exact hasDerivAt_sphericalBayesFreeEnergy (Nat.succ_pos n) hlam


end TensorPCA.FiniteIMMSETraceProofs
