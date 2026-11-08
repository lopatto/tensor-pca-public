-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteIMMSETraceProofs
public import TensorPCA.OddValidationProofs
public import TensorPCA.ConvexLimitProofs
public import TensorPCA.CheckedReduction

/-!
# Finite Bayesian monotonicity and convexity

A stronger Gaussian observation can simulate a weaker one by adding independent
noise. Conditional-mean projection then compares the posterior second moments. Finite I-MMSE converts this comparison to convexity in squared strength.
-/
@[expose] public section

namespace TensorPCA.BayesianMonotonicityProofs

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

theorem observed_test_projection {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (u : Model.Tensor N k → Model.Tensor N k) (hu : Measurable u)
    (hu_norm : ∀ y, ‖u y‖ ≤ 1) :
    (∫ z, inner ℝ (u (Model.observation lam z)) (Model.feature k z.1)
      ∂Model.experimentLaw N k) =
    ∫ z, inner ℝ (u (Model.observation lam z))
      (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z))
        ∂Model.experimentLaw N k := by
  have hu_obs : StronglyMeasurable[Model.observedSigma N k lam]
      (fun z ↦ u (Model.observation lam z)) :=
    (hu.comp (comap_measurable (Model.observation lam))).stronglyMeasurable
  have hu_ambient : AEStronglyMeasurable (fun z ↦ u (Model.observation lam z))
      (Model.experimentLaw N k) :=
    (hu_obs.mono (PosteriorProofs.observedSigma_le N k lam)).aestronglyMeasurable
  have hu_bound : ∀ᵐ z ∂Model.experimentLaw N k, ‖u (Model.observation lam z)‖ ≤ 1 :=
    .of_forall fun z ↦ hu_norm _
  have hT := (PosteriorProofs.latent_memLp_two (k := k) hN).integrable (by norm_num)
  have huT := (innerSL ℝ).integrable_of_bilin_of_bdd_left 1 hu_ambient hu_bound hT
  have hce := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hu_obs huT hT
  calc
    _ = ∫ z, (Model.experimentLaw N k)[
        (fun z ↦ inner ℝ (u (Model.observation lam z)) (Model.feature k z.1))
        | Model.observedSigma N k lam] z ∂Model.experimentLaw N k :=
      (integral_condExp (PosteriorProofs.observedSigma_le N k lam)).symm
    _ = ∫ z, inner ℝ (u (Model.observation lam z)) (Model.posteriorTensor N k lam z)
        ∂Model.experimentLaw N k := integral_congr_ae hce
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [PosteriorDensityProofs.gibbsTensorMean_ae_eq_posteriorTensor hN lam] with z hz
      rw [hz]

theorem randomized_test_projection {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsProbabilityMeasure nu]
    (u : Model.Tensor N k → A → Model.Tensor N k)
    (hu : Measurable (Function.uncurry u)) (hu_norm : ∀ y a, ‖u y a‖ ≤ 1) :
    (∫ z, inner ℝ (u (Model.observation lam z.1) z.2) (Model.feature k z.1.1)
      ∂(Model.experimentLaw N k).prod nu) =
    ∫ z, inner ℝ (u (Model.observation lam z.1) z.2)
      (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z.1))
        ∂(Model.experimentLaw N k).prod nu := by
  have hu_meas : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      u (Model.observation lam z.1) z.2) :=
    hu.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk measurable_snd)
  have hT_meas : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      Model.feature k z.1.1) := (PosteriorProofs.measurable_latent N k).comp measurable_fst
  have hm_meas : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z.1)) :=
    ((PosteriorDensityProofs.measurable_gibbsTensorMean N k lam).comp
      (Model.measurable_observation N k lam)).comp measurable_fst
  have hT_norm : ∀ᵐ z ∂(Model.experimentLaw N k).prod nu, ‖Model.feature k z.1.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (PosteriorProofs.latent_norm_ae hN)
  have hf : Integrable (fun z ↦ inner ℝ (u (Model.observation lam z.1) z.2) (Model.feature k z.1.1))
      ((Model.experimentLaw N k).prod nu) := by
    apply (integrable_const (1 : ℝ)).mono'
      (hu_meas.aestronglyMeasurable.inner hT_meas.aestronglyMeasurable)
    filter_upwards [hT_norm] with z hz
    exact (norm_inner_le_norm _ _).trans (by simpa only [hz, mul_one] using hu_norm _ _)
  have hg : Integrable (fun z ↦ inner ℝ (u (Model.observation lam z.1) z.2)
      (PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z.1)))
      ((Model.experimentLaw N k).prod nu) := by
    apply (integrable_const (1 : ℝ)).mono'
      (hu_meas.aestronglyMeasurable.inner hm_meas.aestronglyMeasurable)
    exact .of_forall fun z ↦ by
      have hb := mul_le_mul (hu_norm (Model.observation lam z.1) z.2)
        (PosteriorDensityProofs.norm_gibbsTensorMean_le_one hN lam (Model.observation lam z.1))
        (norm_nonneg _) zero_le_one
      exact (norm_inner_le_norm _ _).trans (by simpa only [mul_one] using hb)
  rw [integral_prod_symm _ hf, integral_prod_symm _ hg]
  apply integral_congr_ae
  exact .of_forall fun a ↦ observed_test_projection hN lam (fun y ↦ u y a)
    (hu.comp (measurable_id.prodMk measurable_const)) (fun y ↦ hu_norm y a)

theorem integrable_norm_sq_of_unit_bound {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (f : Omega → E) (hf : Measurable f)
    (hb : ∀ z, ‖f z‖ ≤ 1) : Integrable (fun z ↦ ‖f z‖ ^ 2) mu := by
  apply (integrable_const (1 : ℝ)).mono' (hf.norm.pow_const 2).aestronglyMeasurable
  exact .of_forall fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (f z)) (hb z) 2

theorem integrable_inner_of_unit_bound {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f g : Omega → E) (hf : Measurable f) (hg : Measurable g)
    (hbf : ∀ z, ‖f z‖ ≤ 1) (hbg : ∀ z, ‖g z‖ ≤ 1) :
    Integrable (fun z ↦ inner ℝ (f z) (g z)) mu := by
  apply (integrable_const (1 : ℝ)).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact .of_forall fun z ↦ (norm_inner_le_norm _ _).trans
    (by simpa only [mul_one] using mul_le_mul (hbf z) (hbg z) (norm_nonneg _) zero_le_one)

/-- A randomized bounded tensor predictor cannot improve on the posterior in mean squared error. This quadratic form is convenient for
comparing two information strengths. -/
theorem randomized_test_secondMoment_bound {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsProbabilityMeasure nu]
    (u : Model.Tensor N k → A → Model.Tensor N k)
    (hu : Measurable (Function.uncurry u)) (hu_norm : ∀ y a, ‖u y a‖ ≤ 1) :
    2 * (∫ z, inner ℝ (u (Model.observation lam z.1) z.2) (Model.feature k z.1.1)
      ∂(Model.experimentLaw N k).prod nu) ≤
    (∫ z, ‖u (Model.observation lam z.1) z.2‖ ^ 2 ∂(Model.experimentLaw N k).prod nu) +
      ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k := by
  let U : (Model.Vector N × Model.Tensor N k) × A → Model.Tensor N k :=
    fun z ↦ u (Model.observation lam z.1) z.2
  let P : (Model.Vector N × Model.Tensor N k) × A → Model.Tensor N k :=
    fun z ↦ PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z.1)
  have hU : Measurable U :=
    hu.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk measurable_snd)
  have hP : Measurable P := ((PosteriorDensityProofs.measurable_gibbsTensorMean N k lam).comp
    (Model.measurable_observation N k lam)).comp measurable_fst
  have hUb (z) : ‖U z‖ ≤ 1 := hu_norm _ _
  have hPb (z) : ‖P z‖ ≤ 1 := PosteriorDensityProofs.norm_gibbsTensorMean_le_one hN lam _
  have hUsq := integrable_norm_sq_of_unit_bound ((Model.experimentLaw N k).prod nu) U hU hUb
  have hPsq := integrable_norm_sq_of_unit_bound ((Model.experimentLaw N k).prod nu) P hP hPb
  have hInner := integrable_inner_of_unit_bound ((Model.experimentLaw N k).prod nu) U P hU hP hUb hPb
  have hI : (∫ z, 2 * inner ℝ (U z) (P z) ∂(Model.experimentLaw N k).prod nu) ≤
      ∫ z, ‖U z‖ ^ 2 + ‖P z‖ ^ 2 ∂(Model.experimentLaw N k).prod nu := by
    apply integral_mono_ae (hInner.const_mul 2) (hUsq.fun_add hPsq)
    exact .of_forall fun z ↦ by linarith [norm_sub_sq_real (U z) (P z), sq_nonneg ‖U z-P z‖]
  rw [integral_const_mul, integral_add hUsq hPsq] at hI
  have hPm : (∫ z, ‖P z‖ ^ 2 ∂(Model.experimentLaw N k).prod nu) =
      ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k := by
    change (∫ z, ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z.1)‖ ^ 2
      ∂(Model.experimentLaw N k).prod nu) = _
    rw [integral_fun_fst (μ := Model.experimentLaw N k) (ν := nu)
      (fun z ↦ ‖PosteriorDensityProofs.gibbsTensorMean N k lam (Model.observation lam z)‖ ^ 2)]
    simpa using FiniteIMMSETraceProofs.integral_mean_norm_sq hN lam
  rw [hPm] at hI
  rw [randomized_test_projection hN lam nu u hu hu_norm]
  exact hI

theorem integral_noiseMix_fst (N k : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (f : Model.Vector N × Model.Tensor N k → ℝ) (hf : Measurable f) :
    (∫ z, f (z.1.1, a • z.1.2 + b • z.2)
      ∂(Model.experimentLaw N k).prod (Model.noiseLaw N k)) =
      ∫ z, f z ∂Model.experimentLaw N k := by
  have hMix := OddValidationProofs.measurePreserving_experimentMix N k a b hab
  have hfm : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × Model.Tensor N k ↦ f z.1) :=
    hf.comp measurable_fst
  have h := integral_map hMix.aemeasurable hfm.aestronglyMeasurable
  rw [hMix.map_eq] at h
  calc
    _ = ∫ z, f z.1 ∂(Model.experimentLaw N k).prod (Model.noiseLaw N k) := h.symm
    _ = _ := by rw [integral_fun_fst f]; simp

/-- Gaussian degradation compares the actual posterior moments. The coefficients
preserve the noise variance and send the stronger signal coefficient to the
weaker one; all posterior projections are taken under the original channel law. -/
theorem posterior_secondMoment_le_of_degradation {N k : ℕ} (hN : 0 < N)
    (low high a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (ha : a * high = low) :
    (∫ z, ‖Model.posteriorTensor N k low z‖ ^ 2 ∂Model.experimentLaw N k) ≤
      ∫ z, ‖Model.posteriorTensor N k high z‖ ^ 2 ∂Model.experimentLaw N k := by
  let u : Model.Tensor N k → Model.Tensor N k → Model.Tensor N k :=
    fun y g ↦ PosteriorDensityProofs.gibbsTensorMean N k low (a • y + b • g)
  have hu : Measurable (Function.uncurry u) :=
    (PosteriorDensityProofs.measurable_gibbsTensorMean N k low).comp
      ((continuous_fst.const_smul a).add (continuous_snd.const_smul b)).measurable
  have hub (y g) : ‖u y g‖ ≤ 1 := PosteriorDensityProofs.norm_gibbsTensorMean_le_one hN low _
  have hbridge (z : (Model.Vector N × Model.Tensor N k) × Model.Tensor N k) :
      u (Model.observation high z.1) z.2 =
      PosteriorDensityProofs.gibbsTensorMean N k low
        (Model.observation low (z.1.1, a • z.1.2 + b • z.2)) := by
    unfold u
    rw [OddValidationProofs.mix_observation_first a b high low ha]
  have hmean : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      PosteriorDensityProofs.gibbsTensorMean N k low (Model.observation low z)) :=
    (PosteriorDensityProofs.measurable_gibbsTensorMean N k low).comp
      (Model.measurable_observation N k low)
  have hcross : (∫ z, inner ℝ (u (Model.observation high z.1) z.2) (Model.feature k z.1.1)
      ∂(Model.experimentLaw N k).prod (Model.noiseLaw N k)) =
      ∫ z, ‖Model.posteriorTensor N k low z‖ ^ 2 ∂Model.experimentLaw N k := by
    simp_rw [hbridge]
    have hh := integral_noiseMix_fst N k a b hab
      (fun z ↦ inner ℝ (PosteriorDensityProofs.gibbsTensorMean N k low (Model.observation low z))
        (Model.feature k z.1))
      (Continuous.measurable2 (continuous_inner (𝕜 := ℝ)) hmean (PosteriorProofs.measurable_latent N k))
    rw [hh]
    simp_rw [real_inner_comm]
    exact FiniteIMMSETraceProofs.integral_latent_inner_mean hN low
  have hsq : (∫ z, ‖u (Model.observation high z.1) z.2‖ ^ 2
      ∂(Model.experimentLaw N k).prod (Model.noiseLaw N k)) =
      ∫ z, ‖Model.posteriorTensor N k low z‖ ^ 2 ∂Model.experimentLaw N k := by
    simp_rw [hbridge]
    have hh := integral_noiseMix_fst N k a b hab
      (fun z ↦ ‖PosteriorDensityProofs.gibbsTensorMean N k low (Model.observation low z)‖ ^ 2)
      (hmean.norm.pow_const 2)
    rw [hh]
    exact FiniteIMMSETraceProofs.integral_mean_norm_sq hN low
  have h := randomized_test_secondMoment_bound hN high (Model.noiseLaw N k) u hu hub
  rw [hcross, hsq] at h
  linarith

theorem monotoneOn_posterior_secondMoment {N k : ℕ} (hN : 0 < N) :
    MonotoneOn (fun lam ↦ ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k)
      (Set.Ioi (0 : ℝ)) := by
  intro low hlow high hhigh hle
  let a := low / high
  let b := Real.sqrt (1 - a ^ 2)
  have ha0 : 0 ≤ a := div_nonneg hlow.le hhigh.le
  have ha1 : a ≤ 1 := (div_le_one hhigh).mpr hle
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hab : a ^ 2 + b ^ 2 = 1 := by dsimp [b]; rw [Real.sq_sqrt (by linarith)]; ring
  have ha : a * high = low := div_mul_cancel₀ low hhigh.ne'
  exact posterior_secondMoment_le_of_degradation hN low high a b hab ha

theorem hasDerivAt_freeEnergy_pos {N k : ℕ} (hN : 0 < N) {gamma : ℝ} (hgamma : 0 < gamma) :
    HasDerivAt (Statistical.sphericalBayesFreeEnergy N k)
      ((1 / 2 : ℝ) * (∫ z, ‖Model.posteriorTensor N k (Real.sqrt gamma) z‖ ^ 2
        ∂Model.experimentLaw N k)) gamma := by
  have h := FiniteIMMSETraceProofs.hasDerivAt_sphericalBayesFreeEnergy (k := k) hN
    (Real.sqrt_pos.mpr hgamma)
  simpa only [Real.sq_sqrt hgamma.le,
    PosteriorProofs.tensorMMSE_eq_one_sub_posterior_secondMoment hN, sub_sub_cancel] using h

theorem monotoneOn_deriv_freeEnergy {N k : ℕ} (hN : 0 < N) :
    MonotoneOn (deriv (Statistical.sphericalBayesFreeEnergy N k)) (Set.Ioi (0 : ℝ)) := by
  intro gamma hgamma eta heta hle
  rw [(hasDerivAt_freeEnergy_pos (k := k) hN hgamma).deriv,
    (hasDerivAt_freeEnergy_pos (k := k) hN heta).deriv]
  exact mul_le_mul_of_nonneg_left
    (monotoneOn_posterior_secondMoment hN (Real.sqrt_pos.mpr hgamma)
      (Real.sqrt_pos.mpr heta) (Real.sqrt_le_sqrt hle)) (by norm_num)

theorem convexOn_freeEnergy {N k : ℕ} (hN : 0 < N) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (Statistical.sphericalBayesFreeEnergy N k) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi (0 : ℝ))
  · intro gamma hgamma
    exact (hasDerivAt_freeEnergy_pos hN hgamma).continuousAt.continuousWithinAt
  · rw [isOpen_Ioi.interior_eq]
    exact fun gamma hgamma ↦ (hasDerivAt_freeEnergy_pos hN hgamma).differentiableAt.differentiableWithinAt
  · simpa only [isOpen_Ioi.interior_eq] using monotoneOn_deriv_freeEnergy (k := k) hN

/-- The concrete finite secants hold at every dimension; the eventual form in
the reduction therefore introduces no discarded exceptional dimensions. -/
theorem bayesianConvexSecants (k : ℕ) : CheckedReduction.BayesianConvexSecants k := by
  intro gamma hgamma j
  apply Filter.Eventually.of_forall
  intro n
  have hstep : 0 < LimitTools.secantStep gamma j :=
    div_pos hgamma (by positivity)
  have hsmall : LimitTools.secantStep gamma j < gamma :=
    div_lt_self hgamma (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hc := convexOn_freeEnergy (k := k) (Nat.succ_pos n)
  have hd := (hasDerivAt_freeEnergy_pos (k := k) (Nat.succ_pos n) hgamma).differentiableAt
  constructor
  · have h := hc.slope_le_deriv (by simpa using sub_pos.mpr hsmall) hgamma
      (sub_lt_self gamma hstep) hd
    simpa only [slope_def_field, sub_sub_cancel] using h
  · have h := hc.deriv_le_slope hgamma (by simpa using add_pos hgamma hstep)
      (lt_add_of_pos_right gamma hstep) hd
    simpa only [slope_def_field, add_sub_cancel_left] using h


end TensorPCA.BayesianMonotonicityProofs
