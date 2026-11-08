-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-dimensional posterior identities

These statements concern conditional expectation given the observation. In particular, the sub-σ-algebra is the comap of the observation,
and no conditioning on an individual Gaussian observation is used.
-/
@[expose] public section

namespace TensorPCA.PosteriorProofs

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- The observed σ-algebra is contained in the ambient experiment σ-algebra. -/
theorem observedSigma_le (N k : ℕ) (lam : ℝ) :
    Model.observedSigma N k lam ≤
      (inferInstance : MeasurableSpace (Model.Vector N × Model.Tensor N k)) :=
  (Model.measurable_observation N k lam).comap_le

/-- The planted tensor has unit norm almost surely, including tensor order zero. -/
theorem latent_norm_ae {N k : ℕ} (hN : 0 < N) :
    ∀ᵐ z ∂Model.experimentLaw N k, ‖Model.feature k z.1‖ = 1 := by
  have hx : ∀ᵐ z ∂Model.experimentLaw N k, ‖z.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  filter_upwards [hx] with z hz
  exact Geometry.feature_unit_norm z.1 hz

theorem measurable_latent (N k : ℕ) :
    Measurable (fun z : Model.Vector N × Model.Tensor N k ↦ Model.feature k z.1) :=
  (Model.continuous_feature N k).measurable.comp measurable_fst

/-- The concrete latent feature is square integrable. -/
theorem latent_memLp_two {N k : ℕ} (hN : 0 < N) :
    MemLp (fun z : Model.Vector N × Model.Tensor N k ↦ Model.feature k z.1)
      2 (Model.experimentLaw N k) := by
  apply MemLp.of_bound (measurable_latent N k).aestronglyMeasurable 1
  exact (latent_norm_ae hN).mono fun _ hz ↦ hz.le

/-- The posterior is measurable with respect to precisely the observed σ-algebra. -/
theorem stronglyMeasurable_posterior (N k : ℕ) (lam : ℝ) :
    StronglyMeasurable[Model.observedSigma N k lam] (Model.posteriorTensor N k lam) :=
  stronglyMeasurable_condExp

theorem posterior_memLp_two {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    MemLp (Model.posteriorTensor N k lam) 2 (Model.experimentLaw N k) :=
  (latent_memLp_two hN).condExp (by norm_num)

/-- Conditional Jensen preserves the almost sure unit-ball bound. -/
theorem posterior_norm_le_one_ae {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    ∀ᵐ z ∂Model.experimentLaw N k, ‖Model.posteriorTensor N k lam z‖ ≤ 1 :=
  ae_bdd_norm_condExp_of_ae_bdd_norm ((latent_norm_ae hN).mono fun _ hz ↦ hz.le)

theorem integrable_latent_norm_sq {N k : ℕ} (hN : 0 < N) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦ ‖Model.feature k z.1‖ ^ 2)
      (Model.experimentLaw N k) := by
  exact (latent_memLp_two hN).integrable_norm_pow (by decide)

theorem integrable_posterior_norm_sq {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z ↦ ‖Model.posteriorTensor N k lam z‖ ^ 2)
      (Model.experimentLaw N k) := by
  exact (posterior_memLp_two hN lam).integrable_norm_pow (by decide)

/-- The latent second moment is exactly one under the physical prior. -/
theorem integral_latent_norm_sq {N k : ℕ} (hN : 0 < N) :
    (∫ z, ‖Model.feature k z.1‖ ^ 2 ∂Model.experimentLaw N k) = 1 := by
  calc
    _ = ∫ _z, (1 : ℝ) ∂Model.experimentLaw N k := by
      apply integral_congr_ae
      filter_upwards [latent_norm_ae hN] with z hz
      simp [hz]
    _ = 1 := by simp

theorem integrable_latent_inner_posterior {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z ↦ inner ℝ (Model.feature k z.1) (Model.posteriorTensor N k lam z))
      (Model.experimentLaw N k) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_latent N k).aestronglyMeasurable.inner
      ((stronglyMeasurable_posterior N k lam).mono (observedSigma_le N k lam)).aestronglyMeasurable)
  filter_upwards [latent_norm_ae hN, posterior_norm_le_one_ae hN lam] with z ht hp
  calc
    ‖inner ℝ (Model.feature k z.1) (Model.posteriorTensor N k lam z)‖ ≤
        ‖Model.feature k z.1‖ * ‖Model.posteriorTensor N k lam z‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by simpa [ht] using hp

/-- The conditional mean has the same cross second moment as its own second
moment. This is the finite posterior projection identity, before expanding loss. -/
theorem integral_latent_inner_posterior {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, inner ℝ (Model.feature k z.1) (Model.posteriorTensor N k lam z)
      ∂Model.experimentLaw N k) =
      ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k := by
  have hce := condExp_bilin_of_stronglyMeasurable_right (innerSL ℝ)
    (stronglyMeasurable_posterior N k lam)
    (integrable_latent_inner_posterior hN lam)
    ((latent_memLp_two hN).integrable (by norm_num))
  calc
    _ = ∫ z, (Model.experimentLaw N k)[
        (fun z ↦ inner ℝ (Model.feature k z.1) (Model.posteriorTensor N k lam z))
        | Model.observedSigma N k lam] z ∂Model.experimentLaw N k :=
      (integral_condExp (observedSigma_le N k lam)).symm
    _ = ∫ z, inner ℝ (Model.posteriorTensor N k lam z)
        (Model.posteriorTensor N k lam z) ∂Model.experimentLaw N k :=
      integral_congr_ae hce
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

/-- The actual tensor Bayes risk is one minus the posterior second moment. -/
theorem tensorMMSE_eq_one_sub_posterior_secondMoment {N k : ℕ}
    (hN : 0 < N) (lam : ℝ) :
    Model.tensorMMSE N k lam =
      1 - ∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2 ∂Model.experimentLaw N k := by
  unfold Model.tensorMMSE
  simp_rw [norm_sub_sq_real]
  rw [integral_add
    (f := fun z ↦ ‖Model.feature k z.1‖ ^ 2 -
      2 * inner ℝ (Model.feature k z.1) (Model.posteriorTensor N k lam z))
    (g := fun z ↦ ‖Model.posteriorTensor N k lam z‖ ^ 2)
    ((integrable_latent_norm_sq hN).sub
      ((integrable_latent_inner_posterior hN lam).const_mul 2))
    (integrable_posterior_norm_sq hN lam)]
  rw [integral_sub (f := fun z ↦ ‖Model.feature k z.1‖ ^ 2)
    (g := fun z ↦ 2 * inner ℝ (Model.feature k z.1) (Model.posteriorTensor N k lam z))
    (integrable_latent_norm_sq hN)
    ((integrable_latent_inner_posterior hN lam).const_mul 2)]
  rw [integral_const_mul, integral_latent_norm_sq hN,
    integral_latent_inner_posterior hN lam]
  ring

theorem tensorMMSE_nonneg (N k : ℕ) (lam : ℝ) :
    0 ≤ Model.tensorMMSE N k lam :=
  integral_nonneg fun _ ↦ sq_nonneg _

theorem tensorMMSE_le_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Model.tensorMMSE N k lam ≤ 1 := by
  rw [tensorMMSE_eq_one_sub_posterior_secondMoment hN lam]
  have := integral_nonneg
    (μ := Model.experimentLaw N k) (fun z ↦ sq_nonneg ‖Model.posteriorTensor N k lam z‖)
  linarith

/-- The first posterior norm moment is controlled by its second moment. -/
theorem integral_posterior_norm_le_sqrt {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, ‖Model.posteriorTensor N k lam z‖ ∂Model.experimentLaw N k) ≤
      Real.sqrt (∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2
        ∂Model.experimentLaw N k) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := Model.experimentLaw N k) (p := 2) (q := 2)
    (f := fun z ↦ ‖Model.posteriorTensor N k lam z‖) (g := fun _ ↦ (1 : ℝ))
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (by simpa using (posterior_memLp_two hN lam).norm)
    (by simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : Model.Vector N × Model.Tensor N k ↦ (1 : ℝ)) 2
        (Model.experimentLaw N k)))
  rw [Real.sqrt_eq_rpow]
  simpa [Real.rpow_two] using h

/-- A measurable observation-dependent tensor in the unit ball has signed
correlation bounded by the square root of the posterior second moment. -/
theorem observed_test_inner_le_sqrt {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (u : Model.Tensor N k → Model.Tensor N k) (hu : Measurable u)
    (hu_norm : ∀ y, ‖u y‖ ≤ 1) :
    (∫ z, inner ℝ (u (Model.observation lam z)) (Model.feature k z.1)
      ∂Model.experimentLaw N k) ≤
      Real.sqrt (∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2
        ∂Model.experimentLaw N k) := by
  have hu_obs : StronglyMeasurable[Model.observedSigma N k lam]
      (fun z ↦ u (Model.observation lam z)) :=
    (hu.comp (comap_measurable (Model.observation lam))).stronglyMeasurable
  have hu_ambient : AEStronglyMeasurable (fun z ↦ u (Model.observation lam z))
      (Model.experimentLaw N k) :=
    (hu_obs.mono (observedSigma_le N k lam)).aestronglyMeasurable
  have hu_bound : ∀ᵐ z ∂Model.experimentLaw N k, ‖u (Model.observation lam z)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z ↦ hu_norm _
  have hT := (latent_memLp_two (k := k) hN).integrable (by norm_num)
  have hP := (posterior_memLp_two (k := k) hN lam).integrable (by norm_num)
  have huT := (innerSL ℝ).integrable_of_bilin_of_bdd_left 1 hu_ambient hu_bound hT
  have huP := (innerSL ℝ).integrable_of_bilin_of_bdd_left 1 hu_ambient hu_bound hP
  have hce := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hu_obs huT hT
  calc
    _ = ∫ z, (Model.experimentLaw N k)[
        (fun z ↦ inner ℝ (u (Model.observation lam z)) (Model.feature k z.1))
        | Model.observedSigma N k lam] z ∂Model.experimentLaw N k :=
      (integral_condExp (observedSigma_le N k lam)).symm
    _ = ∫ z, inner ℝ (u (Model.observation lam z)) (Model.posteriorTensor N k lam z)
        ∂Model.experimentLaw N k := integral_congr_ae hce
    _ ≤ ∫ z, ‖Model.posteriorTensor N k lam z‖ ∂Model.experimentLaw N k := by
      apply integral_mono_ae huP hP.norm
      filter_upwards with z
      calc
        inner ℝ (u (Model.observation lam z)) (Model.posteriorTensor N k lam z) ≤
            ‖u (Model.observation lam z)‖ * ‖Model.posteriorTensor N k lam z‖ :=
          real_inner_le_norm _ _
        _ ≤ 1 * ‖Model.posteriorTensor N k lam z‖ :=
          mul_le_mul_of_nonneg_right (hu_norm _) (norm_nonneg _)
        _ = _ := one_mul _
    _ ≤ _ := integral_posterior_norm_le_sqrt hN lam

/-- Independent auxiliary randomization preserves the finite signed tensor-test
bound, by Fubini applied at each auxiliary value. -/
theorem randomized_test_inner_le_sqrt {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (u : Model.Tensor N k → A → Model.Tensor N k)
    (hu : Measurable (Function.uncurry u)) (hu_norm : ∀ y a, ‖u y a‖ ≤ 1) :
    (∫ z, inner ℝ (u (Model.observation lam z.1) z.2) (Model.feature k z.1.1)
      ∂(Model.experimentLaw N k).prod ν) ≤
      Real.sqrt (∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2
        ∂Model.experimentLaw N k) := by
  have hu_meas : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      u (Model.observation lam z.1) z.2) :=
    hu.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk measurable_snd)
  have hT_meas : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      Model.feature k z.1.1) := (measurable_latent N k).comp measurable_fst
  have hT_norm : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν,
      ‖Model.feature k z.1.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (latent_norm_ae hN)
  have hf : Integrable (fun z ↦
      inner ℝ (u (Model.observation lam z.1) z.2) (Model.feature k z.1.1))
      ((Model.experimentLaw N k).prod ν) := by
    apply (integrable_const (1 : ℝ)).mono'
      (hu_meas.aestronglyMeasurable.inner hT_meas.aestronglyMeasurable)
    filter_upwards [hT_norm] with z hz
    calc
      ‖inner ℝ (u (Model.observation lam z.1) z.2) (Model.feature k z.1.1)‖ ≤
          ‖u (Model.observation lam z.1) z.2‖ * ‖Model.feature k z.1.1‖ :=
        norm_inner_le_norm _ _
      _ ≤ 1 := by simpa [hz] using hu_norm (Model.observation lam z.1) z.2
  rw [integral_prod_symm _ hf]
  calc
    _ ≤ ∫ _a, Real.sqrt (∫ z, ‖Model.posteriorTensor N k lam z‖ ^ 2
        ∂Model.experimentLaw N k) ∂ν := by
      apply integral_mono_ae hf.integral_prod_right (integrable_const _)
      filter_upwards with a
      exact observed_test_inner_le_sqrt hN lam (fun y ↦ u y a)
        (hu.comp (measurable_id.prodMk measurable_const)) (fun y ↦ hu_norm y a)
    _ = _ := by simp

/-- The manuscript's signed kth-moment bound, including arbitrary independent
auxiliary randomness, under the concrete posterior convention. -/
theorem signed_overlap_le_sqrt_one_sub_tensorMMSE {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    (∫ z, (inner ℝ (est (Model.observation lam z.1) z.2) z.1.1) ^ k
      ∂(Model.experimentLaw N k).prod ν) ≤
      Real.sqrt (1 - Model.tensorMMSE N k lam) := by
  have h := randomized_test_inner_le_sqrt hN lam ν
    (fun y a ↦ Model.feature k (est y a))
    ((Model.continuous_feature N k).measurable.comp hest.1)
    (fun y a ↦ by simp [Geometry.feature_norm, hest.2 y a])
  simpa only [Geometry.feature_inner,
    tensorMMSE_eq_one_sub_posterior_secondMoment hN lam, sub_sub_cancel] using h

/-- For even order, the signed bound is already the absolute-moment bound. -/
theorem even_expectedOverlapPower_le_sqrt_one_sub_tensorMMSE {N k : ℕ}
    (hN : 0 < N) (hk : Even k) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k lam est ν k ≤ Real.sqrt (1 - Model.tensorMMSE N k lam) := by
  simpa only [Model.expectedOverlapPower, hk.pow_abs] using
    signed_overlap_le_sqrt_one_sub_tensorMMSE hN lam ν est hest


end TensorPCA.PosteriorProofs
