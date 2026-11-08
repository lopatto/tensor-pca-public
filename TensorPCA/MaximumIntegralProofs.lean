-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.MaximumDerivativeProofs
public import TensorPCA.BayesianMonotonicityProofs
public import TensorPCA.ScalarBayesianProofs
public import TensorPCA.FiniteIMMSETraceProofs
public import TensorPCA.ValidationControlProofs
public import TensorPCA.EstimatorBounds

/-! Maximum derivative integration and bounded reverse Fatou. Bayesian
free-energy value convergence is an independent intermediate premise;
no expected-maximum or MLE-value conclusion is assumed. -/

@[expose] public section
namespace TensorPCA.MaximumIntegralProofs
open MeasureTheory ProbabilityTheory Set Filter MaximumDerivativeProofs MleEstimatorProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- The proved finite Bayesian secants, I-MMSE identity and scalar derivative
turn value convergence into the positive-strength MMSE limit. -/
theorem tensorMMSE_tendsto_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ Scalar.lambdaC k) :
    Tendsto (fun n : ℕ ↦ Model.tensorMMSE (n+1) k lam) atTop (𝓝 (1-(Scalar.qStar k lam)^k)) := by
  apply Statistical.tensorMMSE_tendsto_of_derivative_values (FiniteIMMSETraceProofs.finiteIMMSE k hlam)
  exact Reduction.bayesian_derivative_at hlam hvalues
    (BayesianMonotonicityProofs.bayesianConvexSecants k (lam^2) (sq_pos_of_pos hlam))
    (ScalarBayesianProofs.hasDerivAt_bayesianLimit k hk hlam hne)

/-- The estimator upper bound is derived from Bayesian values and finite
posterior/validation inequalities. -/
theorem estimator_kth_limsup_le_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam : ℝ}
    (hlam : 0 ≤ lam) (hne : lam ≠ Scalar.lambdaC k)
    {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
    (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
    (est : ∀ n, Model.Estimator (n+1) k (A n))
    (hest : ∀ n, Model.IsUnitEstimator (est n)) :
    limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k) atTop ≤
      (Real.sqrt (Scalar.qStar k lam))^k := by
  exact (Reduction.estimator_of_finite_bounds ν est
    (EstimatorBounds.finiteEstimatorBounds k (by omega) lam A ν est hest)
    (ValidationControlProofs.validationEnvelopeControl k hk hlam hne
      (fun mu hmu hne ↦ tensorMMSE_tendsto_of_values k hk hvalues hmu hne))).1

/-- Every signed overlap power is dominated in expectation by its absolute
power under the actual experiment and independent estimator randomness. -/
theorem signed_overlap_integral_le {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    (∫ z : (Model.Vector N × Model.Tensor N k) × A,
      (inner ℝ (est (Model.observation lam z.1) z.2) z.1.1)^k ∂(Model.experimentLaw N k).prod ν) ≤
      Model.expectedOverlapPower N k lam est ν k := by
  have hAbs := Geometry.estimator_overlap_power_integrable ν hN est hest lam k
  have hMeas : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      (inner ℝ (est (Model.observation lam z.1) z.2) z.1.1)^k) := by
    apply Measurable.pow_const
    exact continuous_inner.measurable.comp
      ((hest.1.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk
        measurable_snd)).prodMk (measurable_fst.comp measurable_fst))
  have hSigned := hAbs.mono' hMeas.aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs, abs_pow]))
  exact integral_mono hSigned hAbs (fun z ↦ by rw [← abs_pow]; exact le_abs_self _)

/-- Absolute overlap powers of unit estimators are at most one in the actual
experiment, providing the essential boundedness needed by reverse Fatou. -/
theorem expectedOverlapPower_le_one {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k lam est ν k ≤ 1 := by
  have hi := Geometry.estimator_overlap_power_integrable ν hN est hest lam k
  have hs : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ‖z.1.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (OddValidationProofs.experiment_vector_norm_ae hN)
  have hbound : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν,
      |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1|^k ≤ 1 := by
    filter_upwards [hs] with z hz
    apply pow_le_one₀ (abs_nonneg _)
    simpa only [hest.2 _ _, hz, one_mul] using
      abs_real_inner_le_norm (est (Model.observation lam z.1) z.2) z.1.1
  have H := integral_mono_ae hi (integrable_const (1 : ℝ)) hbound
  simpa only [Model.expectedOverlapPower, integral_const, probReal_univ, one_smul] using H

/-- The actual selected derivative has the pointwise-in-strength limsup upper
bound required before applying the bounded reverse-Fatou argument. -/
theorem selectedSlope_limsup_le_of_values (k : ℕ) (hk : 2 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence (k+1)) {lam : ℝ}
    (hlam : 0 ≤ lam) (hne : lam ≠ Scalar.lambdaC (k+1)) :
    limsup (fun n : ℕ ↦ selectedSlope (n+1) k (Nat.succ_pos n) lam) atTop ≤
      (Real.sqrt (Scalar.qStar (k+1) lam))^(k+1) := by
  have hcomp (n : ℕ) : selectedSlope (n+1) k (Nat.succ_pos n) lam ≤
      Model.expectedOverlapPower (n+1) (k+1) lam
        (fairEstimator (n+1) k (Nat.succ_pos n)) fairSeed (k+1) := by
    rw [selectedSlope_eq_fairEstimator]
    exact signed_overlap_integral_le (Nat.succ_pos n) lam fairSeed _ (fairEstimator_isUnit _ _ _)
  have hlower : atTop.IsCoboundedUnder (· ≤ ·)
      (fun n : ℕ ↦ selectedSlope (n+1) k (Nat.succ_pos n) lam) :=
    isCoboundedUnder_le_of_le atTop (fun n ↦ (abs_le.mp (selectedSlope_abs_le_one (n+1) k (Nat.succ_pos n) lam)).1)
  have hupper : atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ ↦
      Model.expectedOverlapPower (n+1) (k+1) lam
        (fairEstimator (n+1) k (Nat.succ_pos n)) fairSeed (k+1)) :=
    isBoundedUnder_of ⟨1, fun n ↦ expectedOverlapPower_le_one (Nat.succ_pos n) lam fairSeed _ (fairEstimator_isUnit _ _ _)⟩
  exact (limsup_le_limsup (Eventually.of_forall hcomp) hlower hupper).trans
    (estimator_kth_limsup_le_of_values (k+1) (by omega) hvalues hlam hne
      (fun _ ↦ fairSeed) (fun n ↦ fairEstimator (n+1) k (Nat.succ_pos n))
      (fun n ↦ fairEstimator_isUnit _ _ _))

/-- Bounded reverse Fatou for real observables under a finite measure. The
proof uses measurable positive parts and dominated convergence, so all a.e.
and integrability hypotheses remain explicit. -/
theorem limsup_integral_le_of_unit_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hb : ∀ n x, |f n x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1)
    (hlim : ∀ᵐ x ∂μ, limsup (fun n ↦ f n x) atTop ≤ g x) :
    limsup (fun n ↦ ∫ x, f n x ∂μ) atTop ≤ ∫ x, g x ∂μ := by
  have hfi (n : ℕ) : Integrable (f n) μ := Integrable.of_bound (hf n).aestronglyMeasurable 1
    (Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hb n x))
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hgb x))
  have hlo (n : ℕ) : -μ.real univ ≤ ∫ x, f n x ∂μ := by
    have H := integral_mono (integrable_const (-1 : ℝ)) (hfi n) (fun x ↦ (abs_le.mp (hb n x)).1)
    simpa only [integral_const, smul_eq_mul, mul_neg, mul_one] using H
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let eps := delta/(μ.real univ+1)
  have hmass : 0 ≤ μ.real univ := measureReal_nonneg
  have heps : 0 < eps := div_pos hdelta (by linarith)
  let F : ℕ → Ω → ℝ := fun n x ↦ max (f n x-g x-eps) 0
  have hFm (n : ℕ) : Measurable (F n) := ((hf n).sub hg |>.sub measurable_const).max measurable_const
  have hFb (n : ℕ) (x : Ω) : ‖F n x‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by norm_num)
    have h1 := (abs_le.mp (hb n x)).2
    have h2 := (abs_le.mp (hgb x)).1
    linarith
  have hFi (n : ℕ) : Integrable (F n) μ := Integrable.of_bound (hFm n).aestronglyMeasurable 2
    (Eventually.of_forall (hFb n))
  have hFt : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have hupper : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ f n x) :=
      isBoundedUnder_of ⟨1, fun n ↦ (abs_le.mp (hb n x)).2⟩
    have hevent := eventually_lt_add_pos_of_limsup_le hupper hx heps
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    exact (max_eq_right (by linarith : f n x-g x-eps ≤ 0)).symm
  have hFzero : Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _x : Ω ↦ (2 : ℝ)) (fun n ↦ (hFm n).aestronglyMeasurable)
      (integrable_const 2) (fun n ↦ Eventually.of_forall (hFb n)) hFt
  have hpoint (n : ℕ) : (∫ x, f n x ∂μ) ≤
      (∫ x, g x ∂μ)+eps*μ.real univ+(∫ x, F n x ∂μ) := by
    have hgc : Integrable (fun x ↦ g x+eps) μ :=
      (hgi.add (integrable_const eps)).congr (Eventually.of_forall (fun _ ↦ rfl))
    have H := integral_mono (hfi n) (hgc.add (hFi n))
      (fun x ↦ by
        simp only [Pi.add_apply]
        have hh := le_max_left (f n x-g x-eps) 0
        dsimp only [F]
        linarith)
    simp only [Pi.add_apply] at H
    rw [integral_add hgc (hFi n),
      integral_add hgi (integrable_const eps), integral_const, smul_eq_mul] at H
    simpa only [mul_comm] using H
  have hG : Tendsto (fun n ↦ (∫ x, g x ∂μ)+eps*μ.real univ+(∫ x, F n x ∂μ)) atTop
      (𝓝 ((∫ x, g x ∂μ)+eps*μ.real univ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hFzero
  have H := (limsup_le_limsup (Eventually.of_forall hpoint)
    (isCoboundedUnder_le_of_le atTop hlo) hG.isBoundedUnder_le).trans_eq hG.limsup_eq
  have heq : eps*(μ.real univ+1) = delta := div_mul_cancel₀ _ (by linarith)
  have hepsmass : eps*μ.real univ ≤ delta := by nlinarith
  exact H.trans (add_le_add (le_refl _) hepsmass)

end
end TensorPCA.MaximumIntegralProofs
