-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PlantedLikelihoodProofs
public import TensorPCA.ScalarBayesianProofs

/-! Supercritical testing from the Bayesian free-energy value. The
finite testing inequality uses the planted normalized likelihood variance,
without a physical maximum or thermal Parisi value theorem. -/
@[expose] public section
namespace TensorPCA.BayesianDetectionProofs
open MeasureTheory ProbabilityTheory Set Filter PlantedLikelihoodProofs
open TotalVariationProofs TotalVariationVarianceProofs ScalarPhiProofs ScalarSelectionProofs
open ScalarStationaryProofs ScalarThresholdProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mul_min_one_inv {L : ℝ} (hL : 0 < L) : L*min 1 L⁻¹ = min 1 L := by
  rw [mul_min_of_nonneg _ _ hL.le,mul_one,mul_inv_cancel₀ hL.ne']
  exact min_comm _ _

/-- The overlap of the null and alternative laws is also the alternative
expectation of the inverse likelihood truncated at one. -/
theorem integral_planted_inverse_likelihood {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, min 1 (Model.likelihoodRatio N k lam (Model.observation lam z))⁻¹
      ∂Model.experimentLaw N k) = 1-Model.testingDistance N k lam := by
  have hG : Measurable (fun y : Model.Tensor N k ↦ min 1 (Model.likelihoodRatio N k lam y)⁻¹) :=
    measurable_const.min (GaussianChannelProofs.measurable_likelihoodRatio N k lam).inv
  calc
    _ = ∫ y, min 1 (Model.likelihoodRatio N k lam y)⁻¹ ∂Model.observationLaw N k lam := by
      symm
      exact integral_map (Model.measurable_observation N k lam).aemeasurable hG.aestronglyMeasurable
    _ = ∫ y, Model.likelihoodRatio N k lam y*min 1 (Model.likelihoodRatio N k lam y)⁻¹
        ∂Model.noiseLaw N k := by
      rw [GaussianChannelProofs.observationLaw_eq_withDensity hN lam,
        integral_withDensity_eq_integral_toReal_smul
          (GaussianChannelProofs.measurable_likelihoodRatio N k lam).ennreal_ofReal
          (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        dsimp only
        rw [ENNReal.toReal_ofReal (GaussianChannelProofs.likelihoodRatio_pos hN lam y).le,smul_eq_mul]
    _ = ∫ y, min 1 (Model.likelihoodRatio N k lam y) ∂Model.noiseLaw N k :=
      integral_congr_ae (.of_forall fun y ↦ mul_min_one_inv (GaussianChannelProofs.likelihoodRatio_pos hN lam y))
    _ = _ := integral_min_likelihood hN lam

theorem planted_inverse_likelihood_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z ↦ min 1 (Model.likelihoodRatio N k lam (Model.observation lam z))⁻¹)
      (Model.experimentLaw N k) := by
  have hG : Measurable (fun z ↦ min 1 (Model.likelihoodRatio N k lam (Model.observation lam z))⁻¹) :=
    (measurable_const.min (GaussianChannelProofs.measurable_likelihoodRatio N k lam).inv).comp
      (Model.measurable_observation N k lam)
  apply (integrable_const (1 : ℝ)).mono' hG.aestronglyMeasurable
  exact .of_forall fun z ↦ by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_min zero_le_one
      (inv_nonneg.mpr (GaussianChannelProofs.likelihoodRatio_pos hN lam _).le))]
    exact min_le_left _ _

/-- A positive actual planted mean gives a finite testing bound. The null
normalization E_0[L]=1 is retained in the likelihood change of measure above. -/
theorem testingDistance_lower_of_positive_planted_mean {N k : ℕ} (hN : 0 < N)
    {lam : ℝ} (hlam : 0 ≤ lam) {a : ℝ} (ha : 0 < a)
    (hgap : 2*a ≤ Statistical.sphericalBayesFreeEnergy N k (lam^2)) :
    1-Model.testingDistance N k lam ≤ lam^2/(N : ℝ)/a^2+Real.exp (-(N : ℝ)*a) := by
  let m := Statistical.sphericalBayesFreeEnergy N k (lam^2)
  have hsq := plantedLogLikelihood_centered_sq_integrable (k := k) hN lam m
  have hdiv : Integrable (fun z ↦ (normalizedLogLikelihood N k lam (Model.observation lam z)-m)^2/a^2)
      (Model.experimentLaw N k) := hsq.div_const _
  have hbound (z : Model.Vector N × Model.Tensor N k) :
      min 1 (Model.likelihoodRatio N k lam (Model.observation lam z))⁻¹ ≤
        (normalizedLogLikelihood N k lam (Model.observation lam z)-m)^2/a^2+Real.exp (-(N : ℝ)*a) := by
    have H := min_one_exp_le_sq (r := -normalizedLogLikelihood N k lam (Model.observation lam z))
      (m := -m) ha (Nat.cast_nonneg N) (by dsimp [m]; linarith)
    have he : Real.exp ((N : ℝ)*(-normalizedLogLikelihood N k lam (Model.observation lam z))) =
        (Model.likelihoodRatio N k lam (Model.observation lam z))⁻¹ := by
      rw [mul_neg,Real.exp_neg,normalizedLogLikelihood,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
      rw [Statistical.nullLogLikelihood,Real.exp_log (GaussianChannelProofs.likelihoodRatio_pos hN lam _)]
    rw [he] at H
    convert H using 1; ring
  have H := integral_mono (planted_inverse_likelihood_integrable hN lam)
    (hdiv.add (integrable_const (Real.exp (-(N : ℝ)*a)))) hbound
  simp only [Pi.add_apply] at H
  rw [integral_planted_inverse_likelihood hN lam,integral_add hdiv (integrable_const _),
    integral_div,integral_const,probReal_univ,one_smul] at H
  exact H.trans (add_le_add (div_le_div_of_nonneg_right
    (plantedLogLikelihood_variance_le (k := k) hN hlam) (sq_nonneg a)) (le_refl _))

theorem testingDistance_tendsto_one_of_positive_bayesian_mean {k : ℕ} {lam L : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 < L)
    (hmean : Tendsto (fun n : ℕ ↦ Statistical.sphericalBayesFreeEnergy (n+1) k (lam^2))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ Model.testingDistance (n+1) k lam) atTop (𝓝 1) := by
  let a := L/4
  have ha : 0 < a := by dsimp [a]; positivity
  have hgap : ∀ᶠ n : ℕ in atTop, 2*a ≤ Statistical.sphericalBayesFreeEnergy (n+1) k (lam^2) :=
    (hmean.eventually (eventually_ge_nhds (by dsimp [a]; linarith : 2*a < L)))
  have hncast : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ by exact_mod_cast Nat.le_succ n)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have herror : Tendsto (fun n : ℕ ↦ lam^2/((n+1 : ℕ) : ℝ)/a^2+
      Real.exp (-((n+1 : ℕ) : ℝ)*a)) atTop (𝓝 0) := by
    have h1 := (hncast.const_div_atTop (lam^2)).div_const (a^2)
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hncast.atTop_mul_const ha)
    simpa only [Function.comp_def,neg_mul,zero_div,zero_add] using h1.add h2
  have hlo : Tendsto (fun n : ℕ ↦ 1-(lam^2/((n+1 : ℕ) : ℝ)/a^2+
      Real.exp (-((n+1 : ℕ) : ℝ)*a))) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub herror
  apply hlo.squeeze' tendsto_const_nhds
  · filter_upwards [hgap] with n hn
    have H := testingDistance_lower_of_positive_planted_mean (Nat.succ_pos n) hlam ha hn
    linarith
  · exact .of_forall fun n ↦ testingDistance_le_one (n+1) k lam

theorem bayesianLimit_pos_supercritical (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) : 0 < Statistical.bayesianLimit k (lam^2) := by
  have hl : 0 < lam := (ScalarStaticRatioProofs.lambdaC_pos k hk).trans hlam
  rw [Statistical.bayesianLimit,Real.sqrt_sq hl.le,ScalarBayesianProofs.sSup_phi_eq_f_qStar k hk hl]
  have hcrit := ScalarStaticRatioProofs.criticalOverlap_mem_Ioo k hk
  have H := (qStar_isScalarMaximizer k hk hl.le).2 (ScalarStaticRatioProofs.criticalOverlap k) ⟨hcrit.1.le,hcrit.2⟩
  exact mul_pos (by norm_num) ((f_criticalOverlap_pos k hk hlam).trans_le H)

/-- This supercritical branch needs only the genuine Bayesian value theorem.
Physical ground-state and thermal Parisi formula obligations are bypassed. -/
theorem testingDistance_supercritical_of_bayesian_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) :
    Tendsto (fun n : ℕ ↦ Model.testingDistance (n+1) k lam) atTop (𝓝 1) := by
  have hl : 0 < lam := (ScalarStaticRatioProofs.lambdaC_pos k hk).trans hlam
  exact testingDistance_tendsto_one_of_positive_bayesian_mean hl.le
    (bayesianLimit_pos_supercritical k hk hlam) (hvalues (lam^2) (sq_pos_of_pos hl))

end
end TensorPCA.BayesianDetectionProofs
