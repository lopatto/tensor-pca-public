-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.TotalVariationProofs

/-! A finite testing-error bound from a negative null mean gap.
The gap is an analytic hypothesis of the bound. -/
@[expose] public section
namespace TensorPCA.TotalVariationVarianceProofs
open MeasureTheory ProbabilityTheory Set Filter TotalVariationProofs
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem min_one_exp_le_sq {r m a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hm : m ≤ -2*a) : min 1 (Real.exp (b*r)) ≤ (r-m)^2/a^2+Real.exp (-b*a) := by
  by_cases hr : r ≤ -a
  · apply (min_le_right _ _).trans
    have h : Real.exp (b*r) ≤ Real.exp (-b*a) := by
      simpa only [mul_neg, neg_mul] using Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hb)
    have hs : 0 ≤ (r-m)^2/a^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  · apply (min_le_left _ _).trans
    have hdiff : a ≤ r-m := by linarith
    have hsq : a^2 ≤ (r-m)^2 := by nlinarith
    have hratio : 1 ≤ (r-m)^2/a^2 :=
      (le_div_iff₀ (sq_pos_of_pos ha)).mpr (by simpa only [one_mul] using hsq)
    linarith [Real.exp_pos (-b*a)]

theorem integrable_deficit {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun y ↦ max (1-Model.likelihoodRatio N k lam y) 0) (Model.noiseLaw N k) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_const.sub (GaussianChannelProofs.measurable_likelihoodRatio N k lam)).max
      measurable_const).aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by
    simp only [Pi.sub_apply]
    linarith [GaussianChannelProofs.likelihoodRatio_pos hN lam y]) zero_le_one

theorem min_likelihood_eq_one_sub_deficit (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) :
    min 1 (Model.likelihoodRatio N k lam y) =
      1-max (1-Model.likelihoodRatio N k lam y) 0 := by
  by_cases hy : Model.likelihoodRatio N k lam y ≤ 1
  · rw [min_eq_right hy, max_eq_left (by linarith)]
    ring
  · rw [min_eq_left (le_of_not_ge hy), max_eq_right (by linarith)]
    ring

theorem integral_min_likelihood {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ y, min 1 (Model.likelihoodRatio N k lam y) ∂Model.noiseLaw N k) =
      1-Model.testingDistance N k lam := by
  simp_rw [min_likelihood_eq_one_sub_deficit]
  rw [integral_sub (integrable_const _) (integrable_deficit hN lam), integral_const,
    probReal_univ, one_smul, ← testingDistance_eq_integral_deficit hN lam]

theorem nullNormalizedLogVariance_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun y ↦ (Statistical.nullLogLikelihood N k lam y/(N : ℝ)-
      Statistical.nullNormalizedLogMean N k lam)^2) (Model.noiseLaw N k) := by
  have hf : MemLp (fun y ↦ Statistical.nullLogLikelihood N k lam y/(N : ℝ)-
      Statistical.nullNormalizedLogMean N k lam) 2 (Model.noiseLaw N k) := by
    have hc := ((nullLogLikelihood_memLp_two (k := k) hN lam).const_mul (N : ℝ)⁻¹).sub
      (memLp_const (Statistical.nullNormalizedLogMean N k lam))
    apply MemLp.ae_eq ?_ hc
    filter_upwards [] with y
    simp only [Pi.sub_apply]
    ring
  exact hf.integrable_sq

/-- Genuine finite likelihood-threshold bound. The strict negative null mean
gap is explicit; no total-variation convergence is taken as an input. -/
theorem testingDistance_variance_lower {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {a : ℝ} (ha : 0 < a)
    (hgap : Statistical.nullNormalizedLogMean N k lam ≤ -2*a) :
    1-Model.testingDistance N k lam ≤
      Statistical.nullNormalizedLogVariance N k lam/a^2+Real.exp (-(N : ℝ)*a) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmin : Integrable (fun y ↦ min 1 (Model.likelihoodRatio N k lam y))
      (Model.noiseLaw N k) := by
    apply ((integrable_const (1 : ℝ)).sub (integrable_deficit hN lam)).congr
    exact Eventually.of_forall fun y ↦ (min_likelihood_eq_one_sub_deficit N k lam y).symm
  have hsq := nullNormalizedLogVariance_integrable (k := k) hN lam
  have hdiv : Integrable (fun y ↦ (Statistical.nullLogLikelihood N k lam y/(N : ℝ)-
      Statistical.nullNormalizedLogMean N k lam)^2/a^2) (Model.noiseLaw N k) := by
    apply (hsq.mul_const (a^2)⁻¹).congr
    exact Eventually.of_forall fun y ↦ by simp only [div_eq_mul_inv]
  have hbound : ∀ y : Model.Tensor N k,
      min 1 (Model.likelihoodRatio N k lam y) ≤
        (Statistical.nullLogLikelihood N k lam y/(N : ℝ)-
          Statistical.nullNormalizedLogMean N k lam)^2/a^2+Real.exp (-(N : ℝ)*a) := by
    intro y
    have hh := min_one_exp_le_sq (r := Statistical.nullLogLikelihood N k lam y/(N : ℝ)) ha hNr.le hgap
    have heq : Real.exp ((N : ℝ)*(Statistical.nullLogLikelihood N k lam y/(N : ℝ))) =
        Model.likelihoodRatio N k lam y := by
      rw [mul_div_cancel₀ _ hNr.ne']
      exact Real.exp_log (GaussianChannelProofs.likelihoodRatio_pos hN lam y)
    simpa only [heq] using hh
  have hi := integral_mono hmin (hdiv.add (integrable_const (Real.exp (-(N : ℝ)*a)))) hbound
  simp only [Pi.add_apply] at hi
  rw [integral_min_likelihood hN lam, integral_add hdiv (integrable_const _),
    integral_div, integral_const, probReal_univ, one_smul] at hi
  exact hi


theorem exp_neg_mul_le_reciprocal {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlarge : 4/a^2 ≤ b) : Real.exp (-b*a) ≤ 1/b := by
  have hhalf : 0 ≤ b*a/2 := by positivity
  have hlin := Real.add_one_le_exp (b*a/2)
  have hsq : (b*a/2)^2 ≤ (Real.exp (b*a/2))^2 := by
    exact (sq_le_sq₀ hhalf (Real.exp_pos _).le).mpr (by linarith)
  have hexp : (Real.exp (b*a/2))^2 = Real.exp (b*a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hba : 4 ≤ b*a^2 := (div_le_iff₀ (sq_pos_of_pos ha)).mp hlarge
  have hbb : b ≤ (b*a/2)^2 := by
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hba)]
  have hbe : b ≤ Real.exp (b*a) := hbb.trans (hsq.trans_eq hexp)
  have hi := one_div_le_one_div_of_le hb hbe
  simpa only [neg_mul, Real.exp_neg, one_div] using hi

theorem testingDistance_le_one (N k : ℕ) (lam : ℝ) : Model.testingDistance N k lam ≤ 1 := by
  have h := tvDist_le_add (μ := Model.observationLaw N k 0) (ν := Model.observationLaw N k lam)
  simp only [probReal_univ] at h
  unfold Model.testingDistance
  linarith

/-- The exact finite variance contract follows from an eventual negative null
mean gap. The gap itself, and any variance limit, are not asserted here. -/
theorem finiteTVVarianceBound_of_eventual_negative_mean_gap {k : ℕ} {lam a : ℝ}
    (ha : 0 < a)
    (hgap : ∀ᶠ n : ℕ in atTop, Statistical.nullNormalizedLogMean (n+1) k lam ≤ -2*a) :
    Statistical.FiniteTVVarianceBound k lam ((a^2)⁻¹) := by
  have hncast : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_mono (fun n : ℕ ↦ (by linarith : (n : ℝ) ≤ (n : ℝ)+1))
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ n : ℕ in atTop, 4/a^2 ≤ ((n+1 : ℕ) : ℝ) :=
    hncast.eventually_ge_atTop _
  filter_upwards [hgap, hlarge] with n hm hn
  refine ⟨?_, testingDistance_le_one (n+1) k lam⟩
  have hlower := testingDistance_variance_lower (Nat.succ_pos n) lam ha hm
  have he := exp_neg_mul_le_reciprocal ha
    (show (0 : ℝ) < ((n+1 : ℕ) : ℝ) by positivity) hn
  rw [Nat.cast_add, Nat.cast_one] at he
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] at hlower he ⊢
  nlinarith

/-- A strictly negative actual null mean limit supplies the required finite
testing coefficient; no testing-distance or variance convergence is assumed. -/
theorem exists_finiteTVVarianceBound_of_negative_mean_limit {k : ℕ} {lam m : ℝ}
    (hm : m < 0)
    (hmean : Tendsto (fun n : ℕ ↦ Statistical.nullNormalizedLogMean (n+1) k lam)
      atTop (𝓝 m)) :
    ∃ C : ℝ, 0 < C ∧ Statistical.FiniteTVVarianceBound k lam C := by
  let a : ℝ := -m/4
  have ha : 0 < a := by dsimp [a]; linarith
  have hm_lt : m < -2*a := by dsimp [a]; linarith
  have hgap : ∀ᶠ n : ℕ in atTop,
      Statistical.nullNormalizedLogMean (n+1) k lam ≤ -2*a :=
    (hmean.eventually (Iio_mem_nhds hm_lt)).mono (fun _ hn ↦ hn.le)
  exact ⟨(a^2)⁻¹, inv_pos.mpr (sq_pos_of_pos ha),
    finiteTVVarianceBound_of_eventual_negative_mean_gap ha hgap⟩

end
end TensorPCA.TotalVariationVarianceProofs
