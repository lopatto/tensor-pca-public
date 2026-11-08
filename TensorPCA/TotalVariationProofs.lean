-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianChannelProofs
public import TensorPCA.Statistical
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-! Finite likelihood-to-total-variation inequalities for the experiment. -/
@[expose] public section
namespace TensorPCA.TotalVariationProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem observationLaw_zero (N k : ℕ) : Model.observationLaw N k 0 = Model.noiseLaw N k := by
  unfold Model.observationLaw
  have hobs : Model.observation (N := N) (k := k) 0 = Prod.snd := by
    funext z
    simp [Model.observation]
  rw [hobs]
  exact (measurePreserving_snd (μ := Model.spherePrior N) (ν := Model.noiseLaw N k)).map_eq

theorem nullLogLikelihood_measurable (N k : ℕ) (lam : ℝ) :
    Measurable (Statistical.nullLogLikelihood N k lam) :=
  (GaussianChannelProofs.measurable_likelihoodRatio N k lam).log

theorem abs_nullLogLikelihood_le {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) :
    |Statistical.nullLogLikelihood N k lam y| ≤
      |lam*Real.sqrt N| * ‖y‖+(N : ℝ)*lam^2/2 := by
  have hp := GaussianChannelProofs.likelihoodRatio_pos hN lam y
  have hlo := Real.log_le_log (Real.exp_pos _)
    (GaussianChannelProofs.likelihoodRatio_lower hN lam y)
  have hhi := Real.log_le_log hp (GaussianChannelProofs.likelihoodRatio_le hN lam y)
  rw [Real.log_exp] at hlo hhi
  unfold Statistical.nullLogLikelihood
  rw [abs_le]
  constructor <;> nlinarith [show (0 : ℝ) ≤ N by positivity, sq_nonneg lam]

theorem nullLogLikelihood_memLp_two {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    MemLp (Statistical.nullLogLikelihood N k lam) 2 (Model.noiseLaw N k) := by
  have hnorm : MemLp (fun y : Model.Tensor N k ↦ ‖y‖) 2 (Model.noiseLaw N k) := by
    change MemLp (fun y : Model.Tensor N k ↦ ‖y‖) 2 (stdGaussian (Model.Tensor N k))
    exact (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) 2 (by norm_num)).norm
  have hb := (hnorm.const_mul |lam*Real.sqrt N|).add
    (memLp_const ((N : ℝ)*lam^2/2))
  apply hb.mono' (nullLogLikelihood_measurable N k lam).aestronglyMeasurable
  filter_upwards [] with y
  simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_nullLogLikelihood_le hN lam y


theorem testingDistance_eq_half_integral {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Model.testingDistance N k lam =
      (∫ y, |1-Model.likelihoodRatio N k lam y| ∂Model.noiseLaw N k)/2 := by
  have hac : Model.observationLaw N k lam ≪ Model.noiseLaw N k := by
    rw [GaussianChannelProofs.observationLaw_eq_withDensity hN lam]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (Model.observationLaw N k lam).rnDeriv (Model.noiseLaw N k) =ᵐ[Model.noiseLaw N k]
      (fun y ↦ ENNReal.ofReal (Model.likelihoodRatio N k lam y)) := by
    rw [GaussianChannelProofs.observationLaw_eq_withDensity hN lam]
    exact Measure.rnDeriv_withDensity _
      (GaussianChannelProofs.measurable_likelihoodRatio N k lam).ennreal_ofReal
  unfold Model.testingDistance
  rw [observationLaw_zero, tvDist_comm, tvDist_eq_integral_abs_rnDeriv_of_ac hac]
  congr 1
  apply integral_congr_ae
  filter_upwards [hrn] with y hy
  simp only [hy, ENNReal.toReal_ofReal (GaussianChannelProofs.likelihoodRatio_pos hN lam y).le]

theorem testingDistance_eq_integral_deficit {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Model.testingDistance N k lam =
      ∫ y, max (1-Model.likelihoodRatio N k lam y) 0 ∂Model.noiseLaw N k := by
  let L := Model.likelihoodRatio N k lam
  have hi : Integrable L (Model.noiseLaw N k) := GaussianChannelProofs.integrable_likelihoodRatio hN lam
  have hd : Integrable (fun y ↦ max (1-L y) 0) (Model.noiseLaw N k) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_const.sub (GaussianChannelProofs.measurable_likelihoodRatio N k lam)).max
        measurable_const).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by dsimp [L]; linarith [GaussianChannelProofs.likelihoodRatio_pos hN lam y])
      zero_le_one
  have ha : (fun y ↦ |1-L y|) = fun y ↦ (L y-1)+2*max (1-L y) 0 := by
    funext y
    by_cases hy : 1 ≤ L y
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
      ring
  rw [testingDistance_eq_half_integral hN lam]
  change (∫ y, |1-L y| ∂Model.noiseLaw N k)/2 = _
  have hs : Integrable (fun y ↦ L y-1) (Model.noiseLaw N k) := by
    apply (hi.sub (integrable_const (1 : ℝ))).congr
    filter_upwards [] with y
    rfl
  rw [ha, integral_add hs (hd.const_mul _),
    integral_sub hi (integrable_const _), integral_const_mul,
    GaussianChannelProofs.integral_likelihoodRatio_eq_one hN lam]
  simp [L]

theorem deficit_le_abs_log {x : ℝ} (hx : 0 < x) : max (1-x) 0 ≤ |Real.log x| := by
  apply max_le
  · have he := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx] at he
    linarith [neg_abs_le (Real.log x)]
  · exact abs_nonneg _

theorem testingDistance_le_integral_abs_log {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Model.testingDistance N k lam ≤
      ∫ y, |Statistical.nullLogLikelihood N k lam y| ∂Model.noiseLaw N k := by
  rw [testingDistance_eq_integral_deficit hN lam]
  have hd : Integrable (fun y ↦ max (1-Model.likelihoodRatio N k lam y) 0)
      (Model.noiseLaw N k) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_const.sub (GaussianChannelProofs.measurable_likelihoodRatio N k lam)).max
        measurable_const).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by
      simp only [Pi.sub_apply]
      linarith [GaussianChannelProofs.likelihoodRatio_pos hN lam y]) zero_le_one
  apply integral_mono_ae hd ((nullLogLikelihood_memLp_two hN lam).integrable (by norm_num)).abs
  exact Eventually.of_forall (fun y ↦ deficit_le_abs_log (GaussianChannelProofs.likelihoodRatio_pos hN lam y))


theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ y, |f y| ∂μ) ≤ Real.sqrt (∫ y, (f y)^2 ∂μ) := by
  have habs : MemLp (fun y ↦ |f y|) 2 μ := by simpa only [Real.norm_eq_abs] using hf.norm
  have hpq : Real.HolderConjugate (2 : ℝ) 2 := by
    norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun y ↦ |f y|) (g := fun _y ↦ (1 : ℝ))
    (Eventually.of_forall fun y ↦ abs_nonneg (f y))
    (Eventually.of_forall fun _y ↦ zero_le_one)
    (by simpa only [ENNReal.ofReal_ofNat] using habs) (memLp_const (1 : ℝ))
  simpa only [mul_one, Real.rpow_two, sq_abs, Real.one_rpow, integral_const,
    probReal_univ, one_smul, ← Real.sqrt_eq_rpow, one_pow, Real.sqrt_one] using hh

/-- The paper's finite null-log-likelihood moment bound, for the actual
probability-normalized testing distance and without asymptotic inputs. -/
theorem finiteTVMomentBound (k : ℕ) (lam : ℝ) : Statistical.FiniteTVMomentBound k lam := by
  intro n
  constructor
  · exact div_nonneg tvDist_nonneg (by norm_num)
  · exact (testingDistance_le_integral_abs_log (Nat.succ_pos n) lam).trans
      (integral_abs_le_sqrt_integral_sq (Model.noiseLaw (n+1) k)
        (nullLogLikelihood_memLp_two (Nat.succ_pos n) lam))

end
end TensorPCA.TotalVariationProofs
