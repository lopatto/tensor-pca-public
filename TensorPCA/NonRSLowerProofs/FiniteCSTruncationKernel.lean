-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSDefinitions

/-! Probability-law truncation toward a closed overlap cutoff. Its profile gain is
constant below the cutoff and is bounded by that same constant everywhere. No cutoff
or mass-tail hypothesis is built into the trial space.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

def truncateOverlap (R : Overlap) (q : Overlap) : Overlap :=
  ⟨min (q : ℝ) (R : ℝ), le_min q.property.1 R.property.1,
    (min_le_left _ _).trans q.property.2⟩

theorem continuous_truncateOverlap (R : Overlap) : Continuous (truncateOverlap R) := by
  unfold truncateOverlap
  fun_prop

def truncateTrial (nu : Trial) (R : Overlap) : Trial := nu.map (truncateOverlap R)

def tailDisplacement (R : Overlap) : C(Overlap, ℝ) :=
  ⟨fun q => max ((q : ℝ)-(R : ℝ)) 0, by fun_prop⟩

def truncationGain (beta : ℝ) (nu : Trial) (R : Overlap) : ℝ :=
  beta * ∫ q, tailDisplacement R q ∂(nu : Measure Overlap)

theorem tailDisplacement_nonneg (R q : Overlap) : 0 ≤ tailDisplacement R q :=
  le_max_right _ _

theorem tailDisplacement_le_one (R q : Overlap) : tailDisplacement R q ≤ 1 :=
  max_le (by linarith [q.property.2, R.property.1]) zero_le_one

theorem tailDisplacement_integrable (nu : Trial) (R : Overlap) :
    Integrable (tailDisplacement R) (nu : Measure Overlap) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact .of_forall fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tailDisplacement_nonneg R q)]
    exact tailDisplacement_le_one R q

theorem truncationGain_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) (nu : Trial) (R : Overlap) :
    0 ≤ truncationGain beta nu R :=
  mul_nonneg hbeta (integral_nonneg (tailDisplacement_nonneg R))

theorem kernel_truncate_gain_eq {t : ℝ} (R q : Overlap) (ht : t ≤ (R : ℝ)) :
    kernel t (truncateOverlap R q)-kernel t q = tailDisplacement R q := by
  change (1-max t (min (q : ℝ) (R : ℝ)))-(1-max t (q : ℝ)) = max ((q : ℝ)-(R : ℝ)) 0
  by_cases hq : (q : ℝ) ≤ (R : ℝ)
  · rw [min_eq_left hq, sub_self, max_eq_right (sub_nonpos.mpr hq)]
  · have hRq := le_of_not_ge hq
    rw [min_eq_right hRq, max_eq_right ht, max_eq_right (ht.trans hRq),
      max_eq_left (sub_nonneg.mpr hRq)]
    ring

theorem kernel_truncate_gain_bounds (R q : Overlap) (t : ℝ) :
    0 ≤ kernel t (truncateOverlap R q)-kernel t q ∧
      kernel t (truncateOverlap R q)-kernel t q ≤ tailDisplacement R q := by
  change 0 ≤ (1-max t (min (q : ℝ) (R : ℝ)))-(1-max t (q : ℝ)) ∧
    (1-max t (min (q : ℝ) (R : ℝ)))-(1-max t (q : ℝ)) ≤ max ((q : ℝ)-(R : ℝ)) 0
  constructor
  · have H := max_le_max_left t (min_le_left (q : ℝ) (R : ℝ))
    linarith
  · by_cases ht : t ≤ (R : ℝ)
    · exact (kernel_truncate_gain_eq R q ht).le
    · have hRt := le_of_not_ge ht
      rw [max_eq_left ((min_le_right _ _).trans hRt)]
      by_cases hqt : (q : ℝ) ≤ t
      · rw [max_eq_left hqt]
        simpa only [sub_self] using le_max_right ((q : ℝ)-(R : ℝ)) 0
      · have htq := le_of_not_ge hqt
        rw [max_eq_right htq]
        have H := le_max_left ((q : ℝ)-(R : ℝ)) 0
        linarith

theorem kernel_truncate_terminal {t : ℝ} (R q : Overlap) (ht : (R : ℝ) ≤ t) :
    kernel t (truncateOverlap R q) = 1-t := by
  change 1-max t (min (q : ℝ) (R : ℝ)) = 1-t
  rw [max_eq_left ((min_le_right _ _).trans ht)]

theorem profile_truncate_integral (beta t : ℝ) (nu : Trial) (R : Overlap) :
    profile beta (truncateTrial nu R) t =
      beta * ∫ q, kernel t (truncateOverlap R q) ∂(nu : Measure Overlap) := by
  unfold profile truncateTrial
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_truncateOverlap R).measurable.aemeasurable
      (by fun_prop)]

theorem kernel_truncate_integrable (nu : Trial) (R : Overlap) (t : ℝ) :
    Integrable (fun q => kernel t (truncateOverlap R q)) (nu : Measure Overlap) := by
  exact (integrable_map_measure (by fun_prop)
    (continuous_truncateOverlap R).measurable.aemeasurable).mp
      (kernel_integrable (truncateTrial nu R : Measure Overlap) t)

theorem profile_truncate_gain_eq (beta : ℝ) (nu : Trial) (R : Overlap)
    {t : ℝ} (ht : t ≤ (R : ℝ)) :
    profile beta (truncateTrial nu R) t-profile beta nu t = truncationGain beta nu R := by
  rw [profile_truncate_integral]
  unfold profile truncationGain
  rw [← mul_sub, ← integral_sub (kernel_truncate_integrable nu R t)
    (kernel_integrable (nu : Measure Overlap) t)]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun q => kernel_truncate_gain_eq R q ht

theorem profile_truncate_gain_bounds {beta : ℝ} (hbeta : 0 ≤ beta) (nu : Trial)
    (R : Overlap) (t : ℝ) :
    0 ≤ profile beta (truncateTrial nu R) t-profile beta nu t ∧
      profile beta (truncateTrial nu R) t-profile beta nu t ≤ truncationGain beta nu R := by
  rw [profile_truncate_integral]
  unfold profile truncationGain
  rw [← mul_sub, ← integral_sub (kernel_truncate_integrable nu R t)
    (kernel_integrable (nu : Measure Overlap) t)]
  constructor
  · exact mul_nonneg hbeta (integral_nonneg (fun q => (kernel_truncate_gain_bounds R q t).1))
  · apply mul_le_mul_of_nonneg_left _ hbeta
    exact integral_mono ((kernel_truncate_integrable nu R t).sub
      (kernel_integrable (nu : Measure Overlap) t)) (tailDisplacement_integrable nu R)
      (fun q => (kernel_truncate_gain_bounds R q t).2)

theorem profile_truncate_terminal (beta : ℝ) (nu : Trial) (R : Overlap)
    {t : ℝ} (ht : (R : ℝ) ≤ t) :
    profile beta (truncateTrial nu R) t = beta*(1-t) := by
  rw [profile_truncate_integral]
  have heq : (fun q => kernel t (truncateOverlap R q)) = (fun _ : Overlap => 1-t) :=
    funext (fun q => kernel_truncate_terminal R q ht)
  rw [heq, integral_const, probReal_univ, one_smul]

theorem truncationGain_eq_zero_iff {beta : ℝ} (hbeta : 0 < beta) (nu : Trial) (R : Overlap) :
    truncationGain beta nu R = 0 ↔ (nu : Measure Overlap) {q | (R : ℝ) < (q : ℝ)} = 0 := by
  rw [truncationGain, mul_eq_zero, or_iff_right hbeta.ne']
  rw [integral_eq_zero_iff_of_nonneg (tailDisplacement_nonneg R)
    (tailDisplacement_integrable nu R)]
  change (∀ᵐ q ∂(nu : Measure Overlap), tailDisplacement R q=0) ↔ _
  rw [ae_iff]
  have heq : {q : Overlap | ¬tailDisplacement R q=0} =
      {q : Overlap | (R : ℝ)<(q : ℝ)} := by
    ext q
    change ¬max ((q : ℝ)-(R : ℝ)) 0=0 ↔ (R : ℝ)<(q : ℝ)
    rw [max_eq_right_iff]
    simp only [sub_nonpos, not_le]
  rw [heq]


end
end TensorPCA.NonRSLowerProofs.FiniteCS
