-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPriorTransferProofs

/-!
# Gaussian-mixture free-energy stability

Finite coupling relative entropy proves all log-likelihood integrability.
Only the spherical reference channel will need a bounded signal map.
-/
@[expose] public section

namespace TensorPCA.GaussianMixtureStabilityProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
open scoped ENNReal RealInnerProductSpace

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
theorem mixtureLaw_zero (mu : Measure Omega) [IsProbabilityMeasure mu] :
    mixtureLaw mu (fun _ ↦ (0 : E)) = stdGaussian E := by
  simp [mixtureLaw, Measure.map_snd_prod]

theorem mixtureLaw_absolutelyContinuous (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : mixtureLaw mu F ≪ stdGaussian E := by
  rw [mixtureLaw_eq_withDensity mu F hF]
  exact withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_mixtureLaw (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : stdGaussian E ≪ mixtureLaw mu F := by
  rw [mixtureLaw_eq_withDensity mu F hF]
  exact withDensity_absolutelyContinuous' (measurable_mixtureLikelihood mu F hF).ennreal_ofReal.aemeasurable
    (.of_forall fun y ↦ (ENNReal.ofReal_pos.mpr (mixtureLikelihood_pos mu F hF y)).ne')

theorem mixtureLaw_llr_noise (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    llr (mixtureLaw mu F) (stdGaussian E) =ᵐ[mixtureLaw mu F] fun y ↦ Real.log (mixtureLikelihood mu F y) := by
  have h := Measure.rnDeriv_withDensity (stdGaussian E) (measurable_mixtureLikelihood mu F hF).ennreal_ofReal
  rw [← mixtureLaw_eq_withDensity mu F hF] at h
  filter_upwards [h.filter_mono (mixtureLaw_absolutelyContinuous mu F hF).ae_le] with y hy
  rw [llr, hy, ENNReal.toReal_ofReal (mixtureLikelihood_pos mu F hF y).le]

theorem mixtureLaw_llr (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G) :
    llr (mixtureLaw mu F) (mixtureLaw mu G) =ᵐ[mixtureLaw mu F] fun y ↦
      Real.log (mixtureLikelihood mu F y) - Real.log (mixtureLikelihood mu G y) := by
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  have hright := Measure.rnDeriv_withDensity_right (mixtureLaw mu F) (stdGaussian E)
    (measurable_mixtureLikelihood mu G hG).ennreal_ofReal.aemeasurable
    (.of_forall fun y ↦ (ENNReal.ofReal_pos.mpr (mixtureLikelihood_pos mu G hG y)).ne')
    (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)
  have hleft := Measure.rnDeriv_withDensity (stdGaussian E) (measurable_mixtureLikelihood mu F hF).ennreal_ofReal
  rw [← mixtureLaw_eq_withDensity mu F hF] at hleft
  rw [← mixtureLaw_eq_withDensity mu G hG] at hright
  filter_upwards [hleft.filter_mono (mixtureLaw_absolutelyContinuous mu F hF).ae_le,
    hright.filter_mono (mixtureLaw_absolutelyContinuous mu F hF).ae_le] with y hl hr
  rw [llr, hr, hl, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mixtureLikelihood_pos mu F hF y).le,
    ENNReal.toReal_ofReal (mixtureLikelihood_pos mu G hG y).le,
    Real.log_mul (inv_ne_zero (mixtureLikelihood_pos mu G hG y).ne')
      (mixtureLikelihood_pos mu F hF y).ne', Real.log_inv]
  ring

theorem klDiv_mixtureLaw_ne_top (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hD : MemLp (fun x ↦ F x-G x) 2 mu) : klDiv (mixtureLaw mu F) (mixtureLaw mu G) ≠ ∞ :=
  (lt_of_le_of_lt (klDiv_mixtureLaw_le mu F G hF hG hD) ENNReal.ofReal_lt_top).ne

theorem integrable_mixtureLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu) :
    Integrable (fun y ↦ Real.log (mixtureLikelihood mu F y)) (mixtureLaw mu F) := by
  have hKL := klDiv_mixtureLaw_ne_top mu F (fun _ ↦ (0 : E)) hF measurable_const
    (by simpa using hF2)
  rw [mixtureLaw_zero] at hKL
  exact (klDiv_ne_top_iff.mp hKL).2.congr (mixtureLaw_llr_noise mu F hF)

theorem mixtureFreeEnergy_eq_integral (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    mixtureFreeEnergy mu F = ∫ y, Real.log (mixtureLikelihood mu F y) ∂mixtureLaw mu F := by
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  rw [mixtureFreeEnergy, toReal_klDiv_of_measure_eq (mixtureLaw_absolutelyContinuous mu F hF) (by simp)]
  exact integral_congr_ae (mixtureLaw_llr_noise mu F hF)

theorem integrable_referenceLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 mu) (hG2 : MemLp G 2 mu) :
    Integrable (fun y ↦ Real.log (mixtureLikelihood mu G y)) (mixtureLaw mu F) := by
  have hD : MemLp (fun x ↦ F x-G x) 2 mu := hF2.sub hG2
  have hllr := (klDiv_ne_top_iff.mp (klDiv_mixtureLaw_ne_top mu F G hF hG hD)).2
  apply ((integrable_mixtureLogLikelihood mu F hF hF2).sub hllr).congr
  filter_upwards [mixtureLaw_llr mu F G hF hG] with y hy
  dsimp only [Pi.sub_apply]
  rw [hy]
  ring

theorem mixtureFreeEnergy_sub_eq (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 mu) (hG2 : MemLp G 2 mu) :
    mixtureFreeEnergy mu F - mixtureFreeEnergy mu G =
      (klDiv (mixtureLaw mu F) (mixtureLaw mu G)).toReal +
      ((∫ y, Real.log (mixtureLikelihood mu G y) ∂mixtureLaw mu F) -
        ∫ y, Real.log (mixtureLikelihood mu G y) ∂mixtureLaw mu G) := by
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  have : IsProbabilityMeasure (mixtureLaw mu G) := mixtureLaw_probability mu G hG
  rw [toReal_klDiv_of_measure_eq ((mixtureLaw_absolutelyContinuous mu F hF).trans
    (absolutelyContinuous_mixtureLaw mu G hG)) (by simp),
    integral_congr_ae (mixtureLaw_llr mu F G hF hG),
    integral_sub (integrable_mixtureLogLikelihood mu F hF hF2)
      (integrable_referenceLogLikelihood mu F G hF hG hF2 hG2),
    mixtureFreeEnergy_eq_integral mu F hF, mixtureFreeEnergy_eq_integral mu G hG]
  ring

theorem log_mixtureLikelihood_sub_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (G : Omega → E) (hG : Measurable G) {K : ℝ}
    (hb : ∀ᵐ x ∂mu, ‖G x‖ ≤ K) (y z : E) :
    Real.log (mixtureLikelihood mu G y) - Real.log (mixtureLikelihood mu G z) ≤ K * ‖y-z‖ := by
  have hpoint : ∀ᵐ x ∂mu, mixtureWeight (G x) y ≤
      Real.exp (K * ‖y-z‖) * mixtureWeight (G x) z := by
    filter_upwards [hb] with x hx
    unfold mixtureWeight
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hi := (real_inner_le_norm (G x) (y-z)).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg (y-z)))
    rw [inner_sub_right] at hi
    linarith
  have hi := integral_mono_ae (integrable_mixtureWeight mu G hG y)
    ((integrable_mixtureWeight mu G hG z).const_mul (Real.exp (K * ‖y-z‖))) hpoint
  rw [integral_const_mul] at hi
  have hl := Real.log_le_log (mixtureLikelihood_pos mu G hG y) hi
  change Real.log (mixtureLikelihood mu G y) ≤
    Real.log (Real.exp (K * ‖y-z‖) * mixtureLikelihood mu G z) at hl
  rw [Real.log_mul (Real.exp_ne_zero _) (mixtureLikelihood_pos mu G hG z).ne', Real.log_exp] at hl
  linarith

theorem abs_log_mixtureLikelihood_sub_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (G : Omega → E) (hG : Measurable G) {K : ℝ}
    (hb : ∀ᵐ x ∂mu, ‖G x‖ ≤ K) (y z : E) :
    |Real.log (mixtureLikelihood mu G y) - Real.log (mixtureLikelihood mu G z)| ≤ K * ‖y-z‖ := by
  have h1 := log_mixtureLikelihood_sub_le mu G hG hb y z
  have h2 := log_mixtureLikelihood_sub_le mu G hG hb z y
  rw [norm_sub_rev] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem reference_log_integral_sub_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 mu) (hG2 : MemLp G 2 mu) {K : ℝ}
    (hb : ∀ᵐ x ∂mu, ‖G x‖ ≤ K) :
    |(∫ y, Real.log (mixtureLikelihood mu G y) ∂mixtureLaw mu F) -
      ∫ y, Real.log (mixtureLikelihood mu G y) ∂mixtureLaw mu G| ≤
      K * ∫ x, ‖F x-G x‖ ∂mu := by
  have hlog : Measurable (fun y ↦ Real.log (mixtureLikelihood mu G y)) :=
    (measurable_mixtureLikelihood mu G hG).log
  have hObsF : Measurable (fun z : Omega × E ↦ F z.1 + z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  have hObsG : Measurable (fun z : Omega × E ↦ G z.1 + z.2) :=
    (hG.comp measurable_fst).add measurable_snd
  have hiF : Integrable (fun z : Omega × E ↦ Real.log (mixtureLikelihood mu G (F z.1+z.2)))
      (mu.prod (stdGaussian E)) :=
    (integrable_map_measure hlog.aestronglyMeasurable hObsF.aemeasurable).mp
      (integrable_referenceLogLikelihood mu F G hF hG hF2 hG2)
  have hiG : Integrable (fun z : Omega × E ↦ Real.log (mixtureLikelihood mu G (G z.1+z.2)))
      (mu.prod (stdGaussian E)) :=
    (integrable_map_measure hlog.aestronglyMeasurable hObsG.aemeasurable).mp
      (integrable_mixtureLogLikelihood mu G hG hG2)
  have hD : MemLp (fun x ↦ F x-G x) 2 mu := hF2.sub hG2
  simp only [mixtureLaw]
  rw [integral_map hObsF.aemeasurable hlog.aestronglyMeasurable,
    integral_map hObsG.aemeasurable hlog.aestronglyMeasurable,
    ← integral_sub hiF hiG]
  calc
    _ ≤ ∫ z : Omega × E, |Real.log (mixtureLikelihood mu G (F z.1+z.2)) -
        Real.log (mixtureLikelihood mu G (G z.1+z.2))| ∂mu.prod (stdGaussian E) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : Omega × E, K * ‖F z.1-G z.1‖ ∂mu.prod (stdGaussian E) := by
      apply integral_mono_ae (hiF.sub' hiG).abs
        (((hD.integrable (by norm_num)).norm.comp_fst (stdGaussian E)).const_mul K)
      exact .of_forall fun z ↦ by
        simpa only [add_sub_add_right_eq_sub] using
          abs_log_mixtureLikelihood_sub_le mu G hG hb (F z.1+z.2) (G z.1+z.2)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [probReal_univ, one_smul] using
        integral_fun_fst (μ := mu) (ν := stdGaussian E) (fun x ↦ ‖F x-G x‖)

/-- A bounded reference signal controls the free-energy change under an L2
coupling, even when the other signal has unbounded support. -/
theorem mixtureFreeEnergy_sub_bounds (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 mu) (hG2 : MemLp G 2 mu) {K : ℝ}
    (hb : ∀ᵐ x ∂mu, ‖G x‖ ≤ K) :
    -(K * ∫ x, ‖F x-G x‖ ∂mu) ≤ mixtureFreeEnergy mu F-mixtureFreeEnergy mu G ∧
    mixtureFreeEnergy mu F-mixtureFreeEnergy mu G ≤
      K * (∫ x, ‖F x-G x‖ ∂mu) + (1 / 2 : ℝ) * ∫ x, ‖F x-G x‖ ^ 2 ∂mu := by
  have hD : MemLp (fun x ↦ F x-G x) 2 mu := hF2.sub hG2
  have hKL := ENNReal.toReal_mono ENNReal.ofReal_ne_top (klDiv_mixtureLaw_le mu F G hF hG hD)
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (integral_nonneg fun x ↦ sq_nonneg ‖F x-G x‖))] at hKL
  have hcross := abs_le.mp (reference_log_integral_sub_le mu F G hF hG hF2 hG2 hb)
  rw [mixtureFreeEnergy_sub_eq mu F G hF hG hF2 hG2]
  have hnonneg := ENNReal.toReal_nonneg (a := klDiv (mixtureLaw mu F) (mixtureLaw mu G))
  constructor <;> linarith

theorem abs_mixtureFreeEnergy_sub_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 mu) (hG2 : MemLp G 2 mu) {K : ℝ}
    (hb : ∀ᵐ x ∂mu, ‖G x‖ ≤ K) :
    |mixtureFreeEnergy mu F-mixtureFreeEnergy mu G| ≤
      K * (∫ x, ‖F x-G x‖ ∂mu) + (1 / 2 : ℝ) * ∫ x, ‖F x-G x‖ ^ 2 ∂mu := by
  have h := mixtureFreeEnergy_sub_bounds mu F G hF hG hF2 hG2 hb
  have hsq := integral_nonneg (μ := mu) fun x ↦ sq_nonneg ‖F x-G x‖
  exact abs_le.mpr ⟨by linarith [h.1], h.2⟩


end TensorPCA.GaussianMixtureStabilityProofs
