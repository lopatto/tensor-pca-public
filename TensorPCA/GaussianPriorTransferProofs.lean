-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianChannelProofs
public import TensorPCA.GaussianMomentProofs
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# General Gaussian mixtures and spherical-reference transfer

The signal map below includes its channel scaling. Its norm need not equal one:
the likelihood penalizes the full squared norm of that signal. Free energy is
the relative entropy of the output law to canonical Gaussian noise.
-/
@[expose] public section

namespace TensorPCA.GaussianPriorTransferProofs

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def mixtureWeight (v y : E) : ℝ := Real.exp (inner ℝ v y - ‖v‖ ^ 2 / 2)

noncomputable def mixtureLikelihood (mu : Measure Omega) (F : Omega → E) (y : E) : ℝ :=
  ∫ x, mixtureWeight (F x) y ∂mu

noncomputable def jointLaw (mu : Measure Omega) (F : Omega → E) : Measure (Omega × E) :=
  (mu.prod (stdGaussian E)).map (fun z ↦ (z.1, F z.1 + z.2))

noncomputable def mixtureLaw (mu : Measure Omega) (F : Omega → E) : Measure E :=
  (mu.prod (stdGaussian E)).map (fun z ↦ F z.1 + z.2)

noncomputable def mixtureFreeEnergy (mu : Measure Omega) (F : Omega → E) : ℝ :=
  (klDiv (mixtureLaw mu F) (stdGaussian E)).toReal

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_mixtureWeight : Continuous (Function.uncurry (mixtureWeight (E := E))) :=
  Real.continuous_exp.comp ((continuous_fst.inner continuous_snd).sub
    (continuous_fst.norm.pow 2 |>.div_const 2))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mixtureWeight_pos (v y : E) : 0 < mixtureWeight v y := Real.exp_pos _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Square completion controls every observation, even for unbounded signal
priors and tensor features of arbitrarily high degree. -/
theorem mixtureWeight_le (v y : E) : mixtureWeight v y ≤ Real.exp (‖y‖ ^ 2 / 2) := by
  apply Real.exp_le_exp.mpr
  nlinarith [norm_sub_sq_real v y, sq_nonneg ‖v-y‖]

theorem integrable_mixtureWeight (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) :
    Integrable (fun x ↦ mixtureWeight (F x) y) mu := by
  apply (integrable_const (Real.exp (‖y‖ ^ 2 / 2))).mono'
    ((continuous_mixtureWeight.measurable.comp (hF.prodMk measurable_const)).aestronglyMeasurable)
  exact .of_forall fun x ↦ by
    change ‖mixtureWeight (F x) y‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_pos (mixtureWeight_pos (F x) y)] using mixtureWeight_le (F x) y

theorem mixtureLikelihood_pos (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) : 0 < mixtureLikelihood mu F y :=
  integral_exp_pos (integrable_mixtureWeight mu F hF y)

theorem measurable_mixtureLikelihood (mu : Measure Omega) [SFinite mu]
    (F : Omega → E) (hF : Measurable F) : Measurable (mixtureLikelihood mu F) := by
  have hm : StronglyMeasurable (fun z : E × Omega ↦ mixtureWeight (F z.2) z.1) :=
    (continuous_mixtureWeight.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := mu)).measurable

theorem jointLaw_probability (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : IsProbabilityMeasure (jointLaw mu F) := by
  exact Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)).aemeasurable |>.mpr inferInstance

theorem mixtureLaw_probability (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : IsProbabilityMeasure (mixtureLaw mu F) := by
  exact Measure.isProbabilityMeasure_map_iff
    ((hF.comp measurable_fst).add measurable_snd).aemeasurable |>.mpr inferInstance

theorem jointLaw_eq_withDensity (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    jointLaw mu F = (mu.prod (stdGaussian E)).withDensity
      (fun z ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) := by
  have hObs : Measurable (fun z : Omega × E ↦ (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  have hWeight : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) :=
    (continuous_mixtureWeight.measurable.comp ((hF.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro g hg
  rw [jointLaw, lintegral_map hg hObs, lintegral_withDensity_eq_lintegral_mul _ hWeight hg]
  change (∫⁻ z, g (z.1, F z.1 + z.2) ∂mu.prod (stdGaussian E)) =
    ∫⁻ z, ENNReal.ofReal (mixtureWeight (F z.1) z.2) * g z ∂mu.prod (stdGaussian E)
  rw [lintegral_prod (fun z : Omega × E ↦ g (z.1, F z.1 + z.2)) (hg.comp hObs).aemeasurable,
    lintegral_prod (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2) * g z)
      (hWeight.mul hg).aemeasurable]
  apply lintegral_congr_ae
  exact .of_forall fun x ↦ by
    have hgFix : Measurable (fun y : E ↦ g (x, y)) := hg.comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫⁻ y, g (x, y) ∂(stdGaussian E).map (fun w ↦ F x + w) :=
        (lintegral_map hgFix (by fun_prop)).symm
      _ = ∫⁻ y, g (x, y) ∂(stdGaussian E).withDensity
          (fun y ↦ ENNReal.ofReal (mixtureWeight (F x) y)) := by
        rw [GaussianChannelProofs.stdGaussian_map_add_eq_withDensity]
        rfl
      _ = _ := lintegral_withDensity_eq_lintegral_mul _
        (hWeight.comp (measurable_const.prodMk measurable_id)) hgFix

theorem mixtureLaw_eq_withDensity (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    mixtureLaw mu F = (stdGaussian E).withDensity
      (fun y ↦ ENNReal.ofReal (mixtureLikelihood mu F y)) := by
  have hObs : Measurable (fun z : Omega × E ↦ (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  have hWeight : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) :=
    (continuous_mixtureWeight.measurable.comp ((hF.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have hMap : mixtureLaw mu F = (jointLaw mu F).map Prod.snd := by
    rw [jointLaw, Measure.map_map measurable_snd hObs]
    rfl
  apply Measure.ext_of_lintegral
  intro g hg
  rw [hMap, jointLaw_eq_withDensity mu F hF, lintegral_map hg measurable_snd,
    lintegral_withDensity_eq_lintegral_mul (g := fun z : Omega × E ↦ g z.2) _ hWeight (hg.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_mixtureLikelihood mu F hF).ennreal_ofReal hg]
  change (∫⁻ z, ENNReal.ofReal (mixtureWeight (F z.1) z.2) * g z.2 ∂mu.prod (stdGaussian E)) = _
  rw [lintegral_prod_symm (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2) * g z.2)
    (hWeight.mul (hg.comp measurable_snd)).aemeasurable]
  apply lintegral_congr_ae
  exact .of_forall fun y ↦ by
    dsimp only
    have hw : Measurable (fun x ↦ ENNReal.ofReal (mixtureWeight (F x) y)) :=
      (continuous_mixtureWeight.measurable.comp (hF.prodMk measurable_const)).ennreal_ofReal
    rw [lintegral_mul_const (g y) hw,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_mixtureWeight mu F hF y)
        (.of_forall fun x ↦ (mixtureWeight_pos (F x) y).le)]
    rfl

theorem jointLaw_absolutelyContinuous (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : jointLaw mu F ≪ mu.prod (stdGaussian E) := by
  rw [jointLaw_eq_withDensity mu F hF]
  exact withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_jointLaw (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : mu.prod (stdGaussian E) ≪ jointLaw mu F := by
  rw [jointLaw_eq_withDensity mu F hF]
  apply withDensity_absolutelyContinuous'
  · exact (continuous_mixtureWeight.measurable.comp
      ((hF.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal.aemeasurable
  · exact .of_forall fun z ↦ (ENNReal.ofReal_pos.mpr (mixtureWeight_pos (F z.1) z.2)).ne'

theorem jointLaw_llr (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G) :
    llr (jointLaw mu F) (jointLaw mu G) =ᵐ[jointLaw mu F] fun z ↦
      inner ℝ (F z.1) z.2 - ‖F z.1‖ ^ 2 / 2 -
        (inner ℝ (G z.1) z.2 - ‖G z.1‖ ^ 2 / 2) := by
  have : IsProbabilityMeasure (jointLaw mu F) := jointLaw_probability mu F hF
  have hwF : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) :=
    (continuous_mixtureWeight.measurable.comp ((hF.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have hwG : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (G z.1) z.2)) :=
    (continuous_mixtureWeight.measurable.comp ((hG.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have hright := Measure.rnDeriv_withDensity_right (jointLaw mu F) (mu.prod (stdGaussian E))
    hwG.aemeasurable (.of_forall fun z ↦ (ENNReal.ofReal_pos.mpr (mixtureWeight_pos (G z.1) z.2)).ne')
    (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)
  have hleft := Measure.rnDeriv_withDensity (mu.prod (stdGaussian E)) hwF
  rw [← jointLaw_eq_withDensity mu F hF] at hleft
  rw [← jointLaw_eq_withDensity mu G hG] at hright
  filter_upwards [hleft.filter_mono (jointLaw_absolutelyContinuous mu F hF).ae_le,
    hright.filter_mono (jointLaw_absolutelyContinuous mu F hF).ae_le] with z hl hr
  rw [llr, hr, hl, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mixtureWeight_pos (F z.1) z.2).le,
    ENNReal.toReal_ofReal (mixtureWeight_pos (G z.1) z.2).le,
    Real.log_mul (inv_ne_zero (mixtureWeight_pos (G z.1) z.2).ne')
      (mixtureWeight_pos (F z.1) z.2).ne', Real.log_inv]
  simp only [mixtureWeight, Real.log_exp]
  ring

/-- Under the true first channel, the joint log-likelihood ratio has a
centered Gaussian cross term plus half the squared signal discrepancy. -/
theorem jointLaw_llr_comp (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G) :
    (fun z : Omega × E ↦ llr (jointLaw mu F) (jointLaw mu G) (z.1, F z.1 + z.2)) =ᵐ[
      mu.prod (stdGaussian E)] fun z ↦ inner ℝ (F z.1 - G z.1) z.2 + ‖F z.1-G z.1‖ ^ 2 / 2 := by
  have hmp : MeasurePreserving (fun z : Omega × E ↦ (z.1, F z.1 + z.2))
      (mu.prod (stdGaussian E)) (jointLaw mu F) :=
    ⟨measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd), rfl⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (jointLaw_llr mu F G hF hG)] with z hz
  rw [hz]
  simp only [inner_add_right, inner_sub_left, norm_sub_sq_real, real_inner_self_eq_norm_sq,
    real_inner_comm]
  ring

theorem integrable_discrepancy_cross (mu : Measure Omega) [IsProbabilityMeasure mu]
    (D : Omega → E) (hD : MemLp D 2 mu) :
    Integrable (fun z : Omega × E ↦ inner ℝ (D z.1) z.2) (mu.prod (stdGaussian E)) := by
  apply (hD.integrable (by norm_num)).op_fst_snd (continuous_inner (𝕜 := ℝ))
    ⟨1, fun v w ↦ by simpa only [one_mul] using norm_inner_le_norm v w⟩
    (IsGaussian.integrable_fun_id (μ := stdGaussian E))

theorem integrable_jointLaw_llr (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hD : MemLp (fun x ↦ F x-G x) 2 mu) :
    Integrable (llr (jointLaw mu F) (jointLaw mu G)) (jointLaw mu F) := by
  have hObs : Measurable (fun z : Omega × E ↦ (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  rw [jointLaw, integrable_map_measure (stronglyMeasurable_llr _ _).aestronglyMeasurable hObs.aemeasurable]
  have hs := ((hD.integrable_norm_pow (by decide : 2 ≠ 0)).comp_fst (stdGaussian E)).div_const 2
  exact ((integrable_discrepancy_cross mu _ hD).fun_add hs).congr (jointLaw_llr_comp mu F G hF hG).symm

theorem integral_jointLaw_llr (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hD : MemLp (fun x ↦ F x-G x) 2 mu) :
    (∫ z, llr (jointLaw mu F) (jointLaw mu G) z ∂jointLaw mu F) =
      (1 / 2 : ℝ) * ∫ x, ‖F x-G x‖ ^ 2 ∂mu := by
  have hObs : Measurable (fun z : Omega × E ↦ (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  change (∫ z, llr (jointLaw mu F) (jointLaw mu G) z ∂
    (mu.prod (stdGaussian E)).map (fun z ↦ (z.1, F z.1 + z.2))) = _
  rw [integral_map hObs.aemeasurable (stronglyMeasurable_llr _ _).aestronglyMeasurable,
    integral_congr_ae (jointLaw_llr_comp mu F G hF hG),
    integral_add (integrable_discrepancy_cross mu _ hD)
      (((hD.integrable_norm_pow (by decide : 2 ≠ 0)).comp_fst (stdGaussian E)).div_const 2),
    integral_div]
  have hs : (∫ z : Omega × E, ‖F z.1-G z.1‖ ^ 2 ∂mu.prod (stdGaussian E)) =
      ∫ x, ‖F x-G x‖ ^ 2 ∂mu := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := mu) (ν := stdGaussian E) (fun x ↦ ‖F x-G x‖ ^ 2)
  rw [hs]
  have hc := integral_prod_bilin (innerSL ℝ) (hD.integrable (by norm_num))
    (IsGaussian.integrable_fun_id (μ := stdGaussian E))
  simp only [integral_id_stdGaussian, map_zero] at hc
  change (∫ z : Omega × E, inner ℝ (F z.1-G z.1) z.2 ∂mu.prod (stdGaussian E)) = 0 at hc
  rw [hc]
  simp only [zero_add, div_eq_mul_inv, one_mul, mul_comm]

theorem klDiv_jointLaw (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hD : MemLp (fun x ↦ F x-G x) 2 mu) :
    klDiv (jointLaw mu F) (jointLaw mu G) =
      ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x, ‖F x-G x‖ ^ 2 ∂mu) := by
  have : IsProbabilityMeasure (jointLaw mu F) := jointLaw_probability mu F hF
  have : IsProbabilityMeasure (jointLaw mu G) := jointLaw_probability mu G hG
  rw [klDiv_of_ac_of_integrable ((jointLaw_absolutelyContinuous mu F hF).trans
    (absolutelyContinuous_jointLaw mu G hG)) (integrable_jointLaw_llr mu F G hF hG hD),
    integral_jointLaw_llr mu F G hF hG hD]
  simp

theorem jointLaw_map_snd (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : (jointLaw mu F).map Prod.snd = mixtureLaw mu F := by
  have hObs : Measurable (fun z : Omega × E ↦ (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  rw [jointLaw, Measure.map_map measurable_snd hObs]
  rfl

/-- Relative entropy contracts after hiding the coupled latent variable. -/
theorem klDiv_mixtureLaw_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F G : Omega → E) (hF : Measurable F) (hG : Measurable G)
    (hD : MemLp (fun x ↦ F x-G x) 2 mu) :
    klDiv (mixtureLaw mu F) (mixtureLaw mu G) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x, ‖F x-G x‖ ^ 2 ∂mu) := by
  have : IsProbabilityMeasure (jointLaw mu F) := jointLaw_probability mu F hF
  have : IsProbabilityMeasure (jointLaw mu G) := jointLaw_probability mu G hG
  have h := klDiv_map_le (jointLaw mu F) (jointLaw mu G) (measurable_snd (α := Omega) (β := E))
  simpa only [jointLaw_map_snd mu F hF, jointLaw_map_snd mu G hG,
    klDiv_jointLaw mu F G hF hG hD] using h


end TensorPCA.GaussianPriorTransferProofs
