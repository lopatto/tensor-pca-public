-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression

/-! Integrability for ordinary Gaussian convolutions of marks with exponential-linear
growth. The ordinary tower is `gaussianLogSteps` with all masses set to zero.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsExponentialGrowth
open MeasureTheory ProbabilityTheory Filter
open OneStepGaussianTiltStepDerivative OneStepGaussianStepLipschitz FiniteGaussianLogStepsCompression
open scoped NNReal
noncomputable section
variable {M : ℕ}

private theorem exp_norm_integrable (K : ℝ) :
    Integrable (fun g : Model.Vector M => Real.exp (K*‖g‖)) (stdGaussian (Model.Vector M)) := by
  apply integrable_exp_of_linear_growth measurable_norm (C := 0) (D := 1) _ K
  intro g
  simp only [abs_of_nonneg (norm_nonneg _),zero_add,one_mul]
  exact le_rfl

private theorem shift_dom {F : Model.Vector M→ℝ} {C K : ℝ} (hC : 0≤C) (hK : 0≤K)
    (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖)) (T : Model.Vector M→L[ℝ]Model.Vector M)
    (z g : Model.Vector M) :
    ‖F (z+T g)‖≤(C*Real.exp (K*‖z‖))*Real.exp ((K*‖T‖)*‖g‖) := by
  rw [Real.norm_eq_abs]
  calc
    _ ≤ C*Real.exp (K*‖z+T g‖) := hb _
    _ ≤ C*Real.exp (K*(‖z‖+‖T‖*‖g‖)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl (T.le_opNorm g))) hK)) hC
    _ = _ := by rw [mul_add,Real.exp_add]; ring

theorem shifted_integrable {F : Model.Vector M→ℝ} (hF : Measurable F) {C K : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖))
    (T : Model.Vector M→L[ℝ]Model.Vector M) (z : Model.Vector M) :
    Integrable (fun g : Model.Vector M => F (z+T g)) (stdGaussian (Model.Vector M)) := by
  apply ((exp_norm_integrable (K*‖T‖)).const_mul (C*Real.exp (K*‖z‖))).mono'
    (hF.comp (measurable_const.add T.continuous.measurable)).aestronglyMeasurable
  exact ae_of_all _ (shift_dom hC hK hb T z)

theorem ordinary_shift_growth {F : Model.Vector M→ℝ} (hF : Measurable F) {C K : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖))
    (T : Model.Vector M→L[ℝ]Model.Vector M) :
    let J := ∫g : Model.Vector M,Real.exp ((K*‖T‖)*‖g‖) ∂stdGaussian (Model.Vector M)
    Measurable (fun z => ∫g : Model.Vector M,F (z+T g) ∂stdGaussian (Model.Vector M)) ∧
      ∀z,|(∫g : Model.Vector M,F (z+T g) ∂stdGaussian (Model.Vector M))|≤(C*J)*Real.exp (K*‖z‖) := by
  dsimp only
  have hm : Measurable (fun zg : Model.Vector M×Model.Vector M => F (zg.1+T zg.2)) :=
    hF.comp (measurable_fst.add (T.continuous.measurable.comp measurable_snd))
  refine ⟨hm.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  intro z
  have HI := shifted_integrable hF hC hK hb T z
  have H := integral_mono HI.norm ((exp_norm_integrable (K*‖T‖)).const_mul (C*Real.exp (K*‖z‖)))
    (shift_dom hC hK hb T z)
  have HN := norm_integral_le_integral_norm (f := fun g : Model.Vector M => F (z+T g)) (μ := stdGaussian (Model.Vector M))
  rw [integral_const_mul] at H
  have HA := HN.trans H
  simpa only [Real.norm_eq_abs,mul_assoc,mul_comm (Real.exp (K*‖z‖))] using HA

theorem ordinary_steps_growth (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    {F : Model.Vector M→ℝ} (hF : Measurable F) {C K : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖)) :
    ∃B : ℝ,0≤B ∧ Measurable (gaussianLogSteps (steps.map (fun s => (0,s.2))) F) ∧
      ∀z,|gaussianLogSteps (steps.map (fun s => (0,s.2))) F z|≤B*Real.exp (K*‖z‖) := by
  induction steps with
  | nil => exact ⟨C,hC,hF,hb⟩
  | cons s steps ih =>
    obtain ⟨B,hB,hMeas,hBound⟩ := ih
    let J := ∫g : Model.Vector M,Real.exp ((K*‖s.2‖)*‖g‖) ∂stdGaussian (Model.Vector M)
    have hJ : 0≤J := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have H := ordinary_shift_growth hMeas hB hK hBound s.2
    dsimp only at H
    have HE : gaussianLogSteps ((s::steps).map (fun s => (0,s.2))) F=
        (fun z => ∫g : Model.Vector M,gaussianLogSteps (steps.map (fun s => (0,s.2))) F (z+s.2 g) ∂stdGaussian (Model.Vector M)) := by
      funext z
      simp only [List.map_cons,gaussianLogSteps,List.foldr_cons]
      simp only [gaussianLogStep,if_pos rfl,ite_true]
    refine ⟨B*J,mul_nonneg hB hJ,?_,?_⟩
    · rw [HE]
      exact H.1
    · rw [HE]
      exact H.2

theorem ordinary_steps_shifted_integrable (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    {F : Model.Vector M→ℝ} (hF : Measurable F) {C K : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖))
    (T : Model.Vector M→L[ℝ]Model.Vector M) (z : Model.Vector M) :
    Integrable (fun g : Model.Vector M => gaussianLogSteps (steps.map (fun s => (0,s.2))) F (z+T g))
      (stdGaussian (Model.Vector M)) := by
  obtain ⟨B,hB,hm,hbound⟩ := ordinary_steps_growth steps hF hC hK hb
  exact shifted_integrable hm hB hK hbound T z

theorem exp_sub_growth {L K : ℝ≥0} {F G : Model.Vector M→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G) (z : Model.Vector M) :
    |Real.exp (F z)-Real.exp (G z)|≤
      (Real.exp |F 0|+Real.exp |G 0|)*Real.exp (((L : ℝ)+(K : ℝ))*‖z‖) := by
  have HF : F z≤|F 0|+(L : ℝ)*‖z‖ := by
    have H := hF.dist_le_mul z 0
    simp only [Real.dist_eq,dist_zero_right] at H
    linarith [(abs_le.mp H).2,le_abs_self (F 0)]
  have HG : G z≤|G 0|+(K : ℝ)*‖z‖ := by
    have H := hG.dist_le_mul z 0
    simp only [Real.dist_eq,dist_zero_right] at H
    linarith [(abs_le.mp H).2,le_abs_self (G 0)]
  have HFE : Real.exp (F z)≤Real.exp |F 0| *Real.exp (((L : ℝ)+(K : ℝ))*‖z‖) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg K.coe_nonneg (norm_nonneg z)]
  have HGE : Real.exp (G z)≤Real.exp |G 0| *Real.exp (((L : ℝ)+(K : ℝ))*‖z‖) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg L.coe_nonneg (norm_nonneg z)]
  calc
    _ ≤ Real.exp (F z)+Real.exp (G z) := by
      simpa only [sub_eq_add_neg,abs_neg,abs_of_pos (Real.exp_pos _)] using abs_add_le (Real.exp (F z)) (-Real.exp (G z))
    _ ≤ Real.exp |F 0| *Real.exp (((L : ℝ)+(K : ℝ))*‖z‖)+Real.exp |G 0| *Real.exp (((L : ℝ)+(K : ℝ))*‖z‖) := add_le_add HFE HGE
    _ = _ := by ring

theorem ordinary_steps_exp_sub_shifted_integrable
    (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    {L K : ℝ≥0} {F G : Model.Vector M→ℝ} (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector M→L[ℝ]Model.Vector M) (z : Model.Vector M) :
    Integrable (fun g : Model.Vector M => gaussianLogSteps (steps.map (fun s => (0,s.2)))
      (fun y => Real.exp (F y)-Real.exp (G y)) (z+T g)) (stdGaussian (Model.Vector M)) := by
  exact ordinary_steps_shifted_integrable steps (hF.continuous.measurable.exp.sub hG.continuous.measurable.exp)
    (by positivity) (add_nonneg L.coe_nonneg K.coe_nonneg) (exp_sub_growth hF hG) T z

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsExponentialGrowth
