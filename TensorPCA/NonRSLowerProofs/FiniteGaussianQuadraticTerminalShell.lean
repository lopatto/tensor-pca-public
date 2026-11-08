-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalGood
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLower

/-! The spherical terminal dominates the quadratic spin-shell factor, with the terminal
field cutoff retained.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalShell
open MeasureTheory ProbabilityTheory Set
open FiniteGaussianAffineKernel FiniteGaussianQuadraticKernel FiniteGaussianQuadraticStep
open FiniteGaussianQuadraticTerminalGood
open OneStepGaussianTiltFractional OneStepGaussianTiltEndpoint OneStepGaussianTiltLower
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem terminalSpinKernel_shell_probability {M : ℕ} {B : ℝ} (hB : 0< B)
    (h : Model.Vector M) {S : Set (Model.Vector M)} (hS : MeasurableSet S) :
    (terminalSpinKernel M hB h).real S=conditionalShellProbability B 0 h S 0 := by
  rw [terminalSpinKernel_eq_affine,affineKernel_apply,← integral_indicator_one hS]
  have hTest : Measurable (S.indicator (1 : Model.Vector M→ℝ)) := measurable_const.indicator hS
  rw [integral_map (by fun_prop : Measurable (fun g : Model.Vector M =>
      B⁻¹ •h+Real.sqrt B⁻¹ •g)).aemeasurable
        hTest.aestronglyMeasurable]
  simp only [conditionalShellProbability,Real.sqrt_zero,zero_smul,add_zero,one_div,Real.sqrt_inv]
  apply integral_congr_ae
  filter_upwards [] with g
  by_cases hg : B⁻¹ •h+(Real.sqrt B)⁻¹ •g∈S <;> simp [hg]

theorem terminal_joint_good_probability {M : ℕ} {B : ℝ} (hB : 0< B)
    (C eps : ℝ) (h : Model.Vector M) :
    ((Kernel.id ×ₖ terminalSpinKernel M hB) h).real (terminalGoodSet M C eps)=
      if ‖h‖^2≤C^2*(M : ℝ) then
        (terminalSpinKernel M hB h).real {sigma | |‖sigma‖^2-(M : ℝ)|≤eps*(M : ℝ)} else 0 := by
  have H := Kernel.id_prod_apply' (terminalSpinKernel M hB) h (terminalGoodSet_measurable M C eps)
  by_cases hh : ‖h‖^2≤C^2*(M : ℝ)
  · have hSet : Prod.mk h ⁻¹' terminalGoodSet M C eps=
        {sigma : Model.Vector M | |‖sigma‖^2-(M : ℝ)|≤eps*(M : ℝ)} := by
      ext sigma
      simp only [terminalGoodSet,mem_preimage,mem_setOf_eq,hh,true_and]
    rw [if_pos hh]
    change (((Kernel.id ×ₖ terminalSpinKernel M hB) h) (terminalGoodSet M C eps)).toReal=_
    rw [H,hSet]
    rfl
  · have hSet : Prod.mk h ⁻¹' terminalGoodSet M C eps=∅ := by
      ext sigma
      simp only [terminalGoodSet,mem_preimage,mem_setOf_eq,hh,false_and,mem_empty_iff_false]
    rw [if_neg hh]
    change (((Kernel.id ×ₖ terminalSpinKernel M hB) h) (terminalGoodSet M C eps)).toReal=0
    rw [H,hSet,measure_empty,ENNReal.toReal_zero]

theorem terminal_spherical_shell_lower {M : ℕ} (hM : 0< M) {B C eps : ℝ}
    (hB : 0< B) (hC : 0≤ C) (heps : 0≤ eps) (h : Model.Vector M) :
    Real.exp (quadratic (-(M : ℝ)*Real.log B/2) B h+
      (M : ℝ)*((B-1)/2-eps*(C+|B-1|/2)))*
        ((Kernel.id ×ₖ terminalSpinKernel M hB) h).real (terminalGoodSet M C eps)≤
      sphericalLaplace M h := by
  rw [terminal_joint_good_probability]
  split_ifs with hh
  · have hnorm : ‖h‖≤C*Real.sqrt (M : ℝ) := by
      apply (sq_le_sq₀ (norm_nonneg h) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
      simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)] using hh
    have HP := shell_kernel_le_sphericalLaplace hM hB heps hC h (0 : Model.Vector M)
      (v := 0) (by simpa only [Real.sqrt_zero,zero_smul,add_zero] using hnorm)
    simp only [Real.sqrt_zero,zero_smul,add_zero] at HP
    rw [← terminalSpinKernel_shell_probability hB h
      (measurableSet_le (by fun_prop) measurable_const)] at HP
    let A := (M : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2))
    calc
      _=Real.exp (-A)*(Real.exp (‖h‖^2/(2*B))*
          (terminalSpinKernel M hB h).real {sigma | |‖sigma‖^2-(M : ℝ)|≤eps*(M : ℝ)}) := by
        rw [← mul_assoc,← Real.exp_add]
        congr 2
        unfold quadratic A
        ring
      _≤Real.exp (-A)*(Real.exp A*sphericalLaplace M h) :=
        mul_le_mul_of_nonneg_left HP (Real.exp_pos _).le
      _=sphericalLaplace M h := by rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  · simpa only [mul_zero] using (sphericalLaplace_pos hM h).le

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalShell
