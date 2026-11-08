-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalStages
public import TensorPCA.NonRSLowerProofs.FiniteGaussianProbabilityPropagation

/-! Finite propagation from a conditional-probability recursion. The suffix kernel
supplies the recursion hypotheses in its consumer.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticOrderedPropagation
open MeasureTheory ProbabilityTheory Set
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticStep
open FiniteGaussianQuadraticKernel FiniteGaussianQuadraticSpine
open FiniteGaussianQuadraticLogSteps FiniteGaussianQuadraticSphericalStages
open FiniteGaussianQuadraticTerminalGood FiniteGaussianQuadraticTerminalShell
open FiniteGaussianProbabilityPropagation OneStepGaussianStepTiltMoment
open OneStepGaussianTiltEndpoint
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ordered_probability_propagation {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B C eps : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (hC : 0≤ C) (heps : 0≤ eps)
    (G : ℕ→Model.Vector M→ℝ) (hGm : ∀i,Measurable (G i))
    (hG01 : ∀i h,G i h∈Icc (0 : ℝ) 1)
    (hGend : ∀h,G d h=((Kernel.id ×ₖ terminalSpinKernel M (precision_B_pos hx hDelta hB)) h).real
      (terminalGoodSet M C eps))
    (hGstep : ∀(j : Fin d) h,G j h=
      ∫g,G ((j : ℕ)+1) (h+shift M (Delta j) g)
        ∂gaussianTilt (shift M (Delta j)) (x j) (envelope M x Delta B ((j : ℕ)+1)) h) :
    ∀(i : Fin (d+1)) h,G i h≤
      Real.exp (stageMass x i*(sphericalStage M x Delta i h-envelope M x Delta B i h-
        (M : ℝ)*((B-1)/2-eps*(C+|B-1|/2)))) := by
  intro i
  refine Fin.reverseInduction ?_ ?_ i
  · intro h
    change G d h≤Real.exp (stageMass x d*(sphericalStage M x Delta d h-
      envelope M x Delta B d h-(M : ℝ)*((B-1)/2-eps*(C+|B-1|/2))))
    rw [stageMass_terminal,sphericalStage_terminal,envelope_terminal,one_mul,hGend]
    have HP := terminal_spherical_shell_lower hM (precision_B_pos hx hDelta hB) hC heps h
    have heq : Real.log (sphericalLaplace M h)-quadratic (-(M : ℝ)*Real.log B/2) B h-
        (M : ℝ)*((B-1)/2-eps*(C+|B-1|/2))=
        Real.log (sphericalLaplace M h)-(quadratic (-(M : ℝ)*Real.log B/2) B h+
          (M : ℝ)*((B-1)/2-eps*(C+|B-1|/2))) := by ring
    rw [heq,Real.exp_sub,Real.exp_log (sphericalLaplace_pos hM h)]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using HP)
  · intro j ih h
    change G j h≤Real.exp (stageMass x j*(sphericalStage M x Delta j h-
      envelope M x Delta B j h-(M : ℝ)*((B-1)/2-eps*(C+|B-1|/2))))
    rw [stageMass_self,hGstep]
    have hP := precision_pos hx hDelta hB
    have hH : Integrable (fun g : Model.Vector M =>
        Real.exp (x j*envelope M x Delta B ((j : ℕ)+1) (h+shift M (Delta j) g)))
        (stdGaussian (Model.Vector M)) :=
      quadratic_exp_integrable (hP ((j : ℕ)+1)) (hDelta j)
        (show 0< precision x Delta B ((j : ℕ)+1)-x j*Delta j by
          rw [step_precision]; exact hP j)
        (profileConstant M x Delta B ((j : ℕ)+1)) h
    have HP := gaussianLogStep_probability_lower (shift M (Delta j)) (hx j)
      (stageMass_next_ge hMono hx1 j)
      (sphericalStage M x Delta ((j : ℕ)+1)) (envelope M x Delta B ((j : ℕ)+1))
      (G ((j : ℕ)+1)) ((M : ℝ)*((B-1)/2-eps*(C+|B-1|/2)))
      (hGm _) (hG01 _) (fun z => ih z) h
      (sphericalStage_exp_integrable hM x Delta ((j : ℕ)+1) (shift M (Delta j)) (x j) h) hH
    rw [← sphericalStage_step M x Delta j,envelope_step M hx hDelta hB j h] at HP
    exact HP

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticOrderedPropagation
