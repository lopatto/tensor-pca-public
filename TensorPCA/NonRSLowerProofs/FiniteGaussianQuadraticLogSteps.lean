-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticStep
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecision
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression

/-! Quadratic Gaussian log-step recursion at every finite depth. The tower is the
Gaussian log-step list fold; quadratic moments are estimated separately from
Lipschitz terminal bounds.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticLogSteps
open MeasureTheory ProbabilityTheory
open FiniteGaussianQuadraticStep FiniteCSGaussianDepthPrecision
open FiniteGaussianLogStepsCompression OneStepGaussianStepLipschitz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gaussianLogSteps_eq_of_recursion {M : ℕ}
    (steps : List (ℝ×(Model.Vector M→L[ℝ] Model.Vector M))) (F : Model.Vector M→ℝ)
    (H : ℕ→Model.Vector M→ℝ) (hEnd : H steps.length=F)
    (hStep : ∀(i : ℕ) (hi : i< steps.length),H i=gaussianLogStep (steps[i]).2 (steps[i]).1 (H (i+1))) :
    gaussianLogSteps steps F=H 0 := by
  induction steps generalizing H with
  | nil => simpa only [gaussianLogSteps,List.foldr_nil,List.length_nil] using hEnd.symm
  | cons a steps ih =>
    have hTailEnd : (fun i => H (i+1)) steps.length=F := by simpa only [List.length_cons] using hEnd
    have hTailStep (i : ℕ) (hi : i< steps.length) :
        (fun j => H (j+1)) i=gaussianLogStep (steps[i]).2 (steps[i]).1 ((fun j => H (j+1)) (i+1)) := by
      have HS := hStep (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
      simpa only [List.getElem_cons_succ] using HS
    have HT := ih (fun i => H (i+1)) hTailEnd hTailStep
    have H0 := hStep 0 (by simp)
    simp only [List.getElem_cons_zero,zero_add] at H0
    change gaussianLogStep a.2 a.1 (gaussianLogSteps steps F)=H 0
    rw [HT]
    exact H0.symm

def profileConstant {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) (B : ℝ) (i : ℕ) : ℝ :=
  -(M : ℝ)*Real.log B/2+
    tail (fun j => (M : ℝ)*Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/(2*x j)) i

def envelope {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) (B : ℝ) (i : ℕ) : Model.Vector M→ℝ :=
  quadratic (profileConstant M x Delta B i) (precision x Delta B i)

def quadraticSteps {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) :
    List (ℝ×(Model.Vector M→L[ℝ] Model.Vector M)) :=
  List.ofFn (fun j : Fin d => (x j,shift M (Delta j)))

theorem envelope_terminal {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) (B : ℝ) :
    envelope M x Delta B d=quadratic (-(M : ℝ)*Real.log B/2) B := by
  unfold envelope profileConstant
  rw [tail_end,add_zero,precision_end]

theorem envelope_step {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (j : Fin d) (h : Model.Vector M) :
    gaussianLogStep (shift M (Delta j)) (x j) (envelope M x Delta B ((j : ℕ)+1)) h=
      envelope M x Delta B j h := by
  have hP := precision_pos hx hDelta hB
  have hPrec := precision_succ x Delta B j
  have hD : precision x Delta B ((j : ℕ)+1)-x j*Delta j=precision x Delta B j := by linarith only [hPrec]
  have hC : profileConstant M x Delta B j=profileConstant M x Delta B ((j : ℕ)+1)+
      (M : ℝ)*Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/(2*x j) := by
    have H := tail_succ (fun l => (M : ℝ)*Real.log
      (precision x Delta B ((l : ℕ)+1)/precision x Delta B l)/(2*x l)) j.isLt
    unfold profileConstant
    linarith only [H]
  have H := gaussianLogStep_quadratic (hP ((j : ℕ)+1)) (hDelta j) (hx j).ne'
    (show 0< precision x Delta B ((j : ℕ)+1)-x j*Delta j by rw [hD]; exact hP j)
    (profileConstant M x Delta B ((j : ℕ)+1)) h
  rw [hD] at H
  simpa only [envelope,quadratic,hC] using H

theorem gaussianLogSteps_quadratic {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (h : Model.Vector M) :
    gaussianLogSteps (quadraticSteps M x Delta) (quadratic (-(M : ℝ)*Real.log B/2) B) h=
      profileConstant M x Delta B 0+‖h‖^2/(2*precision x Delta B 0) := by
  have hEnd : envelope M x Delta B (quadraticSteps M x Delta).length=
      quadratic (-(M : ℝ)*Real.log B/2) B := by
    rw [quadraticSteps,List.length_ofFn,envelope_terminal]
  have hStep (i : ℕ) (hi : i<(quadraticSteps M x Delta).length) :
      envelope M x Delta B i=
        gaussianLogStep ((quadraticSteps M x Delta)[i]).2 ((quadraticSteps M x Delta)[i]).1 (envelope M x Delta B (i+1)) := by
    have hid : i< d := by simpa only [quadraticSteps,List.length_ofFn] using hi
    funext h
    have H := envelope_step M hx hDelta hB ⟨i,hid⟩ h
    simpa only [quadraticSteps,List.getElem_ofFn] using H.symm
  have H := gaussianLogSteps_eq_of_recursion (quadraticSteps M x Delta)
    (quadratic (-(M : ℝ)*Real.log B/2) B) (envelope M x Delta B) hEnd hStep
  exact congrFun H h

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticLogSteps
