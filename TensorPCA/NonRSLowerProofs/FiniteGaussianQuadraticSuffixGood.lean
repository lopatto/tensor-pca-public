-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalGood

/-! The suffix joint law of terminal field and spin, with its good-event probability.
Each recursive mean uses the normalized quadratic fresh Gaussian law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSuffixGood
open MeasureTheory ProbabilityTheory Set
open FiniteGaussianAffineKernel FiniteGaussianQuadraticStep FiniteGaussianQuadraticKernel
open FiniteGaussianQuadraticLogSteps FiniteGaussianQuadraticSpine
open FiniteGaussianQuadraticForwardSpine FiniteGaussianQuadraticTerminalJoint
open FiniteGaussianQuadraticTerminalGood FiniteCSGaussianDepthPrecision
open OneStepGaussianStepTiltMoment
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem jointFold_markov {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (terminal : Kernel (Model.Vector M) (Model.Vector M×Model.Vector M)) [IsMarkovKernel terminal]
    (hSteps : ∀K∈steps,IsMarkovKernel K) :
    IsMarkovKernel (steps.foldr (fun step downstream ↦ downstream ∘ₖ step) terminal) := by
  revert hSteps
  induction steps with
  | nil => intro hSteps; change IsMarkovKernel terminal; infer_instance
  | cons a steps ih =>
    intro hSteps
    haveI : IsMarkovKernel a := hSteps a (by simp)
    haveI : IsMarkovKernel (steps.foldr (fun step downstream ↦ downstream ∘ₖ step) terminal) :=
      ih (fun K hK ↦ hSteps K (by simp [hK]))
    change IsMarkovKernel ((steps.foldr (fun step downstream ↦ downstream ∘ₖ step) terminal) ∘ₖ a)
    infer_instance

private theorem jointFold_forward {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (terminal : Kernel (Model.Vector M) (Model.Vector M×Model.Vector M))
    (initial : Kernel (Model.Vector M) (Model.Vector M)) :
    terminal ∘ₖ forwardKernels steps initial=
      steps.foldr (fun step downstream ↦ downstream ∘ₖ step) terminal ∘ₖ initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons a steps ih =>
    change terminal ∘ₖ forwardKernels steps (a ∘ₖ initial)=
      ((steps.foldr (fun step downstream ↦ downstream ∘ₖ step) terminal) ∘ₖ a) ∘ₖ initial
    rw [ih,Kernel.comp_assoc]

def suffixJointKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (i : ℕ) :
    Kernel (Model.Vector M) (Model.Vector M×Model.Vector M) :=
  ((spineKernels M hx hDelta hB).drop i).foldr
    (fun step downstream ↦ downstream ∘ₖ step)
    (Kernel.id ×ₖ terminalSpinKernel M (precision_B_pos hx hDelta hB))

instance suffixJointKernel_markov {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (i : ℕ) :
    IsMarkovKernel (suffixJointKernel M hx hDelta hB i) := by
  unfold suffixJointKernel
  apply jointFold_markov
  intro K hK
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hK)
  infer_instance

def suffixGoodProbability {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (i : ℕ) (h : Model.Vector M) : ℝ :=
  (suffixJointKernel M hx hDelta hB i h).real (terminalGoodSet M C eps)

theorem suffixGoodProbability_measurable {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (i : ℕ) :
    Measurable (suffixGoodProbability M hx hDelta hB C eps i) :=
  ((suffixJointKernel M hx hDelta hB i).measurable_coe (terminalGoodSet_measurable M C eps)).ennreal_toReal

theorem suffixGoodProbability_mem_Icc {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (i : ℕ) (h : Model.Vector M) :
    suffixGoodProbability M hx hDelta hB C eps i h∈Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩

theorem suffixJointKernel_zero {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) :
    suffixJointKernel M hx hDelta hB 0=terminalJointKernel M hx hDelta hB := by
  have H := jointFold_forward (spineKernels M hx hDelta hB)
    (Kernel.id ×ₖ terminalSpinKernel M (precision_B_pos hx hDelta hB)) Kernel.id
  simp only [Kernel.comp_id] at H
  simpa only [suffixJointKernel,List.drop_zero,terminalJointKernel,fieldKernel] using H.symm

theorem suffixJointKernel_terminal {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) :
    suffixJointKernel M hx hDelta hB d=
      Kernel.id ×ₖ terminalSpinKernel M (precision_B_pos hx hDelta hB) := by
  have hdrop : (spineKernels M hx hDelta hB).drop d=[] := by
    apply List.drop_eq_nil_of_le
    simpa only [spineKernels,List.length_ofFn] using (le_refl d)
  simp only [suffixJointKernel,hdrop,List.foldr_nil]

theorem suffixJointKernel_succ {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (j : Fin d) :
    suffixJointKernel M hx hDelta hB j=
      suffixJointKernel M hx hDelta hB ((j : ℕ)+1) ∘ₖ spineStep M hx hDelta hB j := by
  have hj : (j : ℕ)<(spineKernels M hx hDelta hB).length := by
    simpa only [spineKernels,List.length_ofFn] using j.isLt
  unfold suffixJointKernel
  rw [List.drop_eq_getElem_cons hj,List.foldr_cons]
  congr 1
  simp only [spineKernels,List.getElem_ofFn]

theorem suffixGoodProbability_zero {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (h : Model.Vector M) :
    suffixGoodProbability M hx hDelta hB C eps 0 h=terminalGoodProbability M hx hDelta hB C eps h := by
  simp only [suffixGoodProbability,terminalGoodProbability,suffixJointKernel_zero]

theorem suffixGoodProbability_terminal {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (h : Model.Vector M) :
    suffixGoodProbability M hx hDelta hB C eps d h=
      ((Kernel.id ×ₖ terminalSpinKernel M (precision_B_pos hx hDelta hB)) h).real (terminalGoodSet M C eps) := by
  simp only [suffixGoodProbability,suffixJointKernel_terminal]

theorem suffixGoodProbability_recursion {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (j : Fin d) (h : Model.Vector M) :
    suffixGoodProbability M hx hDelta hB C eps j h=
      ∫g,suffixGoodProbability M hx hDelta hB C eps ((j : ℕ)+1) (h+shift M (Delta j) g)
        ∂gaussianTilt (shift M (Delta j)) (x j) (envelope M x Delta B ((j : ℕ)+1)) h := by
  have H := integral_kernel_real_comp (suffixJointKernel M hx hDelta hB ((j : ℕ)+1))
    (spineStep M hx hDelta hB j) h (terminalGoodSet M C eps) (terminalGoodSet_measurable M C eps)
  rw [← suffixJointKernel_succ M hx hDelta hB j] at H
  change (∫z,suffixGoodProbability M hx hDelta hB C eps ((j : ℕ)+1) z
    ∂spineStep M hx hDelta hB j h)=suffixGoodProbability M hx hDelta hB C eps j h at H
  have hTransition : spineStep M hx hDelta hB j h=
      (gaussianTilt (shift M (Delta j)) (x j) (envelope M x Delta B ((j : ℕ)+1)) h).map
        (fun g ↦ h+shift M (Delta j) g) := rfl
  rw [hTransition,integral_map (by fun_prop : Measurable
      (fun g : Model.Vector M ↦ h+shift M (Delta j) g)).aemeasurable
    (suffixGoodProbability_measurable M hx hDelta hB C eps ((j : ℕ)+1)).aestronglyMeasurable] at H
  exact H.symm

theorem suffixGoodProbability_fresh_integrable {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (C eps : ℝ) (j : Fin d) (h : Model.Vector M) :
    Integrable (fun g ↦ suffixGoodProbability M hx hDelta hB C eps ((j : ℕ)+1)
        (h+shift M (Delta j) g))
      (gaussianTilt (shift M (Delta j)) (x j) (envelope M x Delta B ((j : ℕ)+1)) h) := by
  haveI : IsProbabilityMeasure
      (gaussianTilt (shift M (Delta j)) (x j) (envelope M x Delta B ((j : ℕ)+1)) h) := by
    change IsProbabilityMeasure ((freshKernel M (mass := x j)
      (precision_pos hx hDelta hB ((j : ℕ)+1)) (hDelta j)
      (by rw [step_precision]; exact precision_pos hx hDelta hB j)
      (profileConstant M x Delta B ((j : ℕ)+1))) h)
    infer_instance
  apply Integrable.of_bound
    ((suffixGoodProbability_measurable M hx hDelta hB C eps ((j : ℕ)+1)).comp
      (by fun_prop)).aestronglyMeasurable 1
  exact .of_forall (fun g ↦ by
    have H := suffixGoodProbability_mem_Icc M hx hDelta hB C eps ((j : ℕ)+1) (h+shift M (Delta j) g)
    rw [Real.norm_eq_abs,Function.comp_apply,abs_of_nonneg H.1]
    exact H.2)

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSuffixGood
