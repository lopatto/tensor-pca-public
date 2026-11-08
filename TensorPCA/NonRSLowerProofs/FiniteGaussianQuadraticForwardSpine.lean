-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSpine
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformBounds

/-! Forward state laws of the normalized finite quadratic spine.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticForwardSpine
open MeasureTheory ProbabilityTheory
open FiniteGaussianAffineKernel FiniteGaussianQuadraticKernel
open FiniteGaussianQuadraticSpine FiniteGaussianQuadraticUniformBounds
open FiniteCSGaussianDepthPrecision
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def forwardKernels {M : ℕ} (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (initial : Kernel (Model.Vector M) (Model.Vector M)) :
    Kernel (Model.Vector M) (Model.Vector M) :=
  steps.foldl (fun current step => step ∘ₖ current) initial

theorem forwardKernels_eq_of_recursion {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (H : ℕ→Kernel (Model.Vector M) (Model.Vector M))
    (hStep : ∀(i : ℕ) (hi : i< steps.length),H (i+1)=steps[i] ∘ₖ H i) :
    forwardKernels steps (H 0)=H steps.length := by
  induction steps generalizing H with
  | nil => rfl
  | cons a steps ih =>
    have hTailStep (i : ℕ) (hi : i< steps.length) :
        (fun j => H (j+1)) (i+1)=steps[i] ∘ₖ (fun j => H (j+1)) i := by
      have HS := hStep (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
      simpa only [List.getElem_cons_succ] using HS
    have HT := ih (fun i => H (i+1)) hTailStep
    have H0 := hStep 0 (by simp)
    simp only [List.getElem_cons_zero,zero_add] at H0
    change forwardKernels steps (a ∘ₖ H 0)=H (steps.length+1)
    rw [← H0]
    exact HT

def stateVariance {d : ℕ} (x Delta : Fin d→ℝ) (B y0 : ℝ) (i : ℕ) : ℝ :=
  (precision x Delta B i)^2*prefixVariance x Delta B y0 i

def prefixStateKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) (i : ℕ) :
    Kernel (Model.Vector M) (Model.Vector M) :=
  forwardKernels ((spineKernels M hx hDelta hB).take i) (affineKernel M 0 (Real.sqrt y0))

theorem prefixVariance_succ {d : ℕ} (x Delta : Fin d→ℝ) (B y0 : ℝ) (j : Fin d) :
    prefixVariance x Delta B y0 ((j : ℕ)+1)=prefixVariance x Delta B y0 j+
      Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) := by
  unfold prefixVariance
  rw [prefix_succ _ j.isLt]
  ring

theorem stateVariance_zero {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hP : precision x Delta B 0≠0) : stateVariance x Delta B y0 0=y0 := by
  rw [stateVariance,prefixVariance,prefix_zero,add_zero]
  field_simp

theorem stateVariance_succ {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (j : Fin d) (hP : precision x Delta B j≠0) (hQ : precision x Delta B ((j : ℕ)+1)≠0) :
    (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)^2*stateVariance x Delta B y0 j+
      Delta j*precision x Delta B ((j : ℕ)+1)/precision x Delta B j=
      stateVariance x Delta B y0 ((j : ℕ)+1) := by
  unfold stateVariance
  rw [prefixVariance_succ]
  field_simp
  <;> ring

theorem prefixStateKernel_eq_affine {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    {i : ℕ} (hi : i≤d) :
    prefixStateKernel M hx hDelta hB y0 i=
      affineKernel M 0 (Real.sqrt (stateVariance x Delta B y0 i)) := by
  have hP := precision_pos hx hDelta hB
  have hV (l : ℕ) : 0≤stateVariance x Delta B y0 l :=
    mul_nonneg (sq_nonneg _) (prefixVariance_mem_Icc hx hDelta hB hy hroot l).1
  let H := fun l => affineKernel M 0 (Real.sqrt (stateVariance x Delta B y0 l))
  have hInitial : H 0=affineKernel M 0 (Real.sqrt y0) := by
    dsimp only [H]
    rw [stateVariance_zero (hP 0).ne']
  have hStep (l : ℕ) (hl : l< ((spineKernels M hx hDelta hB).take i).length) :
      H (l+1)=((spineKernels M hx hDelta hB).take i)[l] ∘ₖ H l := by
    have hld : l< d := by
      have hli : l< i := by
        simpa only [List.length_take,spineKernels,List.length_ofFn,Nat.min_eq_left hi] using hl
      exact lt_of_lt_of_le hli hi
    let j : Fin d := ⟨l,hld⟩
    have hGet : ((spineKernels M hx hDelta hB).take i)[l]=spineStep M hx hDelta hB j := by
      simp only [List.getElem_take,spineKernels,List.getElem_ofFn]
      rfl
    have hT : spineStep M hx hDelta hB j=
        affineKernel M (precision x Delta B (l+1)/precision x Delta B l)
          (Real.sqrt (Delta j*precision x Delta B (l+1)/precision x Delta B l)) := by
      unfold spineStep
      simp only [transitionKernel_eq_affine,step_precision]
      rfl
    have hnoise : (precision x Delta B (l+1)/precision x Delta B l*
        Real.sqrt (stateVariance x Delta B y0 l))^2+
        (Real.sqrt (Delta j*precision x Delta B (l+1)/precision x Delta B l))^2=
        stateVariance x Delta B y0 (l+1) := by
      rw [mul_pow,Real.sq_sqrt (hV l),Real.sq_sqrt
        (div_nonneg (mul_nonneg (hDelta j) (hP (l+1)).le) (hP l).le)]
      exact stateVariance_succ j (hP l).ne' (hP (l+1)).ne'
    rw [hGet,hT]
    dsimp only [H]
    rw [affineKernel_comp,hnoise,mul_zero]
  have HE := forwardKernels_eq_of_recursion ((spineKernels M hx hDelta hB).take i) H hStep
  rw [hInitial,List.length_take,spineKernels,List.length_ofFn,Nat.min_eq_left hi] at HE
  exact HE

theorem prefixStateKernel_norm_scale_bound {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (i : ℕ) : stateVariance x Delta B y0 i≤B^2 :=
  scaledPrefixVariance_le hx hDelta hB hy hroot i

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticForwardSpine
