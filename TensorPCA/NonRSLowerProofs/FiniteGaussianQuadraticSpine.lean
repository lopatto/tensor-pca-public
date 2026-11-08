-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticKernel
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticLogSteps

/-! The finite Gaussian quadratic spine and its terminal spin law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSpine
open MeasureTheory ProbabilityTheory
open FiniteGaussianAffineKernel FiniteGaussianQuadraticKernel
open FiniteGaussianQuadraticLogSteps FiniteCSGaussianDepthPrecision
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def spinVariance {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) (i : ℕ) : ℝ :=
  B⁻¹+tail (fun j => Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1))) i

theorem precision_B_pos {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) : 0< B := by
  simpa only [precision_end] using precision_pos hx hDelta hB d

theorem step_precision {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) (j : Fin d) :
    precision x Delta B ((j : ℕ)+1)-x j*Delta j=precision x Delta B j := by
  linarith only [precision_succ x Delta B j]

theorem spinVariance_nonneg {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (i : ℕ) :
    0≤spinVariance x Delta B i := by
  exact add_nonneg (inv_nonneg.mpr (precision_B_pos hx hDelta hB).le)
    (tail_nonneg (fun j => div_nonneg (hDelta j)
      (mul_pos (precision_pos hx hDelta hB j) (precision_pos hx hDelta hB ((j : ℕ)+1))).le) i)

theorem spinVariance_succ {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) (j : Fin d) :
    spinVariance x Delta B j=spinVariance x Delta B ((j : ℕ)+1)+
      Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) := by
  have H := tail_succ (fun l => Delta l/
    (precision x Delta B l*precision x Delta B ((l : ℕ)+1))) j.isLt
  unfold spinVariance
  linarith only [H]

def spineStep {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (j : Fin d) :
    Kernel (Model.Vector M) (Model.Vector M) :=
  transitionKernel M (mass := x j) (precision_pos hx hDelta hB ((j : ℕ)+1)) (hDelta j)
    (by rw [step_precision]; exact precision_pos hx hDelta hB j)
    (profileConstant M x Delta B ((j : ℕ)+1))

instance spineStep_markov {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (j : Fin d) :
    IsMarkovKernel (spineStep M hx hDelta hB j) := by
  unfold spineStep
  infer_instance

def spineKernels {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    List (Kernel (Model.Vector M) (Model.Vector M)) :=
  List.ofFn (spineStep M hx hDelta hB)

def composeSpinKernels {M : ℕ} (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (terminal : Kernel (Model.Vector M) (Model.Vector M)) :
    Kernel (Model.Vector M) (Model.Vector M) :=
  steps.foldr (fun step downstream => downstream ∘ₖ step) terminal

def spinKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    Kernel (Model.Vector M) (Model.Vector M) :=
  composeSpinKernels (spineKernels M hx hDelta hB)
    (terminalSpinKernel M (precision_B_pos hx hDelta hB))

theorem composeSpinKernels_eq_of_recursion {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (terminal : Kernel (Model.Vector M) (Model.Vector M))
    (H : ℕ→Kernel (Model.Vector M) (Model.Vector M))
    (hEnd : H steps.length=terminal)
    (hStep : ∀(i : ℕ) (hi : i< steps.length),H i=H (i+1) ∘ₖ steps[i]) :
    composeSpinKernels steps terminal=H 0 := by
  induction steps generalizing H with
  | nil => simpa only [composeSpinKernels,List.foldr_nil,List.length_nil] using hEnd.symm
  | cons a steps ih =>
    have hTailEnd : (fun i => H (i+1)) steps.length=terminal := by
      simpa only [List.length_cons] using hEnd
    have hTailStep (i : ℕ) (hi : i< steps.length) :
        (fun j => H (j+1)) i=(fun j => H (j+1)) (i+1) ∘ₖ steps[i] := by
      have HS := hStep (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
      simpa only [List.getElem_cons_succ] using HS
    have HT := ih (fun i => H (i+1)) hTailEnd hTailStep
    have H0 := hStep 0 (by simp)
    simp only [List.getElem_cons_zero,zero_add] at H0
    change composeSpinKernels steps terminal ∘ₖ a=H 0
    rw [HT]
    exact H0.symm

theorem spinKernel_eq_affine {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    spinKernel M hx hDelta hB=
      affineKernel M (precision x Delta B 0)⁻¹ (Real.sqrt (spinVariance x Delta B 0)) := by
  let H := fun i => affineKernel M (precision x Delta B i)⁻¹ (Real.sqrt (spinVariance x Delta B i))
  have hEnd : H (spineKernels M hx hDelta hB).length=
      terminalSpinKernel M (precision_B_pos hx hDelta hB) := by
    rw [spineKernels,List.length_ofFn,terminalSpinKernel_eq_affine]
    simp only [H,precision_end,spinVariance,tail_end,add_zero]
  have hStep (i : ℕ) (hi : i<(spineKernels M hx hDelta hB).length) :
      H i=H (i+1) ∘ₖ (spineKernels M hx hDelta hB)[i] := by
    have hi' : i< d := by simpa only [spineKernels,List.length_ofFn] using hi
    let j : Fin d := ⟨i,hi'⟩
    have hD := step_precision x Delta B j
    have HK := conditional_spin_comp M (precision_pos hx hDelta hB (i+1)) (hDelta j)
      (show 0< precision x Delta B (i+1)-x j*Delta j by rw [hD]; exact precision_pos hx hDelta hB i)
      (spinVariance_nonneg hx hDelta hB (i+1)) (profileConstant M x Delta B (i+1))
    conv_rhs at HK => rw [hD,← spinVariance_succ x Delta B j]
    simpa only [spineKernels,List.getElem_ofFn,spineStep,H] using HK.symm
  exact composeSpinKernels_eq_of_recursion _ _ H hEnd hStep

instance spinKernel_markov {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) : IsMarkovKernel (spinKernel M hx hDelta hB) := by
  rw [spinKernel_eq_affine]
  infer_instance

/-- The quenched Gaussian root followed by every normalized fresh-bank transition and
the terminal spin tilt.
-/
def quenchedSpinLaw {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) : Measure (Model.Vector M) :=
  (spinKernel M hx hDelta hB ∘ₖ affineKernel M 0 (Real.sqrt y0)) 0

theorem quenchedSpinLaw_eq_stdGaussian {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B) :
    quenchedSpinLaw M hx hDelta hB y0=stdGaussian (Model.Vector M) := by
  have hP := precision_pos hx hDelta hB 0
  have hV := spinVariance_nonneg hx hDelta hB 0
  have hvariance : ((precision x Delta B 0)⁻¹*Real.sqrt y0)^2+
      (Real.sqrt (spinVariance x Delta B 0))^2=1 := by
    rw [mul_pow,Real.sq_sqrt hy,Real.sq_sqrt hV]
    have HE : (precision x Delta B 0)⁻¹^2*y0=y0/(precision x Delta B 0)^2 := by
      field_simp
    rw [HE,spinVariance,tail_zero]
    simpa only [one_div] using (show y0/(precision x Delta B 0)^2+
      (B⁻¹+∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1 by
        simpa only [one_div] using (show y0/(precision x Delta B 0)^2+
          (1/B+∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1 by
            linarith only [hroot]))
  rw [quenchedSpinLaw,spinKernel_eq_affine,affineKernel_comp,hvariance,Real.sqrt_one,
    mul_zero,affineKernel_apply]
  simp only [zero_smul,zero_add,one_smul,Measure.map_id]
  exact Measure.map_id

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSpine
