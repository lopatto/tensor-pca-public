-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSpineCutoffs

/-! The joint terminal field and spin, retaining the conditional root.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalJoint
open MeasureTheory ProbabilityTheory
open FiniteGaussianAffineKernel FiniteGaussianQuadraticKernel
open FiniteGaussianQuadraticSpine FiniteGaussianQuadraticForwardSpine
open FiniteCSGaussianDepthPrecision
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem composeSpinKernels_forward {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (terminal initial : Kernel (Model.Vector M) (Model.Vector M)) :
    terminal ∘ₖ forwardKernels steps initial=composeSpinKernels steps terminal ∘ₖ initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons a steps ih =>
    change terminal ∘ₖ forwardKernels steps (a ∘ₖ initial)=
      (composeSpinKernels steps terminal ∘ₖ a) ∘ₖ initial
    rw [ih,Kernel.comp_assoc]

theorem forwardKernels_right_comp {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (left right : Kernel (Model.Vector M) (Model.Vector M)) :
    forwardKernels steps (left ∘ₖ right)=forwardKernels steps left ∘ₖ right := by
  have H1 := composeSpinKernels_forward steps Kernel.id (left ∘ₖ right)
  have H2 := composeSpinKernels_forward steps Kernel.id left
  simp only [Kernel.id_comp] at H1 H2
  exact H1.trans ((Kernel.comp_assoc _ left right).symm.trans
    (congrArg (fun K => K ∘ₖ right) H2.symm))

theorem forwardKernels_markov {M : ℕ}
    (steps : List (Kernel (Model.Vector M) (Model.Vector M)))
    (initial : Kernel (Model.Vector M) (Model.Vector M)) [IsMarkovKernel initial]
    (hSteps : ∀K∈steps,IsMarkovKernel K) : IsMarkovKernel (forwardKernels steps initial) := by
  induction steps generalizing initial with
  | nil => change IsMarkovKernel initial; infer_instance
  | cons a steps ih =>
    haveI : IsMarkovKernel a := hSteps a (by simp)
    change IsMarkovKernel (forwardKernels steps (a ∘ₖ initial))
    exact ih _ (fun K hK => hSteps K (by simp [hK]))

def fieldKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    Kernel (Model.Vector M) (Model.Vector M) :=
  forwardKernels (spineKernels M hx hDelta hB) Kernel.id

instance fieldKernel_markov {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) : IsMarkovKernel (fieldKernel M hx hDelta hB) := by
  apply forwardKernels_markov
  intro K hK
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hK
  infer_instance

theorem fieldKernel_root {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) :
    fieldKernel M hx hDelta hB ∘ₖ affineKernel M 0 (Real.sqrt y0)=
      prefixStateKernel M hx hDelta hB y0 d := by
  rw [fieldKernel,← forwardKernels_right_comp,Kernel.id_comp,prefixStateKernel]
  congr 1
  have H : (spineKernels M hx hDelta hB).length=d := by simp [spineKernels]
  simpa only [H] using (List.take_length (l := spineKernels M hx hDelta hB)).symm

theorem terminal_fieldKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    terminalSpinKernel M (precision_B_pos hx hDelta hB) ∘ₖ fieldKernel M hx hDelta hB=
      spinKernel M hx hDelta hB := by
  rw [fieldKernel,composeSpinKernels_forward,Kernel.comp_id]
  rfl

def terminalJointKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    Kernel (Model.Vector M) (Model.Vector M×Model.Vector M) :=
  (Kernel.id ×ₖ terminalSpinKernel M (precision_B_pos hx hDelta hB)) ∘ₖ fieldKernel M hx hDelta hB

instance terminalJointKernel_markov {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) : IsMarkovKernel (terminalJointKernel M hx hDelta hB) := by
  unfold terminalJointKernel
  infer_instance

theorem terminalJointKernel_fst {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    (terminalJointKernel M hx hDelta hB).fst=fieldKernel M hx hDelta hB := by
  simp only [terminalJointKernel,Kernel.fst_comp,Kernel.fst_prod,Kernel.id_comp]

theorem terminalJointKernel_snd {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) :
    (terminalJointKernel M hx hDelta hB).snd=spinKernel M hx hDelta hB := by
  simp only [terminalJointKernel,Kernel.snd_comp,Kernel.snd_prod,terminal_fieldKernel]

def rootJointKernel {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) :
    Kernel (Model.Vector M) (Model.Vector M×Model.Vector M) :=
  terminalJointKernel M hx hDelta hB ∘ₖ affineKernel M 0 (Real.sqrt y0)

instance rootJointKernel_markov {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) : IsMarkovKernel (rootJointKernel M hx hDelta hB y0) := by
  unfold rootJointKernel
  infer_instance

theorem rootJointKernel_fst {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) :
    (rootJointKernel M hx hDelta hB y0).fst=prefixStateKernel M hx hDelta hB y0 d := by
  rw [rootJointKernel,Kernel.fst_comp,terminalJointKernel_fst,fieldKernel_root]

theorem rootJointKernel_snd_eq_stdGaussian {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B) :
    (rootJointKernel M hx hDelta hB y0).snd 0=stdGaussian (Model.Vector M) := by
  rw [rootJointKernel,Kernel.snd_comp,terminalJointKernel_snd]
  exact quenchedSpinLaw_eq_stdGaussian M hx hDelta hB hy hroot

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalJoint
