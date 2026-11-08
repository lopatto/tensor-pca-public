-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramRealization
public import TensorPCA.NonRSLowerProofs.FiniteGGCloningGeometry

/-! A finite prechosen coordinate-window cover of ordered bad unit-Gram triples. Centers
themselves are unit-Gram matrices; the finite family is allowed to be empty when the
bad set is empty.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGTripleWindowCover
open Matrix Set
open FiniteUnitGramRealization FiniteGGCloningGeometry
noncomputable section

def orderedBadUnitGram (gap : ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {A | A∈unitGramSet 3 ∧ A 0 1+gap≤A 0 2 ∧ A 0 2≤A 1 2}

def tripleWindow (eps : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {B | |B 0 1-A 0 1|<eps ∧ |B 0 2-A 0 2|<eps ∧ |B 1 2-A 1 2|<eps}

theorem orderedBadUnitGram_isCompact (gap : ℝ) : IsCompact (orderedBadUnitGram gap) := by
  have h01 : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 0 1) :=
    (continuous_apply 1).comp (continuous_apply 0)
  have h02 : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 0 2) :=
    (continuous_apply 2).comp (continuous_apply 0)
  have h12 : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 1 2) :=
    (continuous_apply 2).comp (continuous_apply 1)
  have hGap : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A 0 1+gap≤A 0 2} :=
    isClosed_le (h01.add_const gap) h02
  have H := (unitGramSet_isCompact 3).inter_right (hGap.inter (isClosed_le h02 h12))
  simpa only [orderedBadUnitGram,Set.setOf_and,Set.setOf_mem_eq] using H

theorem tripleWindow_isOpen (eps : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    IsOpen (tripleWindow eps A) := by
  have hEntry (i j : Fin 3) : Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ |B i j-A i j|) := by
    have hE : Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ B i j) :=
      (continuous_apply j).comp (continuous_apply i)
    have hSub : Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ B i j-A i j) := by
      convert hE.sub (continuous_const : Continuous (fun _ : Matrix (Fin 3) (Fin 3) ℝ ↦ A i j)) using 1
    exact hSub.abs
  exact (isOpen_lt (hEntry 0 1) continuous_const).inter
    ((isOpen_lt (hEntry 0 2) continuous_const).inter (isOpen_lt (hEntry 1 2) continuous_const))

theorem exists_prechosen_ordered_triple_cover (gap : ℝ) {eps : ℝ} (heps : 0<eps) :
    ∃ T : Finset {A : Matrix (Fin 3) (Fin 3) ℝ // A∈orderedBadUnitGram gap},
      ∀ B∈orderedBadUnitGram gap,∃ A∈T,B∈tripleWindow eps A.val := by
  let U : {A : Matrix (Fin 3) (Fin 3) ℝ // A∈orderedBadUnitGram gap} → Set (Matrix (Fin 3) (Fin 3) ℝ) :=
    fun A ↦ tripleWindow eps A.val
  have hCover : orderedBadUnitGram gap⊆⋃ A,U A := by
    intro B hB
    exact Set.mem_iUnion.mpr ⟨⟨B,hB⟩,by simp only [U,tripleWindow,Set.mem_setOf_eq,sub_self,abs_zero]; exact ⟨heps,heps,heps⟩⟩
  obtain ⟨T,hT⟩ := (orderedBadUnitGram_isCompact gap).elim_finite_subcover U
    (fun A ↦ tripleWindow_isOpen eps A.val) hCover
  refine ⟨T,?_⟩
  intro B hB
  obtain ⟨A,hA⟩ := Set.mem_iUnion.mp (hT hB)
  obtain ⟨hAT,hWin⟩ := Set.mem_iUnion.mp hA
  exact ⟨A,hAT,hWin⟩

theorem orderedBadUnitGram_center_margin {gap : ℝ} (hgap : 0<gap)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A∈orderedBadUnitGram gap) :
    A 1 2≤1-gap^2/2 := by
  have hPSD := hA.1.1
  have hDiag := hA.1.2
  have hab : gap≤A 0 2-A 0 1 := by linarith only [hA.2.1]
  have hxy : |inner ℝ (realization A 0) (realization A 1)-A 0 1|≤(0 : ℝ) := by
    rw [realization_inner A hPSD]; simp
  have hxz : |inner ℝ (realization A 0) (realization A 2)-A 0 2|≤(0 : ℝ) := by
    rw [realization_inner A hPSD]; simp
  have hyz : |inner ℝ (realization A 1) (realization A 2)-A 1 2|≤(0 : ℝ) := by
    rw [realization_inner A hPSD]; simp
  have H := window_center_upper_margin (le_refl (0 : ℝ)) (by simpa only [mul_zero] using hgap.le) hab
    (realization A 0) (realization A 1) (realization A 2)
    (realization_norm A hPSD hDiag 0) (realization_norm A hPSD hDiag 1) (realization_norm A hPSD hDiag 2)
    hxy hxz hyz
  simpa only [mul_zero,sub_zero,add_zero] using H

end
end TensorPCA.NonRSLowerProofs.FiniteGGTripleWindowCover
