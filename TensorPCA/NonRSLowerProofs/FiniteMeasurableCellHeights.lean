-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Order.Monotone.Defs

/-! A global height family obtained from a finite measurable partition. The integral
decomposition retains each cell's original mass; no conditional normalization or
choice of a background prior is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteMeasurableCellHeights
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {I S P : Type*} [Fintype I] [MeasurableSpace S] [MeasurableSpace P] {d : ℕ}

def gluedHeights (cell : I→Set S) (x : I→S→Fin d→ℝ) (s : S) : Fin d→ℝ :=
  ∑i,(cell i).indicator (x i) s

theorem gluedHeights_eq_of_mem (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) {i : I} {s : S}
    (hs : s∈cell i) : gluedHeights cell x s=x i s := by
  classical
  have hOthers (j : I) (hj : j≠i) : s∉cell j :=
    fun h => (Set.disjoint_left.mp (hDisjoint j i hj)) h hs
  calc
    _ = (cell i).indicator (x i) s :=
      Finset.sum_eq_single i
        (fun j _ hj => indicator_of_notMem (hOthers j hj) _)
        (fun h => False.elim (h (Finset.mem_univ i)))
    _ = _ := indicator_of_mem hs _

theorem gluedHeights_measurable (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hCell : ∀i,MeasurableSet (cell i)) (hx : ∀i,Measurable (x i)) :
    Measurable (gluedHeights cell x) := by
  classical
  exact Finset.measurable_fun_sum _ (fun i _ => (hx i).indicator (hCell i))

private theorem exists_cell (cell : I→Set S) (hCover : (⋃i,cell i)=univ) (s : S) :
    ∃i,s∈cell i := by
  have h : s∈⋃i,cell i := by rw [hCover]; exact mem_univ s
  exact mem_iUnion.mp h

theorem gluedHeights_positive (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    (hx : ∀i s,s∈cell i→∀j,0<x i s j) : ∀s j,0<gluedHeights cell x s j := by
  intro s j
  obtain ⟨i,hi⟩ := exists_cell cell hCover s
  rw [gluedHeights_eq_of_mem cell x hDisjoint hi]
  exact hx i s hi j

theorem gluedHeights_strictMono (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    (hx : ∀i s,s∈cell i→StrictMono (x i s)) : ∀s,StrictMono (gluedHeights cell x s) := by
  intro s
  obtain ⟨i,hi⟩ := exists_cell cell hCover s
  rw [gluedHeights_eq_of_mem cell x hDisjoint hi]
  exact hx i s hi

theorem gluedHeights_le_one (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    (hx : ∀i s,s∈cell i→∀j,x i s j≤1) : ∀s j,gluedHeights cell x s j≤1 := by
  intro s j
  obtain ⟨i,hi⟩ := exists_cell cell hCover s
  rw [gluedHeights_eq_of_mem cell x hDisjoint hi]
  exact hx i s hi j

/-- Arbitrary tests of the glued family split pointwise into the original
cell masks. The projection permits an independent Gaussian parameter. -/
theorem glued_test_eq_cell_sum (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    (proj : P→S) (F : P→(Fin d→ℝ)→ℝ) (p : P) :
    F p (gluedHeights cell x (proj p))=
      ∑i,(proj ⁻¹'cell i).indicator (fun p => F p (x i (proj p))) p := by
  classical
  obtain ⟨i,hi⟩ := exists_cell cell hCover (proj p)
  rw [gluedHeights_eq_of_mem cell x hDisjoint hi]
  have hOthers (j : I) (hj : j≠i) : p∉proj ⁻¹'cell j :=
    fun h => (Set.disjoint_left.mp (hDisjoint j i hj)) h hi
  symm
  calc
    _ = (proj ⁻¹'cell i).indicator (fun p => F p (x i (proj p))) p :=
      Finset.sum_eq_single (f := fun j : I =>
        (proj ⁻¹'cell j).indicator (fun p => F p (x j (proj p))) p) i
        (fun j _ hj => indicator_of_notMem (hOthers j hj) _)
        (fun h => False.elim (h (Finset.mem_univ i)))
    _ = _ := indicator_of_mem (show p∈proj ⁻¹'cell i from hi) _

theorem glued_test_measurable (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hCell : ∀i,MeasurableSet (cell i)) (hx : ∀i,Measurable (x i))
    {proj : P→S} (hProj : Measurable proj) {F : P→(Fin d→ℝ)→ℝ}
    (hF : Measurable (fun p : P×(Fin d→ℝ) => F p.1 p.2)) :
    Measurable (fun p => F p (gluedHeights cell x (proj p))) :=
  hF.comp (measurable_id.prodMk ((gluedHeights_measurable cell x hCell hx).comp hProj))

/-- Restricted integrability suffices, even if a candidate is uncontrolled
away from its own cell. All original cell masses are retained exactly. -/
theorem glued_test_integrable_and_integral_eq (cell : I→Set S) (x : I→S→Fin d→ℝ)
    (hCell : ∀i,MeasurableSet (cell i))
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    {proj : P→S} (hProj : Measurable proj) (F : P→(Fin d→ℝ)→ℝ) (mu : Measure P)
    (hInt : ∀i,IntegrableOn (fun p => F p (x i (proj p))) (proj ⁻¹'cell i) mu) :
    Integrable (fun p => F p (gluedHeights cell x (proj p))) mu ∧
      (∫p,F p (gluedHeights cell x (proj p))∂mu)=
        ∑i,∫p in proj ⁻¹'cell i,F p (x i (proj p))∂mu := by
  classical
  have hMask (i : I) : Integrable ((proj ⁻¹'cell i).indicator (fun p => F p (x i (proj p)))) mu :=
    (hInt i).integrable_indicator ((hCell i).preimage hProj)
  have hSum := integrable_finsetSum (s := Finset.univ) (fun i _ => hMask i)
  have hEq : (fun p => F p (gluedHeights cell x (proj p)))=
      fun p => ∑i,(proj ⁻¹'cell i).indicator (fun p => F p (x i (proj p))) p := by
    funext p
    exact glued_test_eq_cell_sum cell x hDisjoint hCover proj F p
  refine ⟨hEq.symm ▸ hSum,?_⟩
  rw [hEq,integral_finsetSum _ (fun i _ => hMask i)]
  exact Finset.sum_congr rfl (fun i _ => integral_indicator ((hCell i).preimage hProj))

end
end TensorPCA.NonRSLowerProofs.FiniteMeasurableCellHeights
