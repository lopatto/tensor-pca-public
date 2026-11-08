-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A finite measurable first-good partition. This constructs sets rather
than a prior-dependent polynomial or an unrestricted measurable selector. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGFirstGoodPartition
open Set MeasureTheory
open scoped BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X] {J : ℕ}

def firstGood (good : Fin J→Set X) (j : Fin J) : Set X :=
  good j∩⋂i : Fin J,if i<j then (good i)ᶜ else univ

 theorem mem_firstGood_iff (good : Fin J→Set X) (j : Fin J) (x : X) :
    x∈firstGood good j↔x∈good j ∧ ∀i : Fin J,i<j→x∉good i := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro i hij
    have H := mem_iInter.mp h.2 i
    simpa only [if_pos hij,mem_compl_iff] using H
  · rintro ⟨hj,h⟩
    refine ⟨hj,mem_iInter.mpr (fun i ↦ ?_)⟩
    by_cases hij : i<j
    · simpa only [if_pos hij,mem_compl_iff] using h i hij
    · simp only [if_neg hij,mem_univ]

 theorem firstGood_measurable (good : Fin J→Set X) (hgood : ∀j,MeasurableSet (good j)) (j : Fin J) :
    MeasurableSet (firstGood good j) := by
  apply (hgood j).inter
  exact MeasurableSet.iInter (fun i ↦ by split_ifs; exacts [(hgood i).compl,MeasurableSet.univ])

 theorem firstGood_subset (good : Fin J→Set X) (j : Fin J) : firstGood good j⊆good j := inter_subset_left

 theorem firstGood_disjoint (good : Fin J→Set X) {i j : Fin J} (hij : i≠j) :
    Disjoint (firstGood good i) (firstGood good j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  rw [mem_firstGood_iff] at hi hj
  rcases lt_or_gt_of_ne hij with h|h
  · exact hj.2 i h hi.1
  · exact hi.2 j h hj.1

 theorem exists_firstGood (good : Fin J→Set X) (x : X) (hExists : ∃j,x∈good j) :
    ∃j,x∈firstGood good j := by
  classical
  let S := Finset.univ.filter (fun j : Fin J ↦ x∈good j)
  have hS : S.Nonempty := by
    obtain ⟨j,hj⟩ := hExists
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩⟩
  let j := S.min' hS
  have hj : x∈good j := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  refine ⟨j,(mem_firstGood_iff good j x).mpr ⟨hj,?_⟩⟩
  intro i hij hi
  have hLe : j≤ i := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
  exact (not_lt_of_ge hLe) hij

 theorem firstGood_cover (good : Fin J→Set X) (hExists : ∀x,∃j,x∈good j) :
    (⋃j,firstGood good j)=univ := by
  ext x
  simp only [mem_iUnion,mem_univ,iff_true]
  exact exists_firstGood good x (hExists x)

 theorem sum_firstGood_restrictions_le (good : Fin J→Set X) (hExists : ∀x,∃j,x∈good j)
    (error : Fin J→X→ℝ) {eta : ℝ} (hBound : ∀j x,x∈good j→error j x≤eta) (x : X) :
    (∑j : Fin J,(firstGood good j).indicator (error j) x)≤eta := by
  classical
  obtain ⟨j,hj⟩ := exists_firstGood good x (hExists x)
  have hOthers (i : Fin J) (hij : i≠j) : x∉firstGood good i :=
    fun hi ↦ (Set.disjoint_left.mp (firstGood_disjoint good hij)) hi hj
  calc
    _=(firstGood good j).indicator (error j) x := Finset.sum_eq_single j
      (fun i _ hij ↦ indicator_of_notMem (hOthers i hij) _) (fun h ↦ False.elim (h (Finset.mem_univ j)))
    _=error j x := indicator_of_mem hj _
    _≤eta := hBound j x (firstGood_subset good j hj)
end
end TensorPCA.NonRSLowerProofs.FiniteGGFirstGoodPartition
