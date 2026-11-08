-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionSetoid
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeCylinder
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Classify finite arrays by tree cylinders. Every bad-threshold array is assigned to a
fixed default tree, retaining a full probability law without conditioning on a good-
array restriction.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeExtraction
open MeasureTheory Set
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open SphericalGGTreeCylinder NonRSUpperProofs.SphericalPositivePerturbation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

local instance treeMeasurableSpace (depth n : ℕ) : MeasurableSpace (NestedPartition depth n) := ⊤

def thresholdGood {N depth n : ℕ} (cuts : Fin depth→ℝ) (old : Fin n→UnitSpin N) : Prop :=
  ∀l : Fin depth,Equivalence (fun i j : Fin n ↦ cuts l≤unitOverlap (old i) (old j))

private theorem level_trans {depth n : ℕ} (t : NestedPartition depth n) (l : Fin depth)
    (i j k : Fin n) (hij : (l : ℕ)<coalescence t i j) (hjk : (l : ℕ)<coalescence t j k) :
    (l : ℕ)<coalescence t i k := by
  induction depth generalizing n with
  | zero => exact Fin.elim0 l
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
    obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
    obtain ⟨⟨d,k⟩,rfl⟩ := c.equivSigma.surjective k
    have hab : a=b := by
      by_contra h
      rw [coalescence_cross c f h] at hij
      exact Nat.not_lt_zero _ hij
    subst b
    have had : a=d := by
      by_contra h
      rw [coalescence_cross c f h] at hjk
      exact Nat.not_lt_zero _ hjk
    subst d
    rw [coalescence_same] at hij hjk ⊢
    cases l using Fin.cases with
    | zero => exact Nat.zero_lt_succ _
    | succ l =>
      apply Nat.succ_lt_succ
      apply ih (f a) l i j k
      · simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using hij
      · simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using hjk

theorem thresholdGood_of_treeCylinder {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (t : NestedPartition depth n) (old : Fin n→UnitSpin N) (ht : treeCylinder cuts t old) :
    thresholdGood cuts old := by
  intro l
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (ht l i i).1 (by simpa only [coalescence_self] using l.isLt)
  · intro i j hij
    apply (ht l j i).1
    rw [coalescence_symm]
    exact (ht l i j).2 hij
  · intro i j k hij hjk
    exact (ht l i k).1 (level_trans t l i j k ((ht l i j).2 hij) ((ht l j k).2 hjk))

theorem exists_treeCylinder_of_thresholdGood {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (old : Fin n→UnitSpin N) (hgood : thresholdGood cuts old) :
    ∃t : NestedPartition depth n,treeCylinder cuts t old := by
  let r (l : Fin depth) : Setoid (Fin n) :=
    ⟨fun i j ↦ cuts l≤unitOverlap (old i) (old j),hgood l⟩
  have hRefine : ∀l k : Fin depth,l≤k→∀i j : Fin n,(r k).r i j→(r l).r i j := by
    intro l k hlk i j h
    exact (hcuts hlk).trans h
  obtain ⟨t,ht⟩ := exists_nestedPartition depth n r hRefine
  exact ⟨t,ht⟩

theorem thresholdGood_iff_exists_treeCylinder {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (old : Fin n→UnitSpin N) :
    thresholdGood cuts old ↔ ∃t : NestedPartition depth n,treeCylinder cuts t old :=
  ⟨exists_treeCylinder_of_thresholdGood cuts hcuts old,
    fun ⟨t,ht⟩ ↦ thresholdGood_of_treeCylinder cuts t old ht⟩

theorem treeCylinder_unique {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (old : Fin n→UnitSpin N) (t u : NestedPartition depth n)
    (ht : treeCylinder cuts t old) (hu : treeCylinder cuts u old) : t=u :=
  eq_of_levelRelations depth n t u (fun l i j ↦ (ht l i j).trans (hu l i j).symm)

def extractTree {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (old : Fin n→UnitSpin N) : NestedPartition depth n :=
  if h : thresholdGood cuts old then (exists_treeCylinder_of_thresholdGood cuts hcuts old h).choose
  else default

theorem treeCylinder_extractTree_of_good {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (old : Fin n→UnitSpin N) (hgood : thresholdGood cuts old) :
    treeCylinder cuts (extractTree cuts hcuts old) old := by
  simp only [extractTree,dif_pos hgood]
  exact (exists_treeCylinder_of_thresholdGood cuts hcuts old hgood).choose_spec

theorem extractTree_eq_default_of_bad {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (old : Fin n→UnitSpin N) (hbad : ¬thresholdGood cuts old) :
    extractTree cuts hcuts old=default := by simp only [extractTree,dif_neg hbad]

theorem extractTree_eq_iff {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (old : Fin n→UnitSpin N) (t : NestedPartition depth n) :
    extractTree cuts hcuts old=t ↔ treeCylinder cuts t old ∨ (¬thresholdGood cuts old ∧ t=default) := by
  by_cases hgood : thresholdGood cuts old
  · constructor
    · intro h
      exact Or.inl (h ▸ treeCylinder_extractTree_of_good cuts hcuts old hgood)
    · rintro (ht | ⟨hbad,_⟩)
      · exact treeCylinder_unique cuts old _ t (treeCylinder_extractTree_of_good cuts hcuts old hgood) ht
      · exact (hbad hgood).elim
  · rw [extractTree_eq_default_of_bad cuts hcuts old hgood]
    constructor
    · intro h
      exact Or.inr ⟨hgood,h.symm⟩
    · rintro (ht | ⟨_,h⟩)
      · exact (hgood (thresholdGood_of_treeCylinder cuts t old ht)).elim
      · exact h.symm

theorem thresholdGood_measurable {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) : MeasurableSet {old : Fin n→UnitSpin N | thresholdGood cuts old} := by
  have H : {old : Fin n→UnitSpin N | thresholdGood cuts old}=
      ⋃t : NestedPartition depth n,{old | treeCylinder cuts t old} := by
    ext old
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    exact thresholdGood_iff_exists_treeCylinder cuts hcuts old
  rw [H]
  exact MeasurableSet.iUnion (treeCylinder_measurable cuts)

theorem extractTree_fiber_measurable {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (t : NestedPartition depth n) :
    MeasurableSet {old : Fin n→UnitSpin N | extractTree cuts hcuts old=t} := by
  have H : {old : Fin n→UnitSpin N | extractTree cuts hcuts old=t}=
      {old | treeCylinder cuts t old} ∪ ({old | thresholdGood cuts old}ᶜ∩{old : Fin n→UnitSpin N | t=default}) := by
    ext old
    exact extractTree_eq_iff cuts hcuts old t
  rw [H]
  exact (treeCylinder_measurable cuts t).union
    ((thresholdGood_measurable cuts hcuts).compl.inter (MeasurableSet.const _))

theorem extractTree_measurable {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) : Measurable (extractTree (N := N) (n := n) cuts hcuts) := by
  apply measurable_to_countable'
  intro t
  exact extractTree_fiber_measurable cuts hcuts t

def treePMF {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu] : PMF (NestedPartition depth n) :=
  (mu.map (extractTree cuts hcuts)).toPMF

theorem treePMF_apply {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu] (t : NestedPartition depth n) :
    treePMF cuts hcuts mu t=mu {old | extractTree cuts hcuts old=t} := by
  rw [treePMF,Measure.toPMF_apply,Measure.map_apply (extractTree_measurable cuts hcuts)
    (measurableSet_singleton t)]
  rfl

theorem good_extractTree_fiber {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (t : NestedPartition depth n) :
    {old : Fin n→UnitSpin N | thresholdGood cuts old ∧ extractTree cuts hcuts old=t}=
      {old | treeCylinder cuts t old} := by
  ext old
  constructor
  · rintro ⟨hg,he⟩
    exact he ▸ treeCylinder_extractTree_of_good cuts hcuts old hg
  · intro ht
    have hg := thresholdGood_of_treeCylinder cuts t old ht
    exact ⟨hg,treeCylinder_unique cuts old _ t (treeCylinder_extractTree_of_good cuts hcuts old hg) ht⟩

theorem treePMF_apply_eq_cylinder_add_bad {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu]
    (t : NestedPartition depth n) :
    treePMF cuts hcuts mu t=mu {old | treeCylinder cuts t old}+
      if t=default then mu {old | ¬thresholdGood cuts old} else 0 := by
  classical
  have Hset : {old : Fin n→UnitSpin N | extractTree cuts hcuts old=t}=
      {old | treeCylinder cuts t old} ∪ {old | ¬thresholdGood cuts old ∧ t=default} := by
    ext old
    exact extractTree_eq_iff cuts hcuts old t
  have Hd : Disjoint {old : Fin n→UnitSpin N | treeCylinder cuts t old}
      {old | ¬thresholdGood cuts old ∧ t=default} := by
    apply Set.disjoint_left.mpr
    intro old hc hb
    exact hb.1 (thresholdGood_of_treeCylinder cuts t old hc)
  have Hb : MeasurableSet {old : Fin n→UnitSpin N | ¬thresholdGood cuts old ∧ t=default} :=
    (thresholdGood_measurable cuts hcuts).compl.inter (MeasurableSet.const _)
  rw [treePMF_apply,Hset,measure_union Hd Hb]
  by_cases ht : t=default <;> simp [ht]


end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeExtraction
