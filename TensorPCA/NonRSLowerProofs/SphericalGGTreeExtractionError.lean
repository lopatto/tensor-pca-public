-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeExtraction
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeHeights
public import TensorPCA.NonRSLowerProofs.FiniteNestedLawComparison

/-! Exact real errors caused by assigning every bad threshold array to the unchanged
default tree. The full finite L1 correction is its bad-event mass once; root
insertion rows preserve that mass without a rare-parent or good-event normalization.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeExtractionError
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeHeights
open FiniteNestedPartition FiniteNestedInsertionNumerators FiniteNestedLawComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

theorem treePMF_real_atom {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu] (t : NestedPartition depth n) :
    (treePMF cuts hcuts mu t).toReal=mu.real {old | treeCylinder cuts t old}+
      if t=default then mu.real {old | ¬thresholdGood cuts old} else 0 := by
  classical
  rw [treePMF_apply_eq_cylinder_add_bad]
  by_cases ht : t=default
  · rw [if_pos ht,if_pos ht,ENNReal.toReal_add (measure_ne_top mu _) (measure_ne_top mu _)]
    rfl
  · simp only [if_neg ht,add_zero,ENNReal.toReal_zero]
    rfl

theorem treePMF_real_atom_sub {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu] (t : NestedPartition depth n) :
    (treePMF cuts hcuts mu t).toReal-mu.real {old | treeCylinder cuts t old}=
      if t=default then mu.real {old | ¬thresholdGood cuts old} else 0 := by
  rw [treePMF_real_atom cuts hcuts mu t]
  ring

theorem treePMF_real_atom_sub_nonneg {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu] (t : NestedPartition depth n) :
    0≤(treePMF cuts hcuts mu t).toReal-mu.real {old | treeCylinder cuts t old} := by
  rw [treePMF_real_atom_sub cuts hcuts mu t]
  split_ifs <;> positivity

theorem treePMF_cylinder_l1_eq_bad_mass {N depth n : ℕ} (cuts : Fin depth→ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu] :
    (∑t : NestedPartition depth n,|(treePMF cuts hcuts mu t).toReal-
      mu.real {old | treeCylinder cuts t old}|)=mu.real {old | ¬thresholdGood cuts old} := by
  classical
  simp_rw [abs_of_nonneg (treePMF_real_atom_sub_nonneg cuts hcuts mu _),treePMF_real_atom_sub cuts hcuts mu]
  simp

private theorem scalar_recurrence_error (a b A B w : ℝ) (ha : 0≤a-A) (hb : 0≤b-B) (hw : 0≤w) :
    |a-b*w|≤|A-B*w|+(a-A)+(b-B)*w := by
  have hEq : a-b*w=((A-B*w)+(a-A))-(b-B)*w := by ring
  rw [hEq]
  calc
    _≤|A-B*w+(a-A)|+|(b-B)*w| := abs_sub _ _
    _≤(|A-B*w|+|a-A|)+|(b-B)*w| := add_le_add (abs_add_le _ _) le_rfl
    _=_ := by rw [abs_of_nonneg ha,abs_mul,abs_of_nonneg hb,abs_of_nonneg hw]

/-- Default corrections in the insertion recurrence cost at most the old and new bad-
event probabilities, for the two finite-array probability measures.
-/
theorem recurrenceResidual_le_cylinders_add_bad {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (x : Fin K→ℝ) (hn : 0<n)
    (mu : Measure (Fin n→UnitSpin N)) [IsProbabilityMeasure mu]
    (muNext : Measure (Fin (n+1)→UnitSpin N)) [IsProbabilityMeasure muNext] :
    recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x)
      (treePMF cuts hcuts mu) (treePMF cuts hcuts muNext)≤
      (∑t : NestedPartition depth n,∑o : Insertion depth n t,
        |muNext.real {s | treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) s}-
          mu.real {old | treeCylinder cuts t old}*
            (numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/(n : ℝ))|)+
        mu.real {old | ¬thresholdGood cuts old}+muNext.real {s | ¬thresholdGood cuts s} := by
  classical
  let w : (t : NestedPartition depth n)→Insertion depth n t→ℝ := fun t o ↦
    numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/(n : ℝ)
  let dOld : NestedPartition depth n→ℝ := fun t ↦
    (treePMF cuts hcuts mu t).toReal-mu.real {old | treeCylinder cuts t old}
  let dNew : NestedPartition depth (n+1)→ℝ := fun t ↦
    (treePMF cuts hcuts muNext t).toReal-muNext.real {s | treeCylinder cuts t s}
  have hw (t) (o) : 0≤w t o := (own_root_numerator_mem_Icc nu hv cuts hcuts x hn t o).1
  have hwSum (t) : (∑o : Insertion depth n t,w t o)=1 := own_root_numerator_sum nu v cuts x hn t
  have hOld (t) : 0≤dOld t := treePMF_real_atom_sub_nonneg cuts hcuts mu t
  have hNew (t) : 0≤dNew t := treePMF_real_atom_sub_nonneg cuts hcuts muNext t
  have hOldSum : (∑t : NestedPartition depth n,dOld t)=mu.real {old | ¬thresholdGood cuts old} := by
    have H := treePMF_cylinder_l1_eq_bad_mass cuts hcuts mu
    change (∑t : NestedPartition depth n,|dOld t|)=_ at H
    simpa only [abs_of_nonneg (hOld _)] using H
  have hNewSum : (∑t : NestedPartition depth (n+1),dNew t)=muNext.real {s | ¬thresholdGood cuts s} := by
    have H := treePMF_cylinder_l1_eq_bad_mass cuts hcuts muNext
    change (∑t : NestedPartition depth (n+1),|dNew t|)=_ at H
    simpa only [abs_of_nonneg (hNew _)] using H
  have hOldRows : (∑t : NestedPartition depth n,∑o : Insertion depth n t,dOld t*w t o)=
      mu.real {old | ¬thresholdGood cuts old} := by
    simp_rw [← Finset.mul_sum,hwSum,mul_one]
    exact hOldSum
  have hNewRows : (∑t : NestedPartition depth n,∑o : Insertion depth n t,dNew ((extendEquiv depth n) ⟨t,o⟩))=
      muNext.real {s | ¬thresholdGood cuts s} := by
    calc
      _=(∑s : (Σt : NestedPartition depth n,Insertion depth n t),dNew ((extendEquiv depth n) s)) :=
        (Fintype.sum_sigma (f := fun s : (Σt : NestedPartition depth n,Insertion depth n t) ↦ dNew ((extendEquiv depth n) s))).symm
      _=(∑t : NestedPartition depth (n+1),dNew t) :=
        Fintype.sum_equiv (extendEquiv depth n) (fun s ↦ dNew ((extendEquiv depth n) s)) dNew (fun _ ↦ rfl)
      _=_ := hNewSum
  unfold recurrenceResidual
  calc
    _≤∑t : NestedPartition depth n,∑o : Insertion depth n t,
        (|muNext.real {s | treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) s}-
          mu.real {old | treeCylinder cuts t old}*w t o|+
          dNew ((extendEquiv depth n) ⟨t,o⟩)+dOld t*w t o) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro o _
      exact scalar_recurrence_error _ _ _ _ _ (hNew _) (hOld _) (hw t o)
    _=_ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hNewRows,hOldRows]
      ring

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeExtractionError
