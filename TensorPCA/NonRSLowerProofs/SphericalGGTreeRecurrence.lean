-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeExtractionError
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionUniform

/-! Recurrence means for full tree PMFs. The default tree retains every bad-array mass;
good-array cylinders are not renormalized.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrence
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeHeights SphericalGGJetFamily
open SphericalGGTreeExtractionError SphericalGGTreeInsertionResidual SphericalGGTreeInsertionUniform
open SphericalGGThresholdFirstMomentAverage SphericalGGWeightObservable
open FiniteNestedPartition FiniteNestedInsertionNumerators FiniteNestedLawComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem actual_set_mass_measurable_bound {N K m : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    {S : Set (Fin m→UnitSpin N)} (hS : MeasurableSet S) :
    Measurable (fun x : Fin K→ℝ ↦ (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) m).real S) ∧
    ∀x : Fin K→ℝ,(law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) m).real S∈Icc (0 : ℝ) 1 := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hIm : Measurable (S.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hS
  have hIb (s : Fin m→UnitSpin N) : |S.indicator (fun _ ↦ (1 : ℝ)) s|≤1 := by by_cases h : s∈S <;> simp [h]
  have H := parameterized_law_integral_measurable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) (parameterizedGibbsKernel nu v)
    m (fun _ s ↦ S.indicator (fun _ ↦ (1 : ℝ)) s) (hIm.comp measurable_snd) (fun _ s ↦ hIb s)
  refine ⟨?_,?_⟩
  · simpa only [integral_indicator_const (1 : ℝ) hS,smul_eq_mul,mul_one] using H
  · intro x
    refine ⟨measureReal_nonneg,?_⟩
    simpa only [probReal_univ] using measureReal_mono (subset_univ S)
      (measure_ne_top (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) m) _)

private theorem numerator_parameter_measurable {A : Type*} [MeasurableSpace A]
    (depth n : ℕ) (y : A→Fin depth→ℝ) (p : A→ℝ)
    (hy : ∀l,Measurable (fun x ↦ y x l)) (hp : Measurable p)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    Measurable (fun x ↦ numerator depth n (y x) (p x) t o) := by
  induction depth generalizing n p with
  | zero => exact measurable_const.sub hp
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none => exact ((hy 0).const_mul (c.length : ℝ)).sub hp
    | some a =>
      obtain ⟨i,o⟩ := a
      exact ih (c.partSize i) (fun x l ↦ y x l.succ) (fun x ↦ y x 0)
        (fun l ↦ hy l.succ) (hy 0) (f i) o

private theorem pmf_real_sum {A : Type*} [Fintype A] (P : PMF A) : (∑a : A,(P a).toReal)=1 := by
  rw [← ENNReal.toReal_sum (fun a _ ↦ P.apply_ne_top a)]
  have H : (∑a : A,P a)=1 := by simpa only [tsum_fintype] using P.tsum_coe
  rw [H,ENNReal.toReal_one]

theorem actual_treePMF_atom_measurable {N K depth m : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (t : NestedPartition depth m) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    Measurable (fun x : Fin K→ℝ ↦
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) m) t).toReal) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have H := (actual_set_mass_measurable_bound (K := K) nu hv (extractTree_fiber_measurable cuts hcuts t)).1
  simpa only [treePMF_apply,Measure.real] using H

theorem actual_recurrence_abs_le_two {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (x : Fin K→ℝ) (hn : 0<n) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    |recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x)
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n))
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1)))|≤2 := by
  classical
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let P := treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((parameterizedGibbsKernel nu v).sectR x) n)
  let Q := treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((parameterizedGibbsKernel nu v).sectR x) (n+1))
  let w : (t : NestedPartition depth n)→Insertion depth n t→ℝ := fun t o ↦
    numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/(n : ℝ)
  have hw (t) (o) : 0≤w t o := (own_root_numerator_mem_Icc nu hv cuts hcuts x hn t o).1
  have hwSum (t) : (∑o : Insertion depth n t,w t o)=1 := own_root_numerator_sum nu v cuts x hn t
  have hNew : (∑t : NestedPartition depth n,∑o : Insertion depth n t,(Q ((extendEquiv depth n) ⟨t,o⟩)).toReal)=1 := by
    calc
      _=(∑s : (Σt : NestedPartition depth n,Insertion depth n t),(Q ((extendEquiv depth n) s)).toReal) :=
        (Fintype.sum_sigma (f := fun s : (Σt : NestedPartition depth n,Insertion depth n t) ↦ (Q ((extendEquiv depth n) s)).toReal)).symm
      _=(∑u : NestedPartition depth (n+1),(Q u).toReal) :=
        Fintype.sum_equiv (extendEquiv depth n) _ _ (fun _ ↦ rfl)
      _=1 := pmf_real_sum Q
  have hOld : (∑t : NestedPartition depth n,∑o : Insertion depth n t,(P t).toReal*w t o)=1 := by
    simp_rw [← Finset.mul_sum,hwSum,mul_one]
    exact pmf_real_sum P
  have hNon : 0≤recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x) P Q :=
    Finset.sum_nonneg (fun t _ ↦ Finset.sum_nonneg (fun o _ ↦ abs_nonneg _))
  rw [abs_of_nonneg hNon]
  unfold recurrenceResidual
  calc
    _≤∑t : NestedPartition depth n,∑o : Insertion depth n t,
        ((Q ((extendEquiv depth n) ⟨t,o⟩)).toReal+(P t).toReal*w t o) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro o _
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg ENNReal.toReal_nonneg,abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hw t o))])
    _=2 := by simp_rw [Finset.sum_add_distrib]; rw [hNew,hOld]; norm_num

theorem actual_recurrence_integrable {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (hn : 0<n) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    Integrable (fun x : Fin K→ℝ ↦ recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x)
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n))
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1)))) (positiveCubeLaw K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hM : Measurable (fun x : Fin K→ℝ ↦ recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x)
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n))
      (treePMF cuts hcuts (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1)))) := by
    apply Finset.measurable_sum
    intro t _
    apply Finset.measurable_sum
    intro o _
    apply (continuous_abs.measurable : Measurable (abs : ℝ→ℝ)).comp
    exact (actual_treePMF_atom_measurable nu hv cuts hcuts ((extendEquiv depth n) ⟨t,o⟩)).sub
      ((actual_treePMF_atom_measurable nu hv cuts hcuts t).mul
        ((numerator_parameter_measurable depth n (fun x l ↦ lowerHeight nu v (cuts l) x)
          (fun _ ↦ 0) (fun l ↦ lowerHeight_measurable nu hv (cuts l)) measurable_const t o).div_const _))
  exact Integrable.of_bound hM.aestronglyMeasurable 2
    (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using actual_recurrence_abs_le_two nu hv cuts hcuts x hn))


/-- Exact selected bad-array Fubini identity. Disjoint amplitude cells keep
one bad event under the true full joint law, not a sum over alternatives. -/
theorem selected_bad_mass_eq_joint {A : Type*} [Fintype A] {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : A→Fin depth→ℝ) (hcuts : ∀a,Monotone (cuts a))
    (S : A→Set (Fin K→ℝ)) (hS : ∀a,MeasurableSet (S a))
    (hDisj : ∀a b,a≠b→Disjoint (S a) (S b)) :
    (∑a : A,∫x,(S a).indicator (fun x ↦
      (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1)).real {old | ¬thresholdGood (cuts a) old}) x ∂positiveCubeLaw K)=
      (jointLaw (K := K) nu v n).real {q | ∃a : A,q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2} := by
  classical
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  letI := jointLaw_probability (K := K) nu hv n
  let Q := ((Fin K→ℝ)×PerturbationDisorder N K)×(Fin (n+1)→UnitSpin N)
  let Phi : (Fin K→ℝ)→(Fin (n+1)→UnitSpin N)→ℝ := fun x old ↦
    ∑a : A,if x∈S a ∧ ¬thresholdGood (cuts a) old then 1 else 0
  have hBad (a : A) : MeasurableSet {old : Fin (n+1)→UnitSpin N | ¬thresholdGood (cuts a) old} :=
    (thresholdGood_measurable (cuts a) (hcuts a)).compl
  have hTerm (a : A) : Measurable (fun p : (Fin K→ℝ)×(Fin (n+1)→UnitSpin N) ↦
      if p.1∈S a ∧ ¬thresholdGood (cuts a) p.2 then (1 : ℝ) else 0) :=
    Measurable.ite ((hS a).preimage measurable_fst |>.inter ((hBad a).preimage measurable_snd)) measurable_const measurable_const
  have hPhi : Measurable (fun p : (Fin K→ℝ)×(Fin (n+1)→UnitSpin N) ↦ Phi p.1 p.2) :=
    Finset.measurable_sum _ (fun a _ ↦ hTerm a)
  have hPhiEq (x : Fin K→ℝ) (old : Fin (n+1)→UnitSpin N) :
      Phi x old=if ∃a : A,x∈S a ∧ ¬thresholdGood (cuts a) old then (1 : ℝ) else 0 := by
    by_cases H : ∃a : A,x∈S a ∧ ¬thresholdGood (cuts a) old
    · obtain ⟨a,ha,hbad⟩ := H
      have hExist : ∃a : A,x∈S a ∧ ¬thresholdGood (cuts a) old := ⟨a,ha,hbad⟩
      rw [if_pos hExist]
      unfold Phi
      rw [Finset.sum_eq_single a]
      · exact if_pos ⟨ha,hbad⟩
      · intro b _ hba
        exact if_neg (fun hb ↦ (Set.disjoint_left.mp (hDisj b a hba)) hb.1 ha)
      · simp
    · rw [if_neg H]
      exact Finset.sum_eq_zero (fun a _ ↦ if_neg (fun ha ↦ H ⟨a,ha⟩))
  have hPb (x old) : |Phi x old|≤1 := by rw [hPhiEq]; split_ifs <;> norm_num
  have hCI (a : A) : Integrable ((S a).indicator (fun x : Fin K→ℝ ↦
      (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1)).real {old | ¬thresholdGood (cuts a) old})) (positiveCubeLaw K) := by
    have H := actual_set_mass_measurable_bound (K := K) nu hv (hBad a)
    apply Integrable.of_bound (H.1.indicator (hS a)).aestronglyMeasurable 1
    refine .of_forall (fun x ↦ ?_)
    by_cases hx : x∈S a
    · rw [indicator_of_mem hx,Real.norm_of_nonneg (H.2 x).1]
      exact (H.2 x).2
    · simp only [indicator_of_notMem hx,norm_zero,zero_le_one]
  have hInner (x : Fin K→ℝ) :
      (∫old,Phi x old ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1))=
      ∑a : A,(S a).indicator (fun x ↦
        (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+1)).real {old | ¬thresholdGood (cuts a) old}) x := by
    have hi (a : A) : Integrable (fun old : Fin (n+1)→UnitSpin N ↦
        if x∈S a ∧ ¬thresholdGood (cuts a) old then (1 : ℝ) else 0)
        (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+1)) := by
      apply Integrable.of_bound ((hTerm a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      exact .of_forall (fun old ↦ by
        change ‖if x∈S a ∧ ¬thresholdGood (cuts a) old then (1 : ℝ) else 0‖≤1
        split_ifs <;> norm_num)
    rw [integral_finsetSum Finset.univ (fun a _ ↦ hi a)]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hx : x∈S a
    · simp only [hx,true_and,indicator_of_mem hx]
      simpa only [Set.indicator_apply,mem_setOf_eq,smul_eq_mul,mul_one] using
        (integral_indicator_const (μ := law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+1)) (1 : ℝ) (hBad a))
    · simp only [hx,false_and,if_false,integral_zero,indicator_of_notMem hx]
  let event : Set Q := {q | ∃a : A,q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2}
  have hEvent : MeasurableSet event := by
    have H : event=⋃a : A,{q : Q | q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2} := by
      ext q
      simp only [event,mem_setOf_eq,mem_iUnion]
    rw [H]
    exact MeasurableSet.iUnion (fun a ↦ ((hS a).preimage measurable_fst.fst).inter ((hBad a).preimage measurable_snd))
  calc
    _=(∫x,(∑a : A,(S a).indicator (fun x ↦
        (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+1)).real {old | ¬thresholdGood (cuts a) old}) x) ∂positiveCubeLaw K) :=
      (integral_finsetSum Finset.univ (fun a _ ↦ hCI a)).symm
    _=(∫x,∫old,Phi x old ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+1) ∂positiveCubeLaw K) :=
      integral_congr_ae (.of_forall (fun x ↦ (hInner x).symm))
    _=(∫q,Phi q.1.1 q.2 ∂jointLaw nu v n) := (joint_old_integral_eq_cube nu hv n Phi hPhi hPb).symm
    _=(∫q,event.indicator (fun _ ↦ (1 : ℝ)) q ∂jointLaw nu v n) := by
      apply integral_congr_ae
      exact .of_forall (fun q ↦ by simpa only [event,Set.indicator_apply,mem_setOf_eq] using hPhiEq q.1.1 q.2)
    _=_ := by rw [integral_indicator_const (1 : ℝ) hEvent,smul_eq_mul,mul_one]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrence
