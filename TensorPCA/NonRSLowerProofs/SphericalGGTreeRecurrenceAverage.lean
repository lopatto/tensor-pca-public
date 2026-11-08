-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrence

/-! Finite-cell full-PMF recurrence means, with every bad-array mass retained and no
normalization of the good cylinders.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrenceAverage
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeHeights SphericalGGJetFamily
open SphericalGGTreeExtractionError SphericalGGTreeInsertionResidual SphericalGGTreeInsertionUniform
open SphericalGGTreeRecurrence SphericalGGThresholdFirstMomentAverage
open FiniteNestedPartition FiniteNestedInsertionNumerators FiniteNestedLawComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem badMass_integrable {N K depth m : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) :
    Integrable (fun x : Fin K→ℝ ↦
      (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) m).real {s | ¬thresholdGood cuts s}) (positiveCubeLaw K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let Z : (Fin m→UnitSpin N)→ℝ := {s | ¬thresholdGood cuts s}.indicator (fun _ ↦ 1)
  have hBad : MeasurableSet {s : Fin m→UnitSpin N | ¬thresholdGood cuts s} :=
    (thresholdGood_measurable cuts hcuts).compl
  have hZm : Measurable Z := measurable_const.indicator hBad
  have hZb (s) : |Z s|≤1 := by by_cases h : thresholdGood cuts s <;> simp [Z,h]
  have hM := parameterized_law_integral_measurable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) (parameterizedGibbsKernel nu v)
    m (fun _ s ↦ Z s) (hZm.comp measurable_snd) (fun _ s ↦ hZb s)
  have hMeas : Measurable (fun x : Fin K→ℝ ↦
      (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) m).real {s | ¬thresholdGood cuts s}) := by
    simpa only [Z,integral_indicator_const (1 : ℝ) hBad,smul_eq_mul,mul_one] using hM
  apply Integrable.of_bound hMeas.aestronglyMeasurable 1
  refine .of_forall (fun x ↦ ?_)
  rw [Real.norm_of_nonneg measureReal_nonneg]
  simpa only [probReal_univ] using measureReal_mono (subset_univ {s : Fin m→UnitSpin N | ¬thresholdGood cuts s})
    (measure_ne_top (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) m) _)


/-- Entry bounds are explicit numerical intermediate estimates for the cylinder
residuals; the full-PMF default corrections each occur once.
-/
theorem masked_recurrence_mean_le_of_entry_bounds {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (hn : 0<n)
    (E : Set (Fin K→ℝ)) (hE : MeasurableSet E) (delta : ℝ)
    (hEntry : ∀ (t : NestedPartition depth n) (o : Insertion depth n t),
      (∫x,E.indicator (fun x ↦ |cylinderInsertionResidual nu v cuts t o x|) x ∂positiveCubeLaw K)≤delta) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := fun x : Fin K→ℝ ↦ (parameterizedGibbsKernel nu v).sectR x
    (∫x,E.indicator (fun x ↦ recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x)
      (treePMF cuts hcuts (law d (G x) n)) (treePMF cuts hcuts (law d (G x) (n+1)))) x ∂positiveCubeLaw K)≤
      (Fintype.card (Σt : NestedPartition depth n,Insertion depth n t) : ℝ)*delta+
      (∫x,E.indicator (fun x ↦ (law d (G x) n).real {old | ¬thresholdGood cuts old}) x ∂positiveCubeLaw K)+
      (∫x,E.indicator (fun x ↦ (law d (G x) (n+1)).real {s | ¬thresholdGood cuts s}) x ∂positiveCubeLaw K) := by
  classical
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  dsimp only
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := fun x : Fin K→ℝ ↦ (parameterizedGibbsKernel nu v).sectR x
  let R : (Fin K→ℝ)→ℝ := fun x ↦ recurrenceResidual depth n (fun l ↦ lowerHeight nu v (cuts l) x)
    (treePMF cuts hcuts (law d (G x) n)) (treePMF cuts hcuts (law d (G x) (n+1)))
  let C : (t : NestedPartition depth n)→Insertion depth n t→(Fin K→ℝ)→ℝ :=
    fun t o x ↦ |cylinderInsertionResidual nu v cuts t o x|
  let B : ℕ→(Fin K→ℝ)→ℝ := fun m x ↦ (law d (G x) m).real {old | ¬thresholdGood cuts old}
  have hRI : Integrable (E.indicator R) (positiveCubeLaw K) :=
    (actual_recurrence_integrable nu hv cuts hcuts hn).indicator hE
  have hCI (t) (o) : Integrable (E.indicator (C t o)) (positiveCubeLaw K) :=
    ((cylinderInsertionResidual_integrable nu hv cuts hcuts t o hn).abs).indicator hE
  have hSumI : Integrable (fun x ↦ ∑t : NestedPartition depth n,∑o : Insertion depth n t,E.indicator (C t o) x)
      (positiveCubeLaw K) := integrable_finsetSum Finset.univ (fun t _ ↦
        integrable_finsetSum Finset.univ (fun o _ ↦ hCI t o))
  have hOldI : Integrable (E.indicator (B n)) (positiveCubeLaw K) := (badMass_integrable nu hv cuts hcuts).indicator hE
  have hNewI : Integrable (E.indicator (B (n+1))) (positiveCubeLaw K) := (badMass_integrable nu hv cuts hcuts).indicator hE
  have hPoint (x : Fin K→ℝ) : E.indicator R x≤
      (∑t : NestedPartition depth n,∑o : Insertion depth n t,E.indicator (C t o) x)+
        E.indicator (B n) x+E.indicator (B (n+1)) x := by
    by_cases h : x∈E
    · simp only [indicator_of_mem h]
      exact recurrenceResidual_le_cylinders_add_bad nu hv cuts hcuts x hn (law d (G x) n) (law d (G x) (n+1))
    · simp [h]
  have hSumOld : Integrable (fun x ↦
      (∑t : NestedPartition depth n,∑o : Insertion depth n t,E.indicator (C t o) x)+E.indicator (B n) x) (positiveCubeLaw K) := hSumI.add hOldI
  have H := integral_mono hRI (hSumOld.add hNewI) hPoint
  simp only [Pi.add_apply] at H
  rw [integral_add hSumOld hNewI,integral_add hSumI hOldI,
    integral_finsetSum Finset.univ (fun t _ ↦ integrable_finsetSum Finset.univ (fun o _ ↦ hCI t o))] at H
  simp_rw [integral_finsetSum Finset.univ (fun o _ ↦ hCI _ o)] at H
  have hTotal : (∑t : NestedPartition depth n,∑o : Insertion depth n t,
      ∫x,E.indicator (C t o) x ∂positiveCubeLaw K)≤
      (Fintype.card (Σt : NestedPartition depth n,Insertion depth n t) : ℝ)*delta := by
    calc
      _≤∑t : NestedPartition depth n,∑o : Insertion depth n t,delta :=
        Finset.sum_le_sum (fun t _ ↦ Finset.sum_le_sum (fun o _ ↦ hEntry t o))
      _=(∑s : (Σt : NestedPartition depth n,Insertion depth n t),delta) :=
        (Fintype.sum_sigma (f := fun _ : (Σt : NestedPartition depth n,Insertion depth n t) ↦ delta)).symm
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (∫x,E.indicator R x ∂positiveCubeLaw K)≤_+ (∫x,E.indicator (B n) x ∂positiveCubeLaw K)+
    (∫x,E.indicator (B (n+1)) x ∂positiveCubeLaw K)
  linarith only [H,hTotal]


/-- Finite-cell recurrence estimate. Family cardinality enters the numerical GG budget
chosen after the finite family; masked score errors measured under each amplitude's
pair law have no factor for the number of cut vectors.
-/
theorem exists_uniform_finite_cell_recurrence_threshold {A : Type*} [Fintype A]
    (depth n : ℕ) (P : A→Fin depth→Polynomial ℝ) {eps : ℝ} (heps : 0<eps) :
    let M : ℝ := Fintype.card (Σt : NestedPartition depth (n+1),Insertion depth (n+1) t)
    ∃ V : ℝ,∃ hV : 1≤V,∀ {N K : ℕ} (hPK : ∀a l,(P a l).natDegree≤K)
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : V≤v),
      letI := parameterizedGibbsKernel_markov (K := K) nu ((by norm_num : (0 : ℝ)≤1).trans (hV.trans hv))
      ∀ (cuts : A→Fin depth→ℝ) (hcuts : ∀a,Monotone (cuts a)) (hcuts1 : ∀a l,cuts a l≤1)
        (E : A→Set (Fin K→ℝ)),(∀a,MeasurableSet (E a)) →
        (∀a l r,|extendTest ((P a l).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) →
        let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
        let G := fun x : Fin K→ℝ ↦ (parameterizedGibbsKernel nu v).sectR x
        (∑a : A,∫x,(E a).indicator (fun x ↦ recurrenceResidual depth (n+1)
          (fun l ↦ lowerHeight nu v (cuts a l) x)
          (treePMF (cuts a) (hcuts a) (law d (G x) (n+1)))
          (treePMF (cuts a) (hcuts a) (law d (G x) (n+2)))) x ∂positiveCubeLaw K)≤
          eps+2*M*((n : ℝ)+2)*(∑a : A,∑l : Fin depth,∫x,(E a).indicator (fun x ↦ pairMean nu v (fun r ↦
            |(Ici (cuts a l)).indicator (fun _ ↦ (1 : ℝ)) r-
              extendTest ((P a l).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K)+
          (M*((n : ℝ)+3)+1)*(∑a : A,∫x,(E a).indicator (fun x ↦ (law d (G x) (n+2)).real
            {s | ¬thresholdGood (cuts a) s}) x ∂positiveCubeLaw K)+
          (∑a : A,∫x,(E a).indicator (fun x ↦ (law d (G x) (n+1)).real
            {old | ¬thresholdGood (cuts a) old}) x ∂positiveCubeLaw K) := by
  classical
  dsimp only
  let M : ℝ := Fintype.card (Σt : NestedPartition depth (n+1),Insertion depth (n+1) t)
  have hM : 0≤M := Nat.cast_nonneg _
  let small : ℝ := eps/(M*(Fintype.card A : ℝ)+1)
  have hSmall : 0<small := div_pos heps (by positivity)
  choose VL hVL hRows using (fun a : A ↦ exists_uniform_masked_insertion_threshold depth n (P a) hSmall)
  let V : ℝ := 1+∑a : A,max 0 (VL a)
  have hV : 1≤V := by
    have hSum : 0≤∑a : A,max 0 (VL a) := Finset.sum_nonneg (fun a _ ↦ le_max_left 0 (VL a))
    dsimp only [V]
    linarith only [hSum]
  have hDom (a : A) : VL a≤V := by
    have H := (le_max_right 0 (VL a)).trans
      (Finset.single_le_sum (fun b _ ↦ le_max_left 0 (VL b)) (Finset.mem_univ a))
    dsimp only [V]
    linarith only [H]
  refine ⟨V,hV,?_⟩
  intro N K hPK nu hnu v hv cuts hcuts hcuts1 E hE hGlobal
  have hvp : 0<v := lt_of_lt_of_le zero_lt_one (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hvp.le
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := fun x : Fin K→ℝ ↦ (parameterizedGibbsKernel nu v).sectR x
  let B : ℕ→A→ℝ := fun m a ↦ ∫x,(E a).indicator (fun x ↦
    (law d (G x) m).real {s | ¬thresholdGood (cuts a) s}) x ∂positiveCubeLaw K
  let L : A→ℝ := fun a ↦ ∑l : Fin depth,∫x,(E a).indicator (fun x ↦ pairMean nu v (fun r ↦
    |(Ici (cuts a l)).indicator (fun _ ↦ (1 : ℝ)) r-
      extendTest ((P a l).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K
  let R : A→(Fin K→ℝ)→ℝ := fun a x ↦ recurrenceResidual depth (n+1)
    (fun l ↦ lowerHeight nu v (cuts a l) x)
    (treePMF (cuts a) (hcuts a) (law d (G x) (n+1)))
    (treePMF (cuts a) (hcuts a) (law d (G x) (n+2)))
  have hOne (a : A) : (∫x,(E a).indicator (R a) x ∂positiveCubeLaw K)≤
      M*(small+2*((n : ℝ)+2)*L a+((n : ℝ)+3)*B (n+2) a)+B (n+1) a+B (n+2) a := by
    apply masked_recurrence_mean_le_of_entry_bounds nu hvp.le (cuts a) (hcuts a) (Nat.succ_pos n) (E a) (hE a)
    intro t o
    exact hRows a (hPK a) nu v ((hDom a).trans hv) (cuts a) (hcuts a) (hcuts1 a) t o (E a) (hE a) (hGlobal a)
  have H := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hOne a)
  have hSumEq : (∑a : A,(M*(small+2*((n : ℝ)+2)*L a+((n : ℝ)+3)*B (n+2) a)+B (n+1) a+B (n+2) a))=
      M*(Fintype.card A : ℝ)*small+2*M*((n : ℝ)+2)*(∑a : A,L a)+
        (M*((n : ℝ)+3)+1)*(∑a : A,B (n+2) a)+(∑a : A,B (n+1) a) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simp_rw [← mul_assoc,← Finset.mul_sum]
    ring
  rw [hSumEq] at H
  have hNumeric : M*(Fintype.card A : ℝ)*small≤eps := by
    have hCount : 0≤M*(Fintype.card A : ℝ) := mul_nonneg hM (Nat.cast_nonneg _)
    have hEq : small*(M*(Fintype.card A : ℝ)+1)=eps := div_mul_cancel₀ eps (by positivity : M*(Fintype.card A : ℝ)+1≠0)
    nlinarith only [hSmall.le,hEq]
  change (∑a : A,∫x,(E a).indicator (R a) x ∂positiveCubeLaw K)≤eps+2*M*((n : ℝ)+2)*(∑a : A,L a)+
    (M*((n : ℝ)+3)+1)*(∑a : A,B (n+2) a)+(∑a : A,B (n+1) a)
  linarith only [H,hNumeric]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrenceAverage
