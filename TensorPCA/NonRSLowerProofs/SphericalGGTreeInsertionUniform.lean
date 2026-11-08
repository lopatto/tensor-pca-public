-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionGG
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeBallUniform

/-! Uniform masked insertion bounds for every finite Tree choice. Polynomial budgets are
selected before the physical model; the estimate retains the L1 score error under
the amplitude's pair law and the probability of bad threshold arrays.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionUniform
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGJetFamily
open SphericalGGTreeBallAverage SphericalGGTreeBallUniform SphericalGGTreeInsertionResidual
open SphericalGGTreeInsertionGG SphericalGGTreeInsertionBalls SphericalGGThresholdFirstMomentAverage
open FiniteNestedPartition
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
  have hBad : MeasurableSet {s : Fin m→UnitSpin N | ¬thresholdGood cuts s} := (thresholdGood_measurable cuts hcuts).compl
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

private theorem list_integral_le {A B : Type*} [MeasurableSpace A] (mu : Measure A)
    (xs : List B) (f : B→A→ℝ) (hi : ∀b,Integrable (f b) mu) {C : ℝ}
    (hMean : ∀b,(∫x,f b x ∂mu)≤C) :
    Integrable (fun x ↦ (xs.map (fun b ↦ f b x)).sum) mu ∧
      (∫x,(xs.map (fun b ↦ f b x)).sum ∂mu)≤(xs.length : ℝ)*C := by
  induction xs with
  | nil => exact ⟨by simpa using (integrable_zero A ℝ mu),by simp⟩
  | cons b xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    refine ⟨(hi b).add ih.1,?_⟩
    rw [integral_add (hi b) ih.1]
    exact (add_le_add (hMean b) ih.2).trans_eq (by ring)

/-- Lower-tail heights under the amplitude pair law remain the recurrence coefficients.
The threshold is uniform over dimension, prior, mask and insertion.
-/
theorem exists_uniform_masked_insertion_threshold (depth n : ℕ)
    (P : Fin depth→Polynomial ℝ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ,1≤V ∧ ∀ {N K : ℕ} (hPK : ∀l,(P l).natDegree≤K)
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
      ∀ (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
        (t : NestedPartition depth (n+1)) (o : Insertion depth (n+1) t)
        (E : Set (Fin K→ℝ)),MeasurableSet E →
        (∀ l r,|extendTest ((P l).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) →
        (∫x,E.indicator (fun x ↦ |cylinderInsertionResidual nu v cuts t o x|) x ∂positiveCubeLaw K)≤
          eps+2*((n : ℝ)+2)*(∑l : Fin depth,∫x,E.indicator (fun x ↦ pairMean nu v (fun r ↦
            |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
              extendTest ((P l).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K)+
          ((n : ℝ)+3)*(∫x,E.indicator (fun x ↦
            (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
              ((parameterizedGibbsKernel nu v).sectR x) (n+2)).real {s | ¬thresholdGood cuts s}) x ∂positiveCubeLaw K) := by
  classical
  have hSmallPos : 0<eps/((n : ℝ)+2) := div_pos heps (by positivity)
  choose VL hVL hRows using (fun l : Fin depth ↦ exists_uniform_masked_freshBallResidual_threshold (P l) hSmallPos)
  let V : ℝ := 1+∑l : Fin depth,max 0 (VL l)
  have hV : 1≤V := by
    have hSum : 0≤∑l : Fin depth,max 0 (VL l) := Finset.sum_nonneg (fun l _ ↦ le_max_left 0 (VL l))
    dsimp only [V]
    linarith only [hSum]
  have hDom (l : Fin depth) : VL l≤V := by
    have H := (le_max_right 0 (VL l)).trans
      (Finset.single_le_sum (fun j _ ↦ le_max_left 0 (VL j)) (Finset.mem_univ l))
    dsimp only [V]
    linarith only [H]
  refine ⟨V,hV,?_⟩
  intro N K hPK nu hnu v hv cuts hcuts hcuts1 t o E hE hGlobal
  have hvp : 0<v := lt_of_lt_of_le zero_lt_one (hV.trans hv)
  let balls := insertionBalls depth (n+1) t o
  let R : (Fin depth×Fin (n+1))→(Fin K→ℝ)→ℝ := fun b x ↦ |freshBallResidual nu v cuts t b.1 b.2 x|
  let B : (Fin K→ℝ)→ℝ := fun x ↦
    (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) (n+2)).real {s | ¬thresholdGood cuts s}
  let L : Fin depth→ℝ := fun l ↦ ∫x,E.indicator (fun x ↦ pairMean nu v (fun r ↦
    |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
      extendTest ((P l).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K
  let C : ℝ := eps/((n : ℝ)+2)+2*∑l : Fin depth,L l
  have hL (l : Fin depth) : 0≤L l := by
    apply integral_nonneg
    intro x
    apply indicator_nonneg
    intro _ _
    exact integral_nonneg (fun r ↦ abs_nonneg _)
  have hLsum : 0≤∑l : Fin depth,L l := Finset.sum_nonneg (fun l _ ↦ hL l)
  have hC : 0≤C := add_nonneg hSmallPos.le (mul_nonneg (by norm_num) hLsum)
  have hBI : Integrable B (positiveCubeLaw K) := badMass_integrable nu hvp.le cuts hcuts
  have hRI (b : Fin depth×Fin (n+1)) : Integrable (E.indicator (R b)) (positiveCubeLaw K) :=
    ((freshBallResidual_integrable nu hvp.le cuts t b.1 b.2).abs).indicator hE
  have hEach (b : Fin depth×Fin (n+1)) : (∫x,E.indicator (R b) x ∂positiveCubeLaw K)≤C := by
    have H := hRows b.1 (hPK b.1) nu v ((hDom b.1).trans hv) cuts t b.1 b.2 E hE (hGlobal b.1)
    have hOne : L b.1≤∑l : Fin depth,L l := Finset.single_le_sum (fun l _ ↦ hL l) (Finset.mem_univ _)
    exact H.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hOne (by norm_num)))
  have hParentI : Integrable (fun x ↦ balls.1.elim 0 (fun b ↦ E.indicator (R b) x)) (positiveCubeLaw K) := by
    cases hp : balls.1
    · exact integrable_zero _ _ _
    · exact hRI _
  have hParent : (∫x,balls.1.elim 0 (fun b ↦ E.indicator (R b) x) ∂positiveCubeLaw K)≤C := by
    cases hp : balls.1
    · simpa using hC
    · exact hEach _
  have hList := list_integral_le (positiveCubeLaw K) balls.2 (fun b ↦ E.indicator (R b)) hRI hEach
  have hResI := ((cylinderInsertionResidual_integrable nu hvp.le cuts hcuts t o (Nat.succ_pos n)).abs).indicator hE
  have hPoint (x : Fin K→ℝ) :
      E.indicator (fun x ↦ |cylinderInsertionResidual nu v cuts t o x|) x≤
        balls.1.elim 0 (fun b ↦ E.indicator (R b) x)+
        (balls.2.map (fun b ↦ E.indicator (R b) x)).sum+((n : ℝ)+3)*E.indicator B x := by
    by_cases h : x∈E
    · simpa only [Set.indicator_of_mem h] using cylinderInsertionResidual_le_ball_errors nu hvp.le x cuts hcuts hcuts1 t o
    · cases hp : balls.1 <;> simp [h,hp]
  have hSumI : Integrable (fun x ↦ balls.1.elim 0 (fun b ↦ E.indicator (R b) x)+
      (balls.2.map (fun b ↦ E.indicator (R b) x)).sum) (positiveCubeLaw K) := hParentI.add hList.1
  have H := integral_mono hResI (hSumI.add ((hBI.indicator hE).const_mul ((n : ℝ)+3))) hPoint
  simp only [Pi.add_apply] at hSumI H
  rw [integral_add hSumI ((hBI.indicator hE).const_mul ((n : ℝ)+3)),
    integral_add hParentI hList.1,integral_const_mul] at H
  have hLen : (balls.2.length : ℝ)≤(n : ℝ)+1 := by
    exact_mod_cast insertionBalls_negatives_length_le depth (n+1) t o
  have hTotal : (∫x,balls.1.elim 0 (fun b ↦ E.indicator (R b) x) ∂positiveCubeLaw K)+
      (∫x,(balls.2.map (fun b ↦ E.indicator (R b) x)).sum ∂positiveCubeLaw K)≤((n : ℝ)+2)*C := by
    have H0 := add_le_add hParent hList.2
    have H1 := mul_le_mul_of_nonneg_right hLen hC
    nlinarith only [H0,H1]
  have hBudget : ((n : ℝ)+2)*(eps/((n : ℝ)+2))=eps := mul_div_cancel₀ eps (by positivity : (n : ℝ)+2≠0)
  change _≤eps+2*((n : ℝ)+2)*(∑l : Fin depth,L l)+((n : ℝ)+3)*(∫x,E.indicator B x ∂positiveCubeLaw K)
  dsimp only [C] at hTotal
  nlinarith only [H,hTotal,hBudget]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionUniform
