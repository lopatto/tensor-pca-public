-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeExtraction
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Full extractor PMFs retain the entire bad-array mass. Disjoint amplitude cells are
summed before the joint expectation, so each threshold or other bad event is counted
once, without a family-size or tree-count multiplier.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGExtractedTreeExpectation
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition SphericalGGTreeExtraction SphericalGGWeightObservable
open SphericalGGThresholdFirstMomentAverage
open scoped BigOperators
noncomputable section

local instance treeMeasurableSpace (depth n : ℕ) : MeasurableSpace (NestedPartition depth n) := ⊤

theorem treePMF_expectation {N depth n : ℕ} (cuts : Fin depth → ℝ) (hcuts : Monotone cuts)
    (mu : Measure (Fin n → UnitSpin N)) [IsProbabilityMeasure mu] (T : NestedPartition depth n → ℝ) :
    (∑ t,(treePMF cuts hcuts mu t).toReal*T t)=
      ∫ old,T (extractTree cuts hcuts old) ∂mu := by
  letI : IsProbabilityMeasure (mu.map (extractTree cuts hcuts)) :=
    (Measure.isProbabilityMeasure_map_iff (extractTree_measurable cuts hcuts).aemeasurable).mpr inferInstance
  have H := PMF.integral_eq_sum (treePMF cuts hcuts mu) T
  simp only [smul_eq_mul] at H
  rw [← H,treePMF,Measure.toPMF_toMeasure]
  exact integral_map (extractTree_measurable cuts hcuts).aemeasurable
    (show Measurable T from measurable_from_top).aestronglyMeasurable

private theorem masked_tree_measurable {N K depth r : ℕ} (cuts : Fin depth → ℝ) (hcuts : Monotone cuts)
    {S : Set (Fin K → ℝ)} (hS : MeasurableSet S) (T : NestedPartition depth (r+1) → ℝ) :
    Measurable (fun p : (Fin K → ℝ)×(Fin (r+1) → UnitSpin N) ↦
      S.indicator (fun _ ↦ T (extractTree cuts hcuts p.2)) p.1) := by
  classical
  have hT : Measurable T := measurable_from_top
  have hOld : Measurable (fun old : Fin (r+1) → UnitSpin N ↦ T (extractTree cuts hcuts old)) :=
    hT.comp (extractTree_measurable cuts hcuts)
  have H : Measurable (fun p : (Fin K → ℝ)×(Fin (r+1) → UnitSpin N) ↦
      if p.1∈S then T (extractTree cuts hcuts p.2) else (0 : ℝ)) :=
    Measurable.ite (hS.preimage measurable_fst) (hOld.comp measurable_snd) measurable_const
  convert H using 1 <;> rfl

theorem joint_masked_tree_expectation_eq_cube {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (r : ℕ) (cuts : Fin depth → ℝ) (hcuts : Monotone cuts)
    {S : Set (Fin K → ℝ)} (hS : MeasurableSet S) (T : NestedPartition depth (r+1) → ℝ)
    (hT : ∀ t,T t∈Icc (0 : ℝ) 1) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    (∫ q,S.indicator (fun _ ↦ T (extractTree cuts hcuts q.2)) q.1.1 ∂jointLaw nu v r)=
      ∫ x,S.indicator (fun x ↦ ∑ t,(treePMF cuts hcuts
        (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (r+1)) t).toReal*T t) x ∂positiveCubeLaw K := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let Phi : (Fin K → ℝ) → (Fin (r+1) → UnitSpin N) → ℝ :=
    fun x old ↦ S.indicator (fun _ ↦ T (extractTree cuts hcuts old)) x
  have hPhi := masked_tree_measurable (N := N) cuts hcuts hS T
  have hb (x old) : |Phi x old|≤1 := by
    by_cases hx : x∈S
    · rw [show Phi x old=T (extractTree cuts hcuts old) from indicator_of_mem hx _]
      rw [abs_of_nonneg (hT _).1]
      exact (hT _).2
    · rw [show Phi x old=0 from indicator_of_notMem hx _]; norm_num
  rw [joint_old_integral_eq_cube nu hv r Phi hPhi hb]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  by_cases hx : x∈S
  · simp only [Phi,indicator_of_mem hx]
    exact (treePMF_expectation cuts hcuts _ T).symm
  · simp only [Phi,indicator_of_notMem hx,integral_zero]

private theorem expectation_close_of_two_bad_events {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] {F G : X → ℝ}
    (hF : Measurable F) (hG : Measurable G) (hbF : ∀ x,F x∈Icc (0 : ℝ) 1) (hbG : ∀ x,G x∈Icc (0 : ℝ) 1)
    {B C : Set X} (hB : MeasurableSet B) (hC : MeasurableSet C) {eps : ℝ} (heps : 0≤eps)
    (hNear : ∀ x,x∉B→x∉C→|F x-G x|≤eps) :
    |(∫ x,F x ∂mu)-(∫ x,G x ∂mu)|≤eps+mu.real B+mu.real C := by
  have hFI : Integrable F mu := Integrable.of_bound hF.aestronglyMeasurable 1
    (Eventually.of_forall (fun x ↦ by rw [Real.norm_of_nonneg (hbF x).1]; exact (hbF x).2))
  have hGI : Integrable G mu := Integrable.of_bound hG.aestronglyMeasurable 1
    (Eventually.of_forall (fun x ↦ by rw [Real.norm_of_nonneg (hbG x).1]; exact (hbG x).2))
  have hBI := (integrable_const (μ := mu) (1 : ℝ)).indicator hB
  have hCI := (integrable_const (μ := mu) (1 : ℝ)).indicator hC
  have hAB : Integrable (fun x ↦ eps+B.indicator (fun _ ↦ (1 : ℝ)) x) mu :=
    (integrable_const eps).add hBI
  have hDom := ((integrable_const eps).add hBI).add hCI
  have hPoint (x : X) : |F x-G x|≤eps+B.indicator (fun _ ↦ (1 : ℝ)) x+C.indicator (fun _ ↦ (1 : ℝ)) x := by
    have hOne : |F x-G x|≤1 := abs_le.mpr ⟨by linarith only [(hbF x).1,(hbG x).2],by linarith only [(hbF x).2,(hbG x).1]⟩
    by_cases hb : x∈B <;> by_cases hc : x∈C
    · rw [indicator_of_mem hb,indicator_of_mem hc]; linarith only [hOne,heps]
    · rw [indicator_of_mem hb,indicator_of_notMem hc]; linarith only [hOne,heps]
    · rw [indicator_of_notMem hb,indicator_of_mem hc]; linarith only [hOne,heps]
    · simpa only [indicator_of_notMem hb,indicator_of_notMem hc,add_zero] using hNear x hb hc
  calc
    _ = |∫ x,F x-G x ∂mu| := by rw [integral_sub hFI hGI]
    _ ≤ ∫ x,|F x-G x| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ x,eps+B.indicator (fun _ ↦ (1 : ℝ)) x+C.indicator (fun _ ↦ (1 : ℝ)) x ∂mu :=
      integral_mono (hFI.sub hGI).abs hDom hPoint
    _ = _ := by
      rw [integral_add hAB hCI,integral_add (integrable_const eps) hBI,
        integral_const,probReal_univ,one_smul,integral_indicator_const 1 hB,integral_indicator_const 1 hC]
      simp only [smul_eq_mul,mul_one]

theorem selected_tree_expectation_error {A : Type*} [Fintype A] {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (r : ℕ) (cuts : A → Fin depth → ℝ) (hcuts : ∀ a,Monotone (cuts a))
    (S : A → Set (Fin K → ℝ)) (hS : ∀ a,MeasurableSet (S a))
    (hDis : ∀ a b,a≠b→Disjoint (S a) (S b)) (hCover : (⋃ a,S a)=univ)
    (F : (Fin (r+1) → UnitSpin N) → ℝ) (hF : Measurable F) (hbF : ∀ old,F old∈Icc (0 : ℝ) 1)
    (T : NestedPartition depth (r+1) → ℝ) (hT : ∀ t,T t∈Icc (0 : ℝ) 1)
    {C : Set (Fin (r+1) → UnitSpin N)} (hC : MeasurableSet C) {eps : ℝ} (heps : 0≤eps)
    (hNear : ∀ a old,thresholdGood (cuts a) old → old∉C → |F old-T (extractTree (cuts a) (hcuts a) old)|≤eps) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    |(∫ q,F q.2 ∂jointLaw (K := K) nu v r)-
      (∑ a,∫ x,(S a).indicator (fun x ↦ ∑ t,(treePMF (cuts a) (hcuts a)
        (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (r+1)) t).toReal*T t) x ∂positiveCubeLaw K)|≤
      eps+(jointLaw (K := K) nu v r).real {q | ∃ a,q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2}+
        (jointLaw (K := K) nu v r).real {q | q.2∈C} := by
  classical
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  letI := jointLaw_probability (K := K) nu hv r
  let Phi : A → (Fin K → ℝ) → (Fin (r+1) → UnitSpin N) → ℝ :=
    fun a x old ↦ (S a).indicator (fun _ ↦ T (extractTree (cuts a) (hcuts a) old)) x
  let Psi : (Fin K → ℝ) → (Fin (r+1) → UnitSpin N) → ℝ := fun x old ↦ ∑ a,Phi a x old
  have hExists (x : Fin K → ℝ) : ∃ a,x∈S a := by
    have H : x∈⋃ a,S a := by rw [hCover]; exact mem_univ x
    exact mem_iUnion.mp H
  have hPsiEq (x old a) (ha : x∈S a) : Psi x old=T (extractTree (cuts a) (hcuts a) old) := by
    have hOther (b : A) (hba : b≠a) : x∉S b := fun hb ↦ Set.disjoint_left.mp (hDis b a hba) hb ha
    dsimp only [Psi]
    rw [Finset.sum_eq_single a (fun b _ hba ↦ indicator_of_notMem (hOther b hba) _)
      (fun h ↦ False.elim (h (Finset.mem_univ a)))]
    exact indicator_of_mem ha _
  have hPhiM (a : A) : Measurable (fun p : (Fin K → ℝ)×(Fin (r+1) → UnitSpin N) ↦ Phi a p.1 p.2) :=
    masked_tree_measurable (cuts a) (hcuts a) (hS a) T
  have hPsiM : Measurable (fun p : (Fin K → ℝ)×(Fin (r+1) → UnitSpin N) ↦ Psi p.1 p.2) :=
    Finset.measurable_sum _ (fun a _ ↦ hPhiM a)
  have hPsiB (x old) : Psi x old∈Icc (0 : ℝ) 1 := by
    obtain ⟨a,ha⟩ := hExists x
    rw [hPsiEq x old a ha]
    exact hT _
  let B := {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+1) → UnitSpin N) |
    ∃ a,q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2}
  have hBM : MeasurableSet B := by
    have hEq : B=⋃ a,({q | q.1.1∈S a}∩{q | ¬thresholdGood (cuts a) q.2}) := by ext q; simp [B]
    rw [hEq]
    exact MeasurableSet.iUnion (fun a ↦ ((hS a).preimage measurable_fst.fst).inter
      (((thresholdGood_measurable (cuts a) (hcuts a)).compl).preimage measurable_snd))
  have hI (a : A) : Integrable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+1) → UnitSpin N) ↦
      Phi a q.1.1 q.2) (jointLaw (K := K) nu v r) := by
    have hb (q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+1) → UnitSpin N)) : |Phi a q.1.1 q.2|≤1 := by
      by_cases ha : q.1.1∈S a
      · rw [show Phi a q.1.1 q.2=T (extractTree (cuts a) (hcuts a) q.2) from indicator_of_mem ha _]
        rw [abs_of_nonneg (hT _).1]; exact (hT _).2
      · rw [show Phi a q.1.1 q.2=0 from indicator_of_notMem ha _]; norm_num
    exact Integrable.of_bound ((hPhiM a).comp (measurable_fst.fst.prodMk measurable_snd)).aestronglyMeasurable 1
      (Eventually.of_forall (fun q ↦ by simpa only [Real.norm_eq_abs] using hb q))
  have hMean : (∫ q,Psi q.1.1 q.2 ∂jointLaw (K := K) nu v r)=
      ∑ a,∫ x,(S a).indicator (fun x ↦ ∑ t,(treePMF (cuts a) (hcuts a)
        (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (r+1)) t).toReal*T t) x ∂positiveCubeLaw K := by
    rw [show (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+1) → UnitSpin N) ↦ Psi q.1.1 q.2)=
      (fun q ↦ ∑ a,Phi a q.1.1 q.2) from rfl,integral_finset_sum _ (fun a _ ↦ hI a)]
    exact Finset.sum_congr rfl (fun a _ ↦ joint_masked_tree_expectation_eq_cube nu hv r (cuts a) (hcuts a) (hS a) T hT)
  rw [← hMean]
  apply expectation_close_of_two_bad_events (jointLaw (K := K) nu v r)
    (hF.comp measurable_snd) (hPsiM.comp (measurable_fst.fst.prodMk measurable_snd))
    (fun q ↦ hbF q.2) (fun q ↦ hPsiB q.1.1 q.2) hBM (hC.preimage measurable_snd) heps
  intro q hNotB hNotC
  obtain ⟨a,ha⟩ := hExists q.1.1
  have hGood : thresholdGood (cuts a) q.2 := by
    by_contra hBad
    exact hNotB ⟨a,ha,hBad⟩
  change |F q.2-Psi q.1.1 q.2|≤eps
  rw [hPsiEq q.1.1 q.2 a ha]
  exact hNear a q.2 hGood hNotC

end
end TensorPCA.NonRSLowerProofs.SphericalGGExtractedTreeExpectation
