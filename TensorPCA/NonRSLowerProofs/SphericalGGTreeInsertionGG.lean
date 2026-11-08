-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionResidual
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionScoreBounds
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! All-branch cylinder insertion from global anchored ball residuals. Every source of
probability is a literal consecutive iid Gibbs law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionGG
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGJetFamily
open SphericalGGTreeBallAverage SphericalGGTreeInsertionResidual
open SphericalGGTreeInsertionScore SphericalGGTreeInsertionBalls SphericalGGTreeInsertionScoreBounds
open GGFiniteReplicaConsIntegration
open SphericalGGThresholdFirstMomentAverage GGFiniteFirstJet
open FiniteNestedPartition FiniteNestedInsertionNumerators
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

private theorem fresh_cons_hasLaw {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]
    (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) :
    HasLaw (fun s : Fin (n+2)→V ↦ Fin.cons (s (Fin.last (n+1))) (initial s))
      (law d G (n+2)) (law d G (n+2)) := by
  have h0 : (finRotate (n+2)).symm 0=Fin.last (n+1) := by
    apply (finRotate (n+2)).injective
    rw [Equiv.apply_symm_apply,finRotate_last]
  have hs (j : Fin (n+1)) : (finRotate (n+2)).symm j.succ=j.castSucc := by
    apply (finRotate (n+2)).injective
    rw [Equiv.apply_symm_apply]
    exact (finRotate_of_lt j.isLt).symm
  have hFun : (fun s : Fin (n+2)→V ↦ fun i ↦ s ((finRotate (n+2)).symm i))=
      (fun s ↦ Fin.cons (s (Fin.last (n+1))) (initial s)) := by
    funext s i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [h0,Fin.cons_zero]
    · simp only [hs,Fin.cons_succ,initial]
  rw [← hFun]
  exact replica_permutation_hasLaw d G (n+2) (finRotate (n+2)).symm


private theorem integral_list_map {A B : Type*} [MeasurableSpace A]
    (mu : Measure A) (xs : List B) (f : B→A→ℝ) (hi : ∀b,Integrable (f b) mu) :
    Integrable (fun a ↦ (xs.map (fun b ↦ f b a)).sum) mu ∧
      (∫a,(xs.map (fun b ↦ f b a)).sum ∂mu)=(xs.map (fun b ↦ ∫a,f b a ∂mu)).sum := by
  induction xs with
  | nil => exact ⟨by simpa using (integrable_zero A ℝ mu),by simp⟩
  | cons b xs ih =>
    simp only [List.map_cons,List.sum_cons]
    refine ⟨(hi b).add ih.1,?_⟩
    rw [integral_add (hi b) ih.1,ih.2]

/-- Each nested insertion is a finite combination of global ball events. The resulting
terms are ball GG residuals and bad-event mass.
-/
theorem cylinderInsertionResidual_le_ball_errors {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (x : Fin K→ℝ) (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (t : NestedPartition depth (n+1)) (o : Insertion depth (n+1) t) :
    let balls := insertionBalls depth (n+1) t o
    |cylinderInsertionResidual nu v cuts t o x|≤
      balls.1.elim 0 (fun b ↦ |freshBallResidual nu v cuts t b.1 b.2 x|)+
      (balls.2.map (fun b ↦ |freshBallResidual nu v cuts t b.1 b.2 x|)).sum+
      ((n : ℝ)+3)*(law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+2)).real {s | ¬thresholdGood cuts s} := by
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let mu := law d G (n+2)
  let tNext := (extendEquiv depth (n+1)) ⟨t,o⟩
  let balls := insertionBalls depth (n+1) t o
  let R : (Fin (n+2)→UnitSpin N)→(Fin (n+2)→UnitSpin N) :=
    fun s ↦ Fin.cons (s (Fin.last (n+1))) (initial s)
  let O : (Fin (n+1)→UnitSpin N)→ℝ := {old | treeCylinder cuts t old}.indicator (fun _ ↦ 1)
  let A : (Fin (n+2)→UnitSpin N)→ℝ := {s | treeCylinder cuts tNext s}.indicator (fun _ ↦ 1)
  let Z : (Fin (n+2)→UnitSpin N)→ℝ := {s | ¬thresholdGood cuts s}.indicator (fun _ ↦ 1)
  let U : (Fin depth×Fin (n+1))→(Fin (n+2)→UnitSpin N)→ℝ := fun b s ↦
    (Ici (cuts b.1)).indicator (fun _ ↦ 1) (unitOverlap (s b.2.castSucc) (s (Fin.last (n+1))))
  let W : (Fin depth×Fin (n+1))→(Fin (n+2)→UnitSpin N)→ℝ := fun b s ↦ O (initial s)*U b s
  let F : (Fin depth×Fin (n+1))→ℝ := fun b ↦ ∫s,W b s ∂mu
  let C : (Fin depth×Fin (n+1))→ℝ := fun b ↦ (ballSize t b.1 b.2 : ℝ)-lowerHeight nu v (cuts b.1) x
  let oldMass : ℝ := ∫old,O old ∂law d G (n+1)
  let L : (Fin (n+2)→UnitSpin N)→ℝ := fun s ↦ O (initial s)*
    insertionScore depth (n+1) cuts t o (initial s) (s (Fin.last (n+1))) 1
  have hR : Measurable R := (cons_measurable (n+1)).comp
    ((initial_measurable _).prodMk (measurable_pi_apply _))
  have hLaw : HasLaw R mu mu := fresh_cons_hasLaw d G n
  have hOm : Measurable O := measurable_const.indicator (treeCylinder_measurable cuts t)
  have hAm : Measurable A := measurable_const.indicator (treeCylinder_measurable cuts tNext)
  have hBad : MeasurableSet {s : Fin (n+2)→UnitSpin N | ¬thresholdGood cuts s} :=
    (thresholdGood_measurable cuts hcuts).compl
  have hZm : Measurable Z := measurable_const.indicator hBad
  have hOb (old) : |O old|≤1 := by by_cases h : treeCylinder cuts t old <;> simp [O,h]
  have hAb (s) : |A s|≤1 := by by_cases h : treeCylinder cuts tNext s <;> simp [A,h]
  have hZb (s) : |Z s|≤1 := by by_cases h : thresholdGood cuts s <;> simp [Z,h]
  have hUm (b : Fin depth×Fin (n+1)) : Measurable (U b) := by
    have hPair : Measurable (fun s : Fin (n+2)→UnitSpin N ↦ (s b.2.castSucc,s (Fin.last (n+1)))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (measurable_const.indicator measurableSet_Ici).comp
      ((SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair)
  have hUb (b : Fin depth×Fin (n+1)) (s) : |U b s|≤1 := by
    by_cases h : unitOverlap (s b.2.castSucc) (s (Fin.last (n+1)))∈Ici (cuts b.1) <;> simp [U,h]
  have hWi (b : Fin depth×Fin (n+1)) : Integrable (W b) mu := by
    apply Integrable.of_bound ((hOm.comp (initial_measurable _)).mul (hUm b)).aestronglyMeasurable 1
    exact .of_forall (fun s ↦ by
      change |O (initial s)*U b s|≤1
      rw [abs_mul]
      exact (mul_le_mul (hOb _) (hUb b s) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hOi : Integrable (fun s : Fin (n+2)→UnitSpin N ↦ O (initial s)) mu :=
    Integrable.of_bound (hOm.comp (initial_measurable _)).aestronglyMeasurable 1
      (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hOb (initial s)))
  have hLm : Measurable L := (hOm.comp (initial_measurable _)).mul
    ((insertionScore_joint_measurable depth (n+1) cuts t o).comp
      ((initial_measurable _).prodMk (measurable_pi_apply _)))
  have hLi : Integrable L mu := by
    apply Integrable.of_bound hLm.aestronglyMeasurable ((n : ℝ)+2)
    exact .of_forall (fun s ↦ by
      change |O (initial s)*insertionScore depth (n+1) cuts t o (initial s) (s (Fin.last (n+1))) 1|≤(n : ℝ)+2
      rw [abs_mul]
      have H := insertionScore_abs_le depth (n+1) cuts t o (initial s) (s (Fin.last (n+1)))
      norm_num only [Nat.cast_add,Nat.cast_one] at H
      have H' := mul_le_mul (hOb (initial s)) H (abs_nonneg _) zero_le_one
      simpa only [one_mul,add_assoc,one_add_one_eq_two] using H')
  have hAi : Integrable (fun s ↦ A (R s)) mu := Integrable.of_bound (hAm.comp hR).aestronglyMeasurable 1
    (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hAb (R s)))
  have hZi : Integrable (fun s ↦ Z (R s)) mu := Integrable.of_bound (hZm.comp hR).aestronglyMeasurable 1
    (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hZb (R s)))
  have hPoint (s) : |A (R s)-L s|≤((n : ℝ)+3)*Z (R s) := by
    have H := insertion_indicator_error_le_bad depth (n+1) cuts hcuts hcuts1 t o (initial s) (s (Fin.last (n+1)))
    simpa only [A,O,L,R,Z,tNext,Set.indicator_apply,mem_setOf_eq,Nat.cast_add,Nat.cast_one,add_assoc,show (1 : ℝ)+2=3 by norm_num] using H
  have hError : |(∫s,A (R s) ∂mu)-(∫s,L s ∂mu)|≤((n : ℝ)+3)*(∫s,Z (R s) ∂mu) := by
    rw [← integral_sub hAi hLi]
    have H := (norm_integral_le_integral_norm (f := fun s ↦ A (R s)-L s) (μ := mu)).trans
      (integral_mono (hAi.sub hLi).norm (hZi.const_mul ((n : ℝ)+3)) (fun s ↦ by
        simpa only [Real.norm_eq_abs] using hPoint s))
    simpa only [Real.norm_eq_abs,integral_const_mul] using H
  have hAMean : (∫s,A (R s) ∂mu)=mu.real {s | treeCylinder cuts tNext s} := by
    have H := hLaw.integral_comp hAm.aestronglyMeasurable
    simp only [Function.comp_def] at H
    rw [H]
    change (∫s,{s | treeCylinder cuts tNext s}.indicator (fun _ ↦ (1 : ℝ)) s ∂mu)=_
    rw [integral_indicator_const (1 : ℝ) (treeCylinder_measurable cuts tNext),smul_eq_mul,mul_one]
  have hZMean : (∫s,Z (R s) ∂mu)=mu.real {s | ¬thresholdGood cuts s} := by
    have H := hLaw.integral_comp hZm.aestronglyMeasurable
    simp only [Function.comp_def] at H
    rw [H]
    change (∫s,{s | ¬thresholdGood cuts s}.indicator (fun _ ↦ (1 : ℝ)) s ∂mu)=_
    rw [integral_indicator_const (1 : ℝ) hBad,smul_eq_mul,mul_one]
  rw [hAMean,hZMean] at hError
  have hScore (s) : insertionScore depth (n+1) cuts t o (initial s) (s (Fin.last (n+1))) 1=
      supportValue balls (fun b ↦ U b s) 1 := by
    simpa only [balls,U,Set.indicator_apply,mem_Ici,unitOverlap,real_inner_comm,initial] using
      insertionScore_eq_supportValue depth (n+1) cuts t o (initial s) (s (Fin.last (n+1))) 1
  have hFun : L=(fun s ↦ balls.1.elim (O (initial s)) (fun b ↦ W b s)-
      (balls.2.map (fun b ↦ W b s)).sum) := by
    funext s
    dsimp only [L]
    rw [hScore]
    change O (initial s)*(balls.1.elim 1 (fun b ↦ U b s)-(balls.2.map (fun b ↦ U b s)).sum)=_
    cases hp : balls.1 <;> simp only [hp,Option.elim_none,Option.elim_some,W,List.sum_map_mul_left] <;> ring
  have hParentI : Integrable (fun s ↦ balls.1.elim (O (initial s)) (fun b ↦ W b s)) mu := by
    cases hp : balls.1
    · exact hOi
    · exact hWi _
  have hParentMean : (∫s,balls.1.elim (O (initial s)) (fun b ↦ W b s) ∂mu)=balls.1.elim oldMass F := by
    cases hp : balls.1
    · exact prefix_test_mean d G n O hOm
    · rfl
  have hList := integral_list_map mu balls.2 W hWi
  have hMean : (∫s,L s ∂mu)=supportValue balls F oldMass := by
    rw [hFun,integral_sub hParentI hList.1,hParentMean,hList.2]
    rfl
  have hRes (b : Fin depth×Fin (n+1)) : freshBallResidual nu v cuts t b.1 b.2 x=
      F b-oldMass*C b/((n : ℝ)+1) := rfl
  have hNum : supportValue balls C ((n : ℝ)+1)=numerator depth (n+1)
      (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o := by
    simpa only [Nat.cast_add,Nat.cast_one,sub_zero] using supportValue_ballSize_sub_eq_numerator depth (n+1)
      (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o
  let Eball : (Fin depth×Fin (n+1))→ℝ := fun b ↦ freshBallResidual nu v cuts t b.1 b.2 x
  have hParent : balls.1.elim oldMass F-oldMass*(balls.1.elim ((n : ℝ)+1) C)/((n : ℝ)+1)=balls.1.elim 0 Eball := by
    cases hp : balls.1
    · simp only [Option.elim_none]
      field_simp
      ring
    · simp only [Option.elim_some]
      exact (hRes _).symm
  have hListScalar (xs : List (Fin depth×Fin (n+1))) :
      (xs.map Eball).sum=(xs.map F).sum-oldMass*(xs.map C).sum/((n : ℝ)+1) := by
    induction xs with
    | nil => simp
    | cons b xs ih =>
      simp only [List.map_cons,List.sum_cons,Eball]
      rw [hRes,ih]
      ring
  have hLinear : (∫s,L s ∂mu)-oldMass*(numerator depth (n+1)
      (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/((n : ℝ)+1))=supportValue balls Eball 0 := by
    rw [hMean,← hNum]
    change (balls.1.elim oldMass F-(balls.2.map F).sum)-oldMass*(
      (balls.1.elim ((n : ℝ)+1) C-(balls.2.map C).sum)/((n : ℝ)+1))=_
    calc
      _=(balls.1.elim oldMass F-oldMass*(balls.1.elim ((n : ℝ)+1) C)/((n : ℝ)+1))-
          ((balls.2.map F).sum-oldMass*(balls.2.map C).sum/((n : ℝ)+1)) := by ring
      _=_ := by rw [hParent,← hListScalar]; rfl
  have hListAbs (xs : List (Fin depth×Fin (n+1))) : |(xs.map Eball).sum|≤(xs.map (fun b ↦ |Eball b|)).sum := by
    induction xs with
    | nil => simp
    | cons b xs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add le_rfl ih)
  have hLinearAbs : |(∫s,L s ∂mu)-oldMass*(numerator depth (n+1)
      (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/((n : ℝ)+1))|≤
      balls.1.elim 0 (fun b ↦ |Eball b|)+(balls.2.map (fun b ↦ |Eball b|)).sum := by
    rw [hLinear]
    apply (abs_sub _ _).trans
    have hPar : |balls.1.elim 0 Eball|=balls.1.elim 0 (fun b ↦ |Eball b|) := by cases balls.1 <;> simp
    rw [hPar]
    exact add_le_add le_rfl (hListAbs balls.2)
  have hOldMass : oldMass=(law d G (n+1)).real {old | treeCylinder cuts t old} := by
    dsimp only [oldMass,O]
    rw [integral_indicator_const (1 : ℝ) (treeCylinder_measurable cuts t),smul_eq_mul,mul_one]
  rw [hOldMass] at hLinearAbs
  unfold cylinderInsertionResidual
  simp only [Nat.cast_add,Nat.cast_one]
  change |mu.real {s | treeCylinder cuts tNext s}-(law d G (n+1)).real {old | treeCylinder cuts t old}*
    (numerator depth (n+1) (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/((n : ℝ)+1))|≤_
  calc
    _≤|mu.real {s | treeCylinder cuts tNext s}-(∫s,L s ∂mu)|+
        |(∫s,L s ∂mu)-(law d G (n+1)).real {old | treeCylinder cuts t old}*
          (numerator depth (n+1) (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/((n : ℝ)+1))| := abs_sub_le _ _ _
    _≤_ := add_le_add hError hLinearAbs
    _=_ := add_comm _ _


end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionGG
