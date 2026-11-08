-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeBallAverage
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRootSupport
public import TensorPCA.NonRSLowerProofs.GGFiniteReplicaConsIntegration

/-! Root-new cylinder insertion from fresh-ball GG rows. Iid integration transports
fresh zero to fresh last, and each root-ball partition failure is charged its
threshold-bad probability. Good-array restrictions are not renormalized.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeRootInsertionGG
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeInsertionSupport
open SphericalGGTreeRootSupport SphericalGGTreeBallAverage SphericalGGJetFamily
open SphericalGGThresholdFirstMomentAverage GGFiniteFirstJet
open GGFiniteReplicaConsIntegration GGFiniteReplicaSnocIntegration
open FiniteNestedPartition FiniteNestedPartitionOverlap
open FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

private theorem integral_law_cons_snoc {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    (f : (Fin (n+2)→V)→ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀s,|f s|≤C) :
    (∫s,f s ∂law d G (n+2))=
      ∫s,f (Fin.cons (s (Fin.last (n+1))) (initial s)) ∂law d G (n+2) := by
  let R : (Fin (n+2)→V)→(Fin (n+2)→V) := fun s ↦ Fin.cons (s (Fin.last (n+1))) (initial s)
  have hR : Measurable R := (cons_measurable (n+1)).comp
    ((initial_measurable _).prodMk (measurable_pi_apply _))
  rw [integral_law_eq_nested d G (n+2) f hf hb,
    integral_law_eq_nested d G (n+2) (fun s ↦ f (R s)) (hf.comp hR) (fun s ↦ hb (R s))]
  apply integral_congr_ae
  refine .of_forall (fun w ↦ ?_)
  dsimp only
  rw [integral_pi_cons (G w) (n+1) f hf hb,
    integral_pi_snoc (G w) n (fun s ↦ f (R s)) (hf.comp hR) (fun s ↦ hb (R s))]
  have hi (old : Fin (n+1)→V) (fresh : V) : initial (Fin.snoc old fresh)=old := by
    funext i
    simp only [initial,Fin.snoc_castSucc]
  simp only [R,Fin.snoc_last,hi]

private theorem integral_indicator_real {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (S : Set A) (hS : MeasurableSet S) :
    (∫s,S.indicator (fun _ ↦ (1 : ℝ)) s ∂mu)=mu.real S := by
  rw [integral_indicator_const (1 : ℝ) hS,smul_eq_mul,mul_one]

/-- The root-new coefficient is the number of root children times the lower-tail height
under the amplitude's pair law, divided by the full old count.
-/
theorem root_new_cylinder_error_le {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (x : Fin K→ℝ) (cuts : Fin (depth+1)→ℝ) (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (c : OrderedFinpartition (n+1)) (f : Children depth c) :
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := (parameterizedGibbsKernel nu v).sectR x
    let t : NestedPartition (depth+1) (n+1) := ⟨c,f⟩
    let tNext := (extendEquiv (depth+1) (n+1)) ⟨t,none⟩
    |(law d G (n+2)).real {s | treeCylinder cuts tNext s}-
      (law d G (n+1)).real {old | treeCylinder cuts t old}*
        ((c.length : ℝ)*lowerHeight nu v (cuts 0) x)/((n : ℝ)+1)|≤
      (∑b : Fin c.length,|freshBallResidual nu v cuts t 0 (c.emb b ⟨0,c.partSize_pos b⟩) x|)+
        ((c.length : ℝ)+2)*(law d G (n+2)).real {s | ¬thresholdGood cuts s} := by
  classical
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let mu := law d G (n+2)
  let t : NestedPartition (depth+1) (n+1) := ⟨c,f⟩
  let tNext := (extendEquiv (depth+1) (n+1)) ⟨t,none⟩
  let R : (Fin (n+2)→UnitSpin N)→(Fin (n+2)→UnitSpin N) :=
    fun s ↦ Fin.cons (s (Fin.last (n+1))) (initial s)
  let O : (Fin (n+1)→UnitSpin N)→ℝ := {old | treeCylinder cuts t old}.indicator (fun _ ↦ 1)
  let A : (Fin (n+2)→UnitSpin N)→ℝ := {s | treeCylinder cuts tNext s}.indicator (fun _ ↦ 1)
  let Z : (Fin (n+2)→UnitSpin N)→ℝ := {s | ¬thresholdGood cuts s}.indicator (fun _ ↦ 1)
  let U : Fin c.length→(Fin (n+2)→UnitSpin N)→ℝ := fun b s ↦
    (Ici (cuts 0)).indicator (fun _ ↦ 1)
      (unitOverlap (s (c.emb b ⟨0,c.partSize_pos b⟩).castSucc) (s (Fin.last (n+1))))
  let L : (Fin (n+2)→UnitSpin N)→ℝ := fun s ↦ O (initial s)*(1-∑b,U b s)
  let F : Fin c.length→ℝ := fun b ↦ ∫s,O (initial s)*U b s ∂mu
  let oldMass : ℝ := ∫old,O old ∂law d G (n+1)
  have hR : Measurable R := (cons_measurable (n+1)).comp
    ((initial_measurable _).prodMk (measurable_pi_apply _))
  have hOm : Measurable O := measurable_const.indicator (treeCylinder_measurable cuts t)
  have hAm : Measurable A := measurable_const.indicator (treeCylinder_measurable cuts tNext)
  have hZm : Measurable Z := measurable_const.indicator (thresholdGood_measurable cuts hcuts).compl
  have hOb (old) : |O old|≤1 := by by_cases h : treeCylinder cuts t old <;> simp [O,h]
  have hAb (s) : |A s|≤1 := by by_cases h : treeCylinder cuts tNext s <;> simp [A,h]
  have hZb (s) : |Z s|≤1 := by by_cases h : thresholdGood cuts s <;> simp [Z,h]
  have hUm (b : Fin c.length) : Measurable (U b) := by
    have hPair : Measurable (fun s : Fin (n+2)→UnitSpin N ↦
        (s (c.emb b ⟨0,c.partSize_pos b⟩).castSucc,s (Fin.last (n+1)))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (measurable_const.indicator measurableSet_Ici).comp
      ((SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair)
  have hUb (b : Fin c.length) (s) : U b s∈Icc (0 : ℝ) 1 := by
    by_cases h : unitOverlap (s (c.emb b ⟨0,c.partSize_pos b⟩).castSucc) (s (Fin.last (n+1)))∈Ici (cuts 0) <;> simp [U,h]
  have hLm : Measurable L := (hOm.comp (initial_measurable _)).mul
    (measurable_const.sub (Finset.measurable_sum _ (fun b _ ↦ hUm b)))
  have hLb (s) : |L s|≤1+(c.length : ℝ) := by
    have hS0 : 0≤∑b : Fin c.length,U b s := Finset.sum_nonneg (fun b _ ↦ (hUb b s).1)
    have hS1 : (∑b : Fin c.length,U b s)≤(c.length : ℝ) := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
        Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ (hUb b s).2)
    have hS : |1-∑b,U b s|≤1+(c.length : ℝ) :=
      abs_le.mpr ⟨by linarith only [hS1],by linarith only [hS0]⟩
    dsimp only [L]
    rw [abs_mul]
    exact (mul_le_mul (hOb _) hS (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hAi : Integrable (fun s ↦ A (R s)) mu := Integrable.of_bound (hAm.comp hR).aestronglyMeasurable 1
    (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hAb (R s)))
  have hLi : Integrable L mu := Integrable.of_bound hLm.aestronglyMeasurable (1+(c.length : ℝ))
    (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hLb s))
  have hZi : Integrable (fun s ↦ Z (R s)) mu := Integrable.of_bound (hZm.comp hR).aestronglyMeasurable 1
    (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hZb (R s)))
  have hPoint (s) : |A (R s)-L s|≤((c.length : ℝ)+2)*Z (R s) := by
    by_cases hg : thresholdGood cuts (R s)
    · have H := root_new_indicator_eq cuts hcuts hcuts1 c f (initial s) (s (Fin.last (n+1))) hg
      have hEq : A (R s)=L s := by
        simpa only [A,O,L,U,R,t,tNext,initial,Set.indicator_apply,mem_setOf_eq,mem_Ici,unitOverlap,real_inner_comm] using H
      rw [hEq,sub_self,abs_zero]
      simp [Z,hg]
    · have hZ : Z (R s)=1 := by simp [Z,hg]
      rw [hZ,mul_one]
      exact (abs_sub _ _).trans (by linarith only [hAb (R s),hLb s])
  have hError : |(∫s,A (R s) ∂mu)-(∫s,L s ∂mu)|≤
      ((c.length : ℝ)+2)*(∫s,Z (R s) ∂mu) := by
    rw [← integral_sub hAi hLi]
    have H := (norm_integral_le_integral_norm (f := fun s ↦ A (R s)-L s) (μ := mu)).trans
      (integral_mono (hAi.sub hLi).norm (hZi.const_mul ((c.length : ℝ)+2)) (fun s ↦ by
        simpa only [Real.norm_eq_abs] using hPoint s))
    simpa only [Real.norm_eq_abs,integral_const_mul] using H
  have hAMean : (∫s,A (R s) ∂mu)=mu.real {s | treeCylinder cuts tNext s} := by
    rw [← integral_law_cons_snoc d G n A hAm hAb]
    exact integral_indicator_real mu _ (treeCylinder_measurable cuts tNext)
  have hZMean : (∫s,Z (R s) ∂mu)=mu.real {s | ¬thresholdGood cuts s} := by
    rw [← integral_law_cons_snoc d G n Z hZm hZb]
    exact integral_indicator_real mu _ (thresholdGood_measurable cuts hcuts).compl
  rw [hAMean,hZMean] at hError
  have hFi (b : Fin c.length) : Integrable (fun s ↦ O (initial s)*U b s) mu := by
    apply Integrable.of_bound ((hOm.comp (initial_measurable _)).mul (hUm b)).aestronglyMeasurable 1
    exact .of_forall (fun s ↦ by
      change |O (initial s)*U b s|≤1
      rw [abs_mul,abs_of_nonneg (hUb b s).1]
      exact (mul_le_mul (hOb _) (hUb b s).2 (hUb b s).1 zero_le_one).trans_eq (one_mul _))
  have hOi : Integrable (fun s : Fin (n+2)→UnitSpin N ↦ O (initial s)) mu :=
    Integrable.of_bound (hOm.comp (initial_measurable _)).aestronglyMeasurable 1
      (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hOb (initial s)))
  have hLMean : (∫s,L s ∂mu)=oldMass-∑b,F b := by
    have hFun : L=(fun s ↦ O (initial s)-∑b,O (initial s)*U b s) := by
      funext s
      dsimp only [L]
      rw [← Finset.mul_sum]
      ring
    rw [hFun,integral_sub hOi (integrable_finsetSum Finset.univ (fun b _ ↦ hFi b)),
      integral_finsetSum Finset.univ (fun b _ ↦ hFi b),prefix_test_mean d G n O hOm]
  have hRes (b : Fin c.length) : freshBallResidual nu v cuts t 0 (c.emb b ⟨0,c.partSize_pos b⟩) x=
      F b-oldMass*((c.partSize b : ℝ)-lowerHeight nu v (cuts 0) x)/((n : ℝ)+1) := by
    unfold freshBallResidual
    dsimp only
    rw [ballSize_zero_emb c f]
  have hSizes : (∑b : Fin c.length,(c.partSize b : ℝ))=(n : ℝ)+1 := by exact_mod_cast sum_partSize c
  have hLinear : (∫s,L s ∂mu)-oldMass*((c.length : ℝ)*lowerHeight nu v (cuts 0) x)/((n : ℝ)+1)=
      -(∑b : Fin c.length,freshBallResidual nu v cuts t 0 (c.emb b ⟨0,c.partSize_pos b⟩) x) := by
    rw [hLMean]
    simp_rw [hRes]
    rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum,Finset.sum_sub_distrib,hSizes]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  have hLinearAbs : |(∫s,L s ∂mu)-oldMass*((c.length : ℝ)*lowerHeight nu v (cuts 0) x)/((n : ℝ)+1)|≤
      ∑b : Fin c.length,|freshBallResidual nu v cuts t 0 (c.emb b ⟨0,c.partSize_pos b⟩) x| := by
    rw [hLinear,abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hOldMass : oldMass=(law d G (n+1)).real {old | treeCylinder cuts t old} :=
    integral_indicator_real _ _ (treeCylinder_measurable cuts t)
  rw [hOldMass] at hLinearAbs
  calc
    _≤|mu.real {s | treeCylinder cuts tNext s}-(∫s,L s ∂mu)|+
        |(∫s,L s ∂mu)-(law d G (n+1)).real {old | treeCylinder cuts t old}*
          ((c.length : ℝ)*lowerHeight nu v (cuts 0) x)/((n : ℝ)+1)| := abs_sub_le _ _ _
    _≤_ := add_le_add hError hLinearAbs
    _=_ := add_comm _ _

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeRootInsertionGG
