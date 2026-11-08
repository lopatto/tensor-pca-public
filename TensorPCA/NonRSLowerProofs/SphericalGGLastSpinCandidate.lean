-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGIndicatorTilt
public import TensorPCA.NonRSLowerProofs.FiniteGGConditionalLowMass

/-! Last-spin conditioning under the true joint amplitude/disorder and iid replica law.
Candidate masses retain the same physical spin kernel.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGLastSpinCandidate
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open SphericalGGWeightObservable SphericalGGThresholdWeights SphericalGGIndicatorTilt
open GGFiniteReplicaSnocIntegration FiniteGGConditionalLowMass
open scoped BigOperators
noncomputable section

def lastKernel {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (n : ℕ) :
    Kernel (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) (UnitSpin N) :=
  (parameterizedGibbsKernel nu v).comap Prod.fst measurable_fst

theorem lastKernel_markov {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) : IsMarkovKernel (lastKernel (K := K) nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  unfold lastKernel
  infer_instance

def appendLast {N K : ℕ} (n : ℕ)
    (p : (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×UnitSpin N) :
    ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N) :=
  (p.1.1,Fin.snoc p.1.2 p.2)

theorem appendLast_measurable (N K n : ℕ) : Measurable (appendLast (N := N) (K := K) n) :=
  measurable_fst.fst.prodMk ((snoc_measurable n).comp (measurable_fst.snd.prodMk measurable_snd))

theorem integral_appendLast_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ)
    (F : (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ p,|F p|≤C) :
    (∫ p,F p ∂jointLaw nu v (n+1))=
      ∫ p,F (appendLast n p) ∂((jointLaw nu v n)⊗ₘlastKernel nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  letI := lastKernel_markov (K := K) nu hv n
  letI := jointLaw_probability nu hv n (K := K)
  have HI : Integrable (fun p ↦ F (appendLast n p)) ((jointLaw nu v n)⊗ₘlastKernel nu v n) :=
    Integrable.of_bound (hF.comp (appendLast_measurable N K n)).aestronglyMeasurable C
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hB (appendLast n p)))
  rw [Measure.integral_compProd HI]
  simpa only [jointLaw,lastKernel,Kernel.comap_apply,appendLast] using
    integral_joint_iid_snoc ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)))
      (parameterizedGibbsKernel nu v) n F hF hB

def thresholdPairSet {N K : ℕ} (n : ℕ) (u : ℝ) :
    Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×(UnitSpin N×UnitSpin N)) :=
  {p | u≤unitOverlap p.2.2 p.2.1}

theorem appendLast_hasLaw {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) :
    HasLaw (appendLast (N := N) (K := K) n) (jointLaw nu v (n+1))
      ((jointLaw nu v n)⊗ₘlastKernel nu v n) := by
  letI := lastKernel_markov (K := K) nu hv n
  letI := jointLaw_probability nu hv n (K := K)
  letI := jointLaw_probability nu hv (n+1) (K := K)
  refine ⟨(appendLast_measurable N K n).aemeasurable,?_⟩
  apply Measure.ext
  intro S hS
  have hF : Measurable (S.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hS
  have hB (p) : |S.indicator (fun _ ↦ (1 : ℝ)) p|≤1 := by
    by_cases hp : p∈S
    · rw [indicator_of_mem hp]; norm_num
    · rw [indicator_of_notMem hp]; norm_num
  have H := integral_appendLast_eq nu hv n (S.indicator (fun _ ↦ (1 : ℝ))) hF hB
  rw [← integral_map (appendLast_measurable N K n).aemeasurable hF.aestronglyMeasurable] at H
  simp only [integral_indicator_const (1 : ℝ) hS,smul_eq_mul,mul_one] at H
  exact (measureReal_eq_measureReal_iff).mp H.symm

theorem thresholdPairSet_measurable (N K n : ℕ) (u : ℝ) :
    MeasurableSet (thresholdPairSet (N := N) (K := K) n u) :=
  measurableSet_le measurable_const ((SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp
    (measurable_snd.snd.prodMk measurable_snd.fst))

theorem candidateMass_eq_membershipMass {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u : ℝ)
    (p : (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×UnitSpin N) :
    candidateMass (lastKernel nu v n) (thresholdPairSet n u) p=
      membershipMass nu v (n+1) u (appendLast n p) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let S : Set (UnitSpin N) := {z | u≤unitOverlap z p.2}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    ((SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp (measurable_id.prodMk measurable_const))
  change (parameterizedGibbsKernel nu v p.1.1).real S=_
  have hMass : (∫ z,S.indicator (fun _ ↦ (1 : ℝ)) z ∂parameterizedGibbsKernel nu v p.1.1)=
      (parameterizedGibbsKernel nu v p.1.1).real S := by
    simpa only [smul_eq_mul,mul_one] using integral_indicator_const (1 : ℝ) hS
  rw [← hMass]
  change (∫ z,S.indicator (fun _ ↦ (1 : ℝ)) z ∂parameterizedGibbsKernel nu v p.1.1)=
    ∫ z,thresholdMembership (n+1) u (Fin.snoc p.1.2 p.2,z) ∂parameterizedGibbsKernel nu v p.1.1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z ↦ by
    simp only [Fin.snoc_last,thresholdMembership,S,indicator_apply,mem_setOf_eq,mem_Ici])

end
end TensorPCA.NonRSLowerProofs.SphericalGGLastSpinCandidate
