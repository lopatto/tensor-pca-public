-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdWeights

/-! Exact indicator tilt identities in the full-amplitude Gibbs model. The last/fresh
overlap orientation is matched by inner symmetry.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGIndicatorTilt
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteFirstJet GGFiniteReweightingDerivative GGFiniteReplicaWeightMoments
open SphericalGGJetFamily SphericalGGThresholdWeights FiniteGGWindowScalar
open scoped BigOperators
noncomputable section

theorem threshold_score_eq {N : ℕ} (n : ℕ) (u : ℝ) (old : Fin (n+1) → UnitSpin N) (z : UnitSpin N) :
    score n unitOverlap (thresholdScore n u) old z=thresholdMembership n u (old,z) := by
  unfold score
  rw [Fin.sum_univ_castSucc]
  simp only [thresholdScore,Fin.snoc_castSucc,Fin.snoc_last,Finset.sum_const_zero,zero_add,thresholdMembership]
  congr 1
  exact (real_inner_comm (old (Fin.last n)).val z.val).symm

def membershipMass {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (u : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) : ℝ :=
  ∫ z, thresholdMembership n u (p.2,z) ∂parameterizedGibbsKernel nu v p.1

theorem membershipMass_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u : ℝ) : Measurable (membershipMass (K := K) nu v n u) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let kap : Kernel (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) (UnitSpin N) :=
    (parameterizedGibbsKernel nu v).comap Prod.fst measurable_fst
  have H := ((thresholdMembership_measurable N n u).comp
    (measurable_fst.snd.prodMk measurable_snd)).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)
  convert H.measurable using 1 <;> rfl

theorem membershipMass_mem {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    membershipMass nu v n u p∈Icc (0 : ℝ) 1 := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  refine ⟨integral_nonneg (fun z ↦ (thresholdMembership_mem n u (p.2,z)).1),?_⟩
  have H := norm_integral_le_of_norm_le_const (μ := parameterizedGibbsKernel nu v p.1)
    (f := fun z ↦ thresholdMembership n u (p.2,z)) (C := 1) (Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (thresholdMembership_mem n u (p.2,z)).1]
      exact (thresholdMembership_mem n u (p.2,z)).2))
  exact (le_abs_self _).trans (by simpa only [membershipMass,Real.norm_eq_abs,probReal_univ,mul_one] using H)

private theorem threshold_integrable {N : ℕ} (mu : Measure (UnitSpin N)) [IsProbabilityMeasure mu]
    (n : ℕ) (u : ℝ) (old : Fin (n+1) → UnitSpin N) :
    Integrable (fun z ↦ thresholdMembership n u (old,z)) mu := by
  apply Integrable.of_bound ((thresholdMembership_measurable N n u).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by
    change |thresholdMembership n u (old,z)|≤1
    rw [abs_of_nonneg (thresholdMembership_mem n u (old,z)).1]
    exact (thresholdMembership_mem n u (old,z)).2)

private theorem exp_threshold (n : ℕ) (u t : ℝ) {N : ℕ} (old : Fin (n+1) → UnitSpin N) (z : UnitSpin N) :
    Real.exp (t*thresholdMembership n u (old,z))=1+(Real.exp t-1)*thresholdMembership n u (old,z) := by
  unfold thresholdMembership
  by_cases h : unitOverlap z (old (Fin.last n))∈Ici u
  · simp only [indicator_of_mem h,mul_one]; ring
  · simp only [indicator_of_notMem h,mul_zero,Real.exp_zero,add_zero]

private theorem weighted_exp_threshold (n : ℕ) (u t : ℝ) {N : ℕ} (old : Fin (n+1) → UnitSpin N) (z : UnitSpin N) :
    thresholdMembership n u (old,z)*Real.exp (t*thresholdMembership n u (old,z))=
      Real.exp t*thresholdMembership n u (old,z) := by
  unfold thresholdMembership
  by_cases h : unitOverlap z (old (Fin.last n))∈Ici u
  · simp only [indicator_of_mem h,mul_one,one_mul]
  · simp only [indicator_of_notMem h,mul_zero,zero_mul]

theorem threshold_normalizer_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    reweightingNormalizer n (parameterizedGibbsKernel nu v) unitOverlap (thresholdScore n u) t p.1 p.2=
      1-membershipMass nu v n u p+Real.exp t*membershipMass nu v n u p := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  simp only [reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,threshold_score_eq,exp_threshold]
  rw [integral_add (integrable_const 1) ((threshold_integrable (parameterizedGibbsKernel nu v p.1) n u p.2).const_mul _),
    integral_const_mul,integral_const,probReal_univ,one_smul]
  dsimp only [membershipMass]
  ring

theorem threshold_tiltedWeightMean_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    tiltedWeightMean n (parameterizedGibbsKernel nu v) unitOverlap (thresholdScore n u)
      (thresholdMembership n u) t p.1 p.2=indicatorTiltMass t (membershipMass nu v n u p) := by
  rw [tiltedWeightMean,integral_div]
  simp only [threshold_score_eq,weighted_exp_threshold,integral_const_mul]
  rw [threshold_normalizer_eq nu hv]
  rfl

theorem corrected_sum_threshold_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (u : ℝ) (x : Fin K → ℝ) (old : Fin (n+1) → UnitSpin N) :
    (∑ l,correctedScore n unitOverlap (thresholdScore n u)
      (fun j ↦ pairMean nu v (thresholdScore n u j) x) old l)=
      (∑ l : Fin n,(Ici u).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (old (Fin.last n)) (old l.castSucc)))+
          pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) x := by
  have hScore (z : UnitSpin N) : score n unitOverlap (thresholdScore n u) old z=
      (Ici u).indicator (fun _ ↦ (1 : ℝ)) (unitOverlap (old (Fin.last n)) z) := by
    unfold score
    rw [Fin.sum_univ_castSucc]
    simp only [thresholdScore,Fin.snoc_castSucc,Fin.snoc_last,Finset.sum_const_zero,zero_add]
  unfold correctedScore
  simp_rw [hScore]
  rw [Fin.sum_univ_castSucc]
  simp only [thresholdScore,Fin.snoc_castSucc,Fin.snoc_last,sub_zero,pairMean_zero,add_zero,
    sub_self,zero_add]

theorem corrected_sum_threshold_eq_of_below {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (u : ℝ) (x : Fin K → ℝ) (old : Fin (n+1) → UnitSpin N)
    (hBelow : ∀ l : Fin n,unitOverlap (old (Fin.last n)) (old l.castSucc)<u) :
    (∑ l,correctedScore n unitOverlap (thresholdScore n u)
      (fun j ↦ pairMean nu v (thresholdScore n u j) x) old l)=
      pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) x := by
  rw [corrected_sum_threshold_eq]
  have hZ : (∑ l : Fin n,(Ici u).indicator (fun _ ↦ (1 : ℝ))
      (unitOverlap (old (Fin.last n)) (old l.castSucc)))=0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact indicator_of_notMem (not_le_of_gt (hBelow l)) _
  rw [hZ,zero_add]

theorem scoreIntegrand_eq_of_below {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u kappa t : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))
    (hBelow : ∀ l : Fin n,unitOverlap (p.2 (Fin.last n)) (p.2 l.castSucc)<u) :
    SphericalGGBoundedScoreWeights.scoreIntegrand nu v n (thresholdScore n u) Phi
      (fun _ ↦ thresholdMembership n u) (window kappa) t p=
      (Phi p.1.1 p.2*Real.exp (t*pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) p.1.1)/
        (1-membershipMass nu v n u p+Real.exp t*membershipMass nu v n u p)^(n+1))*
          window kappa (indicatorTiltMass t (membershipMass nu v n u p)) := by
  unfold SphericalGGBoundedScoreWeights.scoreIntegrand GGFiniteJointScoreStability.integrand
  rw [corrected_sum_threshold_eq_of_below nu v n u p.1.1 p.2 hBelow,
    threshold_normalizer_eq nu hv,threshold_tiltedWeightMean_eq nu hv]

end
end TensorPCA.NonRSLowerProofs.SphericalGGIndicatorTilt
