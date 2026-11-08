-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteScoreInvariance
public import TensorPCA.NonRSLowerProofs.FiniteGGParameterScorePartition
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowLipschitz

/-! Last-anchor indicator scores, a finite prechosen polynomial family, and its
amplitude-only first-good restrictions.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGThresholdWeights
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGZeroJets SphericalGGWeightObservable
open SphericalGGBoundedScoreWeights SphericalGGMaskedScoreStability SphericalGGFiniteScoreInvariance
open FiniteGGBoundaryBands FiniteGGParameterScorePartition FiniteGGFirstGoodPartition
open FiniteGGWindowScalar NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

def thresholdScore (n : ℕ) (u : ℝ) : Fin (n+1) → ℝ → ℝ :=
  Fin.snoc (fun _ : Fin n ↦ fun _ : ℝ ↦ 0) ((Ici u).indicator (fun _ ↦ (1 : ℝ)))

def lastPolynomial (n : ℕ) (P : Polynomial ℝ) : Fin (n+1) → Polynomial ℝ :=
  Fin.snoc (fun _ : Fin n ↦ 0) P

def lastBounds (n : ℕ) : Fin (n+1) → ℝ := Fin.snoc (fun _ : Fin n ↦ 0) 2

def thresholdMembership {N : ℕ} (n : ℕ) (u : ℝ) (p : (Fin (n+1) → UnitSpin N)×UnitSpin N) : ℝ :=
  (Ici u).indicator (fun _ ↦ (1 : ℝ)) (unitOverlap p.2 (p.1 (Fin.last n)))

def thresholdMasks {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) (i : Fin J) : Set (Fin K → ℝ) :=
  firstGood (goodParameter (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    (parameterizedGibbsKernel nu v) unitOverlap a b J P eta) i

theorem thresholdScore_measurable (n : ℕ) (u : ℝ) (j : Fin (n+1)) : Measurable (thresholdScore n u j) := by
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simpa only [thresholdScore,Fin.snoc_last] using (measurable_const.indicator measurableSet_Ici :
      Measurable ((Ici u).indicator (fun _ ↦ (1 : ℝ))))
  · simpa only [thresholdScore,Fin.snoc_castSucc] using (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ)))

theorem thresholdScore_bound (n : ℕ) (u : ℝ) (j : Fin (n+1)) (r : ℝ) : |thresholdScore n u j r|≤lastBounds n j := by
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simp only [thresholdScore,lastBounds,Fin.snoc_last]
    by_cases hr : r∈Ici u
    · rw [indicator_of_mem hr]; norm_num
    · rw [indicator_of_notMem hr]; norm_num
  · simp only [thresholdScore,lastBounds,Fin.snoc_castSucc,abs_zero,le_refl]

theorem lastPolynomial_degree (n : ℕ) (P : Polynomial ℝ) {K : ℕ} (hP : P.natDegree≤K) (j : Fin (n+1)) :
    (lastPolynomial n P j).natDegree≤K := by
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simpa only [lastPolynomial,Fin.snoc_last] using hP
  · simp only [lastPolynomial,Fin.snoc_castSucc,Polynomial.natDegree_zero]; exact Nat.zero_le _

theorem lastPolynomial_bound (n : ℕ) (P : Polynomial ℝ)
    (hP : ∀ r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) (j : Fin (n+1)) (r : ℝ) :
    |tests (lastPolynomial n P) j r|≤lastBounds n j := by
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simpa only [tests,lastPolynomial,lastBounds,Fin.snoc_last] using hP r
  · simp [tests,lastPolynomial,lastBounds,extendTest]

theorem sum_lastBounds (n : ℕ) : (∑ j, lastBounds n j)=2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [lastBounds,Fin.snoc_castSucc,Fin.snoc_last,Finset.sum_const_zero,zero_add]

theorem thresholdMembership_measurable (N n : ℕ) (u : ℝ) : Measurable (thresholdMembership (N := N) n u) := by
  exact (measurable_const.indicator measurableSet_Ici).comp
    ((SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp
      (measurable_snd.prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_fst)))

theorem thresholdMembership_mem {N : ℕ} (n : ℕ) (u : ℝ) (p : (Fin (n+1) → UnitSpin N)×UnitSpin N) :
    thresholdMembership n u p∈Icc (0 : ℝ) 1 := by
  unfold thresholdMembership
  by_cases h : unitOverlap p.2 (p.1 (Fin.last n))∈Ici u
  · simp only [indicator_of_mem h]; exact ⟨zero_le_one,le_refl _⟩
  · simp only [indicator_of_notMem h]; exact ⟨le_refl _,zero_le_one⟩

theorem last_score_error_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (u : ℝ) (P : Polynomial ℝ) (x : Fin K → ℝ) :
    (∑ j, pairMean nu v (fun r ↦ |thresholdScore n u j r-tests (lastPolynomial n P) j r|) x)=
      ownScoreL1 (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        (parameterizedGibbsKernel nu v) unitOverlap u P x := by
  rw [Fin.sum_univ_castSucc]
  simp only [thresholdScore,lastPolynomial,tests,Fin.snoc_castSucc,Fin.snoc_last]
  have hZero : pairMean nu v (fun r ↦ |0-extendTest ((0 : Polynomial ℝ).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x=0 := by
    simp [extendTest,pairMean]
  simp only [hZero,Finset.sum_const_zero,zero_add]
  simp only [pairMean,ownScoreL1,abs_sub_comm]

theorem thresholdMasks_properties {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {a b eta : ℝ} (hab : a<b) (J : ℕ) (hJ : 0<J)
    (hBudget : 1/(J : ℝ)≤eta/2) (P : Fin J → Polynomial ℝ)
    (hApprox : ∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    (∀ i,MeasurableSet (thresholdMasks (K := K) nu v a b eta J P i)) ∧
    (∀ i j : Fin J,i≠j→Disjoint (thresholdMasks (K := K) nu v a b eta J P i)
      (thresholdMasks (K := K) nu v a b eta J P j)) ∧
    (⋃ i,thresholdMasks (K := K) nu v a b eta J P i)=univ ∧
    ∀ x : Fin K → ℝ,(∑ i, (thresholdMasks nu v a b eta J P i).indicator
      (fun x ↦ ∑ j, pairMean nu v (fun r ↦ |thresholdScore n (threshold a b J i) j r-
        tests (lastPolynomial n (P i)) j r|) x) x)≤eta := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have H := fixed_family_parameter_partition
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) (parameterizedGibbsKernel nu v)
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N)
    SphericalFirstJetPowerBudget.unitOverlap_mem_Icc hab J hJ hBudget P hApprox hGlobal
  refine ⟨H.1,H.2.1,H.2.2.1,?_⟩
  intro x
  simpa only [last_score_error_eq,thresholdMasks] using H.2.2.2.2 x

end
end TensorPCA.NonRSLowerProofs.SphericalGGThresholdWeights
