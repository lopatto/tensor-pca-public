-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGLastSpinCandidate
public import TensorPCA.NonRSLowerProofs.FiniteGGMaskedCandidateGraphs
public import TensorPCA.NonRSLowerProofs.SphericalGGRootWindowBounds

/-! One finite masked candidate graph for all prechosen thresholds. The first-good
amplitude restrictions are disjoint before any integration.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidate
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGThresholdWeights SphericalGGLastSpinCandidate SphericalGGIndicatorTilt
open SphericalGGBoundedScoreWeights SphericalGGMaskedScoreStability SphericalGGRootWindowBounds
open FiniteGGBoundaryBands FiniteGGFirstGoodPartition FiniteGGParameterScorePartition
open FiniteGGMaskedCandidateGraphs FiniteGGConditionalLowMass
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

def prefixMasks {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) (i : Fin J) :
    Set (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :=
  {p | p.1.1∈thresholdMasks nu v a b eta J P i}

def selectedPairSet {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) :
    Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×(UnitSpin N×UnitSpin N)) :=
  maskedUnion (prefixMasks nu v n a b eta J P) (fun i ↦ thresholdPairSet n (threshold a b J i))

theorem prefixMasks_pairwise {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) :
    Pairwise (fun i j ↦ Disjoint (prefixMasks (K := K) nu v n a b eta J P i)
      (prefixMasks nu v n a b eta J P j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  exact (Set.disjoint_left.mp (firstGood_disjoint _ hij)) hi hj

theorem prefixMasks_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) (i : Fin J) :
    MeasurableSet (prefixMasks (K := K) nu v n a b eta J P i) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have H := goodParameter_measurable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) (parameterizedGibbsKernel nu v)
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) a b J P eta hGlobal
  exact (firstGood_measurable _ H i).preimage measurable_fst.fst

theorem selectedPairSet_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    MeasurableSet (selectedPairSet (K := K) nu v n a b eta J P) :=
  maskedUnion_measurable (prefixMasks nu v n a b eta J P)
    (fun i ↦ thresholdPairSet n (threshold a b J i))
    (prefixMasks_measurable nu hv n a b eta J P hGlobal)
    (fun i ↦ thresholdPairSet_measurable N K n (threshold a b J i))

theorem candidateMass_selected_on_cell {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) (i : Fin J)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))
    (hp : p∈prefixMasks nu v n a b eta J P i) (z : UnitSpin N) :
    candidateMass (lastKernel nu v n) (selectedPairSet nu v n a b eta J P) (p,z)=
      membershipMass nu v (n+1) (threshold a b J i) (appendLast n (p,z)) := by
  have H := candidateMass_maskedUnion_on_cell (lastKernel nu v n)
    (prefixMasks nu v n a b eta J P) (fun i ↦ thresholdPairSet n (threshold a b J i))
    (prefixMasks_pairwise nu v n a b eta J P) hp z
  exact H.trans (candidateMass_eq_membershipMass nu hv n (threshold a b J i) (p,z))

theorem sum_masked_scoreIntegrands_eq_on_cell {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) (i : Fin J) (kappa t : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N))
    (hi : p.1.1∈thresholdMasks nu v a b eta J P i) :
    (∑ j,scoreIntegrand nu v (n+1) (thresholdScore (n+1) (threshold a b J j))
      (maskedPhi (thresholdMasks nu v a b eta J P j) Phi)
      (fun _ ↦ thresholdMembership (n+1) (threshold a b J j)) (FiniteGGWindowScalar.window kappa) t p)=
      scoreIntegrand nu v (n+1) (thresholdScore (n+1) (threshold a b J i)) Phi
        (fun _ ↦ thresholdMembership (n+1) (threshold a b J i)) (FiniteGGWindowScalar.window kappa) t p := by
  have hNot (j : Fin J) (hji : j≠i) : p.1.1∉thresholdMasks nu v a b eta J P j := by
    intro hj
    exact (Set.disjoint_left.mp (firstGood_disjoint _ hji)) hj hi
  calc
    _ = scoreIntegrand nu v (n+1) (thresholdScore (n+1) (threshold a b J i))
        (maskedPhi (thresholdMasks nu v a b eta J P i) Phi)
        (fun _ ↦ thresholdMembership (n+1) (threshold a b J i)) (FiniteGGWindowScalar.window kappa) t p := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        apply scoreIntegrand_zero_of_zero
        simp only [maskedPhi,if_neg (hNot j hji)]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
    _ = _ := by simp only [scoreIntegrand,GGFiniteJointScoreStability.integrand,maskedPhi,if_pos hi]

end
end TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidate
