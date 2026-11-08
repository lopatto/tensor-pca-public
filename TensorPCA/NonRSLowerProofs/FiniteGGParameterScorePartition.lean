-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGFirstGoodPartition
public import TensorPCA.NonRSLowerProofs.FiniteGGPrechosenPolynomialFamily
public import TensorPCA.NonRSLowerProofs.GGFiniteParameterizedJets

/-! First-good restrictions for a fixed finite score family under parameter-dependent,
disorder-averaged pair laws. The partition parameter is amplitude, while Gaussian
disorder is averaged independently.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGParameterScorePartition
open MeasureTheory ProbabilityTheory Set
open FiniteGGFirstGoodPartition FiniteGGPrechosenPolynomialFamily FiniteGGBoundaryBands
open GGFiniteParameterizedJets NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Omega V : Type*} [MeasurableSpace X] [MeasurableSpace Omega] [MeasurableSpace V]

def ownScoreL1 (d : Measure Omega) (K : Kernel (X×Omega) V) (R : V→V→ℝ)
    (threshold : ℝ) (P : Polynomial ℝ) (x : X) : ℝ :=
  ∫r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r-
      (Ici threshold).indicator (fun _ ↦ (1 : ℝ)) r|
    ∂((((K.sectR x)×ₖ(K.sectR x))∘ₘd).map (fun p : V×V ↦ R p.1 p.2))

def goodParameter (d : Measure Omega) (K : Kernel (X×Omega) V) (R : V→V→ℝ)
    (a b : ℝ) (J : ℕ) (P : Fin J→Polynomial ℝ) (eta : ℝ) (j : Fin J) : Set X :=
  {x | (((((K.sectR x)×ₖ(K.sectR x))∘ₘd).map (fun p : V×V ↦ R p.1 p.2)).real (band a b J j))≤eta/2 ∧
    ownScoreL1 d K R (threshold a b J j) (P j) x≤eta}

private theorem indicator_one_abs_le (S : Set ℝ) (r : ℝ) : |S.indicator (fun _ ↦ (1 : ℝ)) r|≤1 := by
  by_cases h : r∈S
  · rw [indicator_of_mem h]; norm_num
  · rw [indicator_of_notMem h]; norm_num

 theorem goodParameter_measurable (d : Measure Omega) [IsProbabilityMeasure d]
    (K : Kernel (X×Omega) V) [IsMarkovKernel K] {R : V→V→ℝ}
    (hR : Measurable (fun p : V×V ↦ R p.1 p.2)) (a b : ℝ) (J : ℕ) (P : Fin J→Polynomial ℝ) (eta : ℝ)
    (hGlobal : ∀j r,|extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) (j : Fin J) :
    MeasurableSet (goodParameter d K R a b J P eta j) := by
  have hBandMeas : Measurable ((band a b J j).indicator (fun _ ↦ (1 : ℝ))) :=
    measurable_const.indicator (show MeasurableSet (band a b J j) from measurableSet_Icc)
  have hMass := conditional_pair_mean_measurable d K hR hBandMeas (indicator_one_abs_le (band a b J j))
  simp only [integral_indicator_const (1 : ℝ) (show MeasurableSet (band a b J j) from measurableSet_Icc),smul_eq_mul,mul_one] at hMass
  have hPhiMeas : Measurable (extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1))) := (extendTest_continuous _).measurable
  have hIndMeas : Measurable ((Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator measurableSet_Ici
  have hErrorMeas : Measurable (fun r ↦ |extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r-
      (Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r|) :=
    (continuous_abs.measurable : Measurable (abs : ℝ→ℝ)).comp (hPhiMeas.sub hIndMeas)
  have hErrorBound (r : ℝ) : abs (abs (extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r-
      (Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r))≤3 := by
    rw [abs_abs]
    exact (abs_sub _ _).trans ((add_le_add (hGlobal j r) (indicator_one_abs_le (Ici (threshold a b J j)) r)).trans_eq (by norm_num))
  have hError := conditional_pair_mean_measurable d K hR hErrorMeas hErrorBound
  exact (measurableSet_le hMass measurable_const).inter (measurableSet_le hError measurable_const)

 theorem exists_goodParameter (d : Measure Omega) [IsProbabilityMeasure d]
    (K : Kernel (X×Omega) V) [IsMarkovKernel K] {R : V→V→ℝ}
    (hR : Measurable (fun p : V×V ↦ R p.1 p.2)) (hUnit : ∀u v,R u v∈Icc (-1 : ℝ) 1)
    {a b eta : ℝ} (hab : a<b) (J : ℕ) (hJ : 0<J) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin J→Polynomial ℝ)
    (hApprox : ∀j,‖(P j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤eta/2)
    (x : X) : ∃j,x∈goodParameter d K R a b J P eta j := by
  let rho := ((((K.sectR x)×ₖ(K.sectR x))∘ₘd).map (fun p : V×V ↦ R p.1 p.2))
  have hSupport : ∀ᵐr ∂rho,r∈Icc (-1 : ℝ) 1 := by
    apply (ae_map_iff hR.aemeasurable measurableSet_Icc).mpr
    exact .of_forall (fun p ↦ hUnit p.1 p.2)
  obtain ⟨j,hj⟩ := exists_small_band hab hJ rho
  have hSmall := hj.trans hBudget
  have hL1 := projected_polynomial_indicator_L1 hab j (P j) (hApprox j) rho hSupport
  refine ⟨j,hSmall,?_⟩
  change ownScoreL1 d K R (threshold a b J j) (P j) x≤eta
  exact hL1.trans (by linarith only [hSmall])

 theorem fixed_family_parameter_partition (d : Measure Omega) [IsProbabilityMeasure d]
    (K : Kernel (X×Omega) V) [IsMarkovKernel K] {R : V→V→ℝ}
    (hR : Measurable (fun p : V×V ↦ R p.1 p.2)) (hUnit : ∀u v,R u v∈Icc (-1 : ℝ) 1)
    {a b eta : ℝ} (hab : a<b) (J : ℕ) (hJ : 0<J) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin J→Polynomial ℝ)
    (hApprox : ∀j,‖(P j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤eta/2)
    (hGlobal : ∀j r,|extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    (∀j,MeasurableSet (firstGood (goodParameter d K R a b J P eta) j)) ∧
    (∀i j : Fin J,i≠j→Disjoint (firstGood (goodParameter d K R a b J P eta) i)
      (firstGood (goodParameter d K R a b J P eta) j)) ∧
    (⋃j,firstGood (goodParameter d K R a b J P eta) j)=univ ∧
    (∀j x,x∈firstGood (goodParameter d K R a b J P eta) j→x∈goodParameter d K R a b J P eta j) ∧
    ∀x,(∑j : Fin J,(firstGood (goodParameter d K R a b J P eta) j).indicator
      (ownScoreL1 d K R (threshold a b J j) (P j)) x)≤eta := by
  have hExists := exists_goodParameter d K hR hUnit hab J hJ hBudget P hApprox
  refine ⟨fun j ↦ firstGood_measurable _ (goodParameter_measurable d K hR a b J P eta hGlobal) j,
    (fun i j hij ↦ firstGood_disjoint _ hij),firstGood_cover _ hExists,?_,?_⟩
  · exact fun j _ hx ↦ firstGood_subset _ j hx
  · intro x
    exact sum_firstGood_restrictions_le _ hExists _ (fun j x hx ↦ hx.2) x

end
end TensorPCA.NonRSLowerProofs.FiniteGGParameterScorePartition
