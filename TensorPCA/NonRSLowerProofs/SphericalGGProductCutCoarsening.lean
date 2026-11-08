-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGProductCutMasks
public import TensorPCA.NonRSLowerProofs.SphericalGGMaskedThresholdBadMass

/-! Product first-good cells discharge the masked boundary budget. The common positive
gap is chosen before every model, and the single UM error gives a uniform finite-
array coarsening bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGProductCutCoarsening
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open FiniteGGBoundaryBands FiniteGGPrechosenPolynomialFamily FiniteGGParameterScorePartition
open FiniteGGMonotoneBoundaryCuts FiniteGGProductCutMasks SphericalGGMaskedThresholdBadMass
open SphericalGGFiniteArrayUltrametricity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem product_cut_lower_band_budget {N K depth J : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (a b eta : Fin depth → ℝ) (hab : ∀ l,a l<b l)
    (hJ : 0<J) (hBudget : ∀ l,1/(J : ℝ)≤eta l/2)
    (P : Fin depth → Fin J → Polynomial ℝ)
    (hApprox : ∀ l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta l/2)
    (hGlobal : ∀ l j r,|NonRSUpperProofs.GaussianGGIndicatorTransfer.extendTest
      ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    (h : ℝ) (hSub : ∀ l (j : Fin J),Ico (threshold (a l) (b l) J j-h)
      (threshold (a l) (b l) J j)⊆band (a l) (b l) J j) :
    let good := fun l ↦ goodParameter
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      (parameterizedGibbsKernel nu v) unitOverlap (a l) (b l) J (P l) (eta l)
    ∀ x,(∑ index : Fin depth → Fin J,∑ l,(cutCell good index).indicator
      (fun x ↦ pairMean nu v ((Ico (threshold (a l) (b l) J (index l)-h)
        (threshold (a l) (b l) J (index l))).indicator (fun _ ↦ (1 : ℝ))) x) x)≤∑ l,eta l/2 := by
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := parameterizedGibbsKernel (K := K) nu v
  let good := fun l ↦ goodParameter d G unitOverlap (a l) (b l) J (P l) (eta l)
  obtain ⟨_,_,_,_,_,hBand⟩ := product_parameter_partition d G (unitOverlap_measurable N)
    unitOverlap_mem_Icc a b eta hab hJ hBudget P hApprox hGlobal
  intro x
  change (∑ index : Fin depth → Fin J,∑ l,(cutCell good index).indicator
    (fun x ↦ pairMean nu v ((Ico (threshold (a l) (b l) J (index l)-h)
      (threshold (a l) (b l) J (index l))).indicator (fun _ ↦ (1 : ℝ))) x) x)≤∑ l,eta l/2
  have hLower (l : Fin depth) (j : Fin J) :
      pairMean nu v ((Ico (threshold (a l) (b l) J j-h) (threshold (a l) (b l) J j)).indicator
        (fun _ ↦ (1 : ℝ))) x≤
      ((((G.sectR x)×ₖ(G.sectR x))∘ₘd).map
        (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)).real (band (a l) (b l) J j) := by
    dsimp only [pairMean]
    rw [integral_indicator_const (1 : ℝ) measurableSet_Ico,smul_eq_mul,mul_one]
    exact measureReal_mono (hSub l j)
  calc
    _ ≤ ∑ index : Fin depth → Fin J,(cutCell good index).indicator
        (fun x ↦ ∑ l,((((G.sectR x)×ₖ(G.sectR x))∘ₘd).map
          (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)).real
            (band (a l) (b l) J (index l))) x := by
      apply Finset.sum_le_sum
      intro index _
      by_cases hx : x∈cutCell good index
      · simp only [indicator_of_mem hx]
        exact Finset.sum_le_sum (fun l _ ↦ hLower l (index l))
      · simp only [indicator_of_notMem hx,Finset.sum_const_zero,le_refl]
    _ ≤ _ := hBand x

theorem exists_uniform_product_cut_threshold (n depth J : ℕ)
    (a b eta : Fin depth → ℝ) (hab : ∀ l,a l<b l) (hb : ∀ l,b l≤1)
    (hJ : 0<J) (hBudget : ∀ l,1/(J : ℝ)≤eta l/2)
    (P : Fin depth → Fin J → Polynomial ℝ)
    (hApprox : ∀ l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta l/2)
    (hGlobal : ∀ l j r,|NonRSUpperProofs.GaussianGGIndicatorTransfer.extendTest
      ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    {delta : ℝ} (hdelta : 0<delta) :
    ∃ h : ℝ,0<h ∧ ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        let good := fun l ↦ goodParameter
          (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          (parameterizedGibbsKernel nu v) unitOverlap (a l) (b l) J (P l) (eta l)
        (jointLaw (K := K) nu v n).real {q | ∃ index : Fin depth → Fin J,
          q.1.1∈cutCell good index ∧ ¬∀ l,Equivalence (fun i j ↦
            threshold (a l) (b l) J (index l)≤unitOverlap (q.2 i) (q.2 j))}<
          delta+((n+1 : ℕ) : ℝ)^2*∑ l,eta l/2 := by
  obtain ⟨h,hh,hSub⟩ := exists_common_boundary_width a b hab J
  obtain ⟨Q,hQ⟩ := exists_uniform_finite_array_ultrametricity_threshold n hh hdelta
  refine ⟨h,hh,Q,?_⟩
  intro K hK
  obtain ⟨V,hV,hUM⟩ := hQ K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  dsimp only
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hv0
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := parameterizedGibbsKernel (K := K) nu v
  let good := fun l ↦ goodParameter d G unitOverlap (a l) (b l) J (P l) (eta l)
  let cuts : (Fin depth → Fin J) → Fin depth → ℝ :=
    fun index l ↦ threshold (a l) (b l) J (index l)
  change (jointLaw (K := K) nu v n).real {q | ∃ index : Fin depth → Fin J,
    q.1.1∈cutCell good index ∧ ¬∀ l,Equivalence
      (fun i j ↦ cuts index l≤unitOverlap (q.2 i) (q.2 j))}<
    delta+((n+1 : ℕ) : ℝ)^2*∑ l,eta l/2
  have hGood (l : Fin depth) (j : Fin J) : MeasurableSet (good l j) :=
    goodParameter_measurable d G (unitOverlap_measurable N) (a l) (b l) J (P l) (eta l) (hGlobal l) j
  have hMasks (index : Fin depth → Fin J) : MeasurableSet (cutCell good index) :=
    cutCell_measurable good hGood index
  have hCuts (index : Fin depth → Fin J) (l : Fin depth) :
      threshold (a l) (b l) J (index l)≤1 :=
    (threshold_vector_lt_one a b hab hb index l).le
  have hBandBudget : ∀ x,(∑ index : Fin depth → Fin J,∑ l,(cutCell good index).indicator
      (fun x ↦ pairMean nu v ((Ico (cuts index l-h) (cuts index l)).indicator
        (fun _ ↦ (1 : ℝ))) x) x)≤∑ l,eta l/2 := by
    convert product_cut_lower_band_budget nu hv0 a b eta hab hJ hBudget P hApprox hGlobal h hSub using 1 <;> rfl
  have hMain := finite_masked_threshold_mass_le_of_budget (A := Fin depth → Fin J)
    (N := N) (K := K) (depth := depth) nu hv0 n cuts hCuts
    (cutCell good) hMasks hh hBandBudget
  exact hMain.trans_lt (add_lt_add_of_lt_of_le (hUM nu v hv) (le_refl _))

end
end TensorPCA.NonRSLowerProofs.SphericalGGProductCutCoarsening
