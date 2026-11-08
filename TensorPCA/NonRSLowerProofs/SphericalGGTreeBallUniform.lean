-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeBallAverage

/-! The polynomial contribution to a masked Tree fresh-ball row error tends to zero
uniformly over dimension, prior, cutoff, cut vector and mask. The L1 score error is
measured under the amplitude's pair law and remains restricted to the same mask.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeBallUniform
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianGGIndicatorTransfer NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGTreeBallAverage SphericalPolynomialFirstJetClippedBudget
open SphericalPolynomialFirstJetCubeMean SphericalGGThresholdWeights
open FiniteNestedPartition
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coeff_abs_sum_stable (P : Polynomial ℝ) {K : ℕ} (hPK : P.natDegree≤K) :
    (∑q ∈ Finset.range (K+1),|P.coeff q|)=∑q ∈ Finset.range (P.natDegree+1),|P.coeff q| := by
  calc
    _=P.sum (fun _ c ↦ |c|) :=
      (P.sum_over_range' (fun _ ↦ abs_zero) (K+1) (Nat.lt_succ_of_le hPK)).symm
    _=_ := P.sum_over_range (fun _ ↦ abs_zero)

/-- Only the fixed polynomial and desired numerical error choose the strength
threshold. The complete physical model, replica count, Tree, cut and measurable
amplitude restriction occur afterwards. -/
theorem exists_uniform_masked_freshBallResidual_threshold
    (P : Polynomial ℝ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ,1≤V ∧ ∀ {N K depth n : ℕ} (hPK : P.natDegree≤K)
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
      ∀ (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
        (l : Fin depth) (i : Fin (n+1)) (E : Set (Fin K → ℝ)),MeasurableSet E →
        (∀ r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) →
        (∫ x,E.indicator (fun x ↦ |freshBallResidual nu v cuts t l i x|) x ∂positiveCubeLaw K)≤
          eps+2*(∫ x,E.indicator (fun x ↦ pairMean nu v (fun r ↦ |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
            extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K) := by
  let C : ℝ := ∑q ∈ Finset.range (P.natDegree+1),|P.coeff q|
  have hC : 0≤C := Finset.sum_nonneg (fun q _ ↦ abs_nonneg _)
  obtain ⟨V,hV,hMean⟩ := exists_uniform_polynomial_error_mean_threshold P.natDegree
    (div_pos heps (by positivity : 0<C+1))
  refine ⟨V,hV,?_⟩
  intro N K depth n hPK nu hnu v hv cuts t l i E hE hGlobal
  have hvp : 0<v := lt_of_lt_of_le zero_lt_one (hV.trans hv)
  let B : (Fin K → ℝ) → ℝ := fun x ↦ ∑q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q
  have hBI : Integrable B (positiveCubeLaw K) :=
    integrable_finsetSum (Finset.range (K+1)) (fun q _ ↦ (boundedPowerError_integrable nu hvp.le n q).const_mul |P.coeff q|)
  have hBN (x) : 0≤B x :=
    Finset.sum_nonneg (fun q _ ↦ mul_nonneg (abs_nonneg _) (boundedPowerError_nonneg nu v x n q))
  have hMask : (∫ x,E.indicator B x ∂positiveCubeLaw K)≤∫ x,B x ∂positiveCubeLaw K := by
    apply integral_mono (hBI.indicator hE) hBI
    intro x
    by_cases h : x∈E
    · simp only [Set.indicator_of_mem h,le_refl]
    · simpa only [Set.indicator_of_notMem h] using hBN x
  have hFull : (∫ x,B x ∂positiveCubeLaw K)≤eps/(C+1)*C := by
    have H := hMean hPK nu v hv n (lastPolynomial n P)
      (fun j ↦ lastPolynomial_degree n P (le_refl _) j)
    simp only [Fin.sum_univ_castSucc,lastPolynomial,Fin.snoc_castSucc,Fin.snoc_last,
      Polynomial.coeff_zero,abs_zero,zero_mul,Finset.sum_const_zero,zero_add] at H
    rw [coeff_abs_sum_stable P hPK] at H
    exact H
  have hSmall : eps/(C+1)*C≤eps := by
    have hNon : 0≤eps/(C+1) := div_nonneg heps.le (by positivity)
    have hEq : eps/(C+1)*(C+1)=eps := div_mul_cancel₀ eps (by positivity : C+1≠0)
    nlinarith only [hNon,hEq]
  have H := masked_freshBallResidual_mean_le nu hvp cuts t l i E hE P hPK hGlobal
  exact H.trans (add_le_add (hMask.trans (hFull.trans hSmall)) le_rfl)

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeBallUniform
