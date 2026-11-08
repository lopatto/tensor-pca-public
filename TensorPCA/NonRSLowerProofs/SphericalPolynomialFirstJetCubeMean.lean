-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetClippedBudget

/-! Cube means of the finite polynomial error in the pointwise first-jet bound. Jet
measurability and Taylor integration are proved separately from this bounded,
integrable estimate.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetCubeMean
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalPolynomialFirstJetClippedBudget SphericalFirstJetCubeBudget
open SphericalFirstJetLowDegreeBudget SphericalPolynomialFirstJetBudget
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem polynomialError_integrable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (m : ℕ) (P : Fin (m+1) → Polynomial ℝ) :
    Integrable (fun x : Fin K → ℝ ↦
      ∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q)
      (positiveCubeLaw K) :=
  integrable_finsetSum Finset.univ (fun j _ ↦ integrable_finsetSum (Finset.range (K+1))
    (fun q _ ↦ (boundedPowerError_integrable nu hv m q).const_mul |(P j).coeff q|))

/-- Only the tested degree bound Q enters the threshold. The total model
cutoff K, dimension, fixed prior, replica count and finite coefficient list
are all chosen after it. The coefficients scale the displayed error exactly. -/
theorem exists_uniform_polynomial_error_mean_threshold (Q : ℕ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N K : ℕ} (hQK : Q≤K)
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ), V≤v →
      ∀ (m : ℕ) (P : Fin (m+1) → Polynomial ℝ), (∀ j, (P j).natDegree≤Q) →
        (∫ x, (∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q)
          ∂positiveCubeLaw K)≤eps*(∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q|) := by
  obtain ⟨V,hV1,hV⟩ := exists_uniform_lowDegreeError_threshold Q heps
  refine ⟨V,hV1,?_⟩
  intro N K hQK nu _ v hvV m P hPQ
  have hv : 0<v := lt_of_lt_of_le zero_lt_one (hV1.trans hvV)
  have hmean (q : ℕ) (hq : q∈Finset.range (K+1)) (hqQ : q≤Q) :
      (∫ x, boundedPowerError nu v x m q ∂positiveCubeLaw K)≤eps := by
    by_cases hq0 : q=0
    · subst q
      simpa [boundedPowerError,powerError] using heps.le
    · have hqK : q≤K := by have h := Finset.mem_range.mp hq; omega
      let p : Fin K := ⟨q-1,by omega⟩
      have hpq : p.val+1=q := by dsimp only [p]; omega
      rw [← hpq]
      simp_rw [boundedPowerError_eq_degreeError]
      exact hV nu v hvV p (by rw [hpq]; exact hqQ) m
  have heq : (∫ x, (∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q)
      ∂positiveCubeLaw K)=
      ∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *(∫ x, boundedPowerError nu v x m q ∂positiveCubeLaw K) := by
    rw [integral_finsetSum Finset.univ (fun j _ ↦ integrable_finsetSum (Finset.range (K+1))
      (fun q _ ↦ (boundedPowerError_integrable nu hv.le m q).const_mul |(P j).coeff q|))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum (Finset.range (K+1))
      (fun q _ ↦ (boundedPowerError_integrable nu hv.le m q).const_mul |(P j).coeff q|)]
    apply Finset.sum_congr rfl
    intro q hq
    exact integral_const_mul _ _
  rw [heq]
  calc
    _ ≤ ∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *eps := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro q hq
      by_cases hqQ : q≤Q
      · exact mul_le_mul_of_nonneg_left (hmean q hq hqQ) (abs_nonneg _)
      · have hz : (P j).coeff q=0 := Polynomial.coeff_eq_zero_of_natDegree_lt
          ((hPQ j).trans_lt (Nat.lt_of_not_ge hqQ))
        simp only [hz,abs_zero,zero_mul,le_refl]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

end
end TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetCubeMean
