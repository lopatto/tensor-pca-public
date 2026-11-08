-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetClippedBudget

/-! Replica-count monotonicity and exact zero-polynomial padding of the finite
coefficient-weighted first-jet error.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalPolynomialErrorMonotonicity
open MeasureTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianPerturbationDeviation
open SphericalPolynomialFirstJetBudget SphericalPolynomialFirstJetClippedBudget SphericalFirstJetCubeBudget
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem boundedPowerError_mono_replica {N K : ℕ} (nu : Measure (UnitSpin N)) {v : ℝ}
    (hv : 0<v) (x : Fin K → ℝ) (hxp : ∀ p, 0<x p) {m0 m : ℕ} (hm : m0≤m) (q : ℕ) :
    boundedPowerError nu v x m q≤boundedPowerError nu v x m0 q := by
  by_cases hq : 0<q ∧ q≤K
  · let p : Fin K := ⟨q-1,by omega⟩
    have ha : 0<v^2*(1/4 : ℝ)^(p.val+1) := by positivity
    have hpx := hxp p
    have hn := totalDeviation_nonneg nu (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) (x p)
    have hraw : degreeError nu v x m p≤degreeError nu v x m0 p := by
      unfold degreeError
      apply div_le_div_of_nonneg_left hn (by positivity)
      have hmr : (m0 : ℝ)≤(m : ℝ) := by exact_mod_cast hm
      nlinarith [mul_nonneg (sub_nonneg.mpr hmr) (mul_nonneg (hxp p).le ha.le)]
    simpa only [boundedPowerError,powerError,dif_pos hq] using
      max_le_max (le_refl (0 : ℝ)) (min_le_min_left 2 hraw)
  · simp only [boundedPowerError,powerError,dif_neg hq,le_refl]

theorem polynomialError_mono_replica {N K R : ℕ} (nu : Measure (UnitSpin N)) {v : ℝ}
    (hv : 0<v) (x : Fin K → ℝ) (hxp : ∀ p, 0<x p) {m0 m : ℕ} (hm : m0≤m)
    (P : Fin R → Polynomial ℝ) :
    (∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q)≤
      ∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m0 q :=
  Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun q _ ↦
    mul_le_mul_of_nonneg_left (boundedPowerError_mono_replica nu hv x hxp hm q) (abs_nonneg _)))

theorem polynomialError_snoc_zero {N K R : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m : ℕ) (P : Fin R → Polynomial ℝ) :
    (∑ j : Fin (R+1), ∑ q ∈ Finset.range (K+1), |(Fin.snoc (α := fun _ ↦ Polynomial ℝ) P 0 j).coeff q| *boundedPowerError nu v x m q)=
      ∑ j : Fin R, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,Polynomial.coeff_zero,abs_zero,zero_mul,Finset.sum_const_zero,add_zero]

theorem polynomialError_snoc_successor_le {N K n : ℕ} (nu : Measure (UnitSpin N)) {v : ℝ}
    (hv : 0<v) (x : Fin K → ℝ) (hxp : ∀ p, 0<x p) (P : Fin (n+1) → Polynomial ℝ) :
    (∑ j : Fin (n+2), ∑ q ∈ Finset.range (K+1), |(Fin.snoc (α := fun _ ↦ Polynomial ℝ) P 0 j).coeff q| *boundedPowerError nu v x (n+1) q)≤
      ∑ j : Fin (n+1), ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x n q := by
  rw [polynomialError_snoc_zero]
  exact polynomialError_mono_replica nu hv x hxp (Nat.le_succ n) P

end
end TensorPCA.NonRSLowerProofs.SphericalPolynomialErrorMonotonicity
