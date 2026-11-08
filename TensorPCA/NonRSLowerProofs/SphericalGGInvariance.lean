-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGZeroJets

/-! Finite-polynomial GG reweighting invariance in amplitude L1. Dimensions and fixed
spin priors may vary along the sequence, and the old test may depend on both the
sequence index and the full amplitude vector. Each amplitude keeps its own Gaussian-
disorder pair means.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGInvariance
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGZeroJets SphericalPolynomialFirstJetCubeMean
open GGFiniteJetL1TaylorPropagation
open scoped BigOperators Topology
noncomputable section

theorem polynomialError_mean_tendsto_zero (D : ℕ → ℕ) (K n : ℕ)
    (nu : (i : ℕ) → Measure (UnitSpin (D i))) [∀ i, IsProbabilityMeasure (nu i)]
    (v : ℕ → ℝ) (hv : Tendsto v atTop atTop)
    (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K) :
    Tendsto (fun i ↦ ∫ x : Fin K → ℝ, polynomialError (nu i) (v i) P x ∂positiveCubeLaw K)
      atTop (𝓝 0) := by
  let S : ℝ := ∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q|
  have hS : 0≤S := Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun q _ ↦ abs_nonneg _))
  rw [Metric.tendsto_nhds]
  intro eps heps
  let delta := eps/(S+1)
  have hd : 0<delta := div_pos heps (by linarith)
  obtain ⟨V,hV1,hV⟩ := exists_uniform_polynomial_error_mean_threshold K hd
  filter_upwards [(tendsto_atTop.1 hv) V] with i hi
  have H := hV (N := D i) (K := K) le_rfl (nu i) (v i) hi n P hPK
  change (∫ x : Fin K → ℝ, polynomialError (nu i) (v i) P x ∂positiveCubeLaw K)≤delta*S at H
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x ↦ polynomialError_nonneg (nu i) (v i) P x))]
  apply H.trans_lt
  dsimp only [delta]
  rw [div_mul_eq_mul_div,div_lt_iff₀ (by linarith : (0 : ℝ)<S+1)]
  nlinarith

theorem positive_zero_jets_l1_tendsto_zero (D : ℕ → ℕ) (K n : ℕ)
    (nu : (i : ℕ) → Measure (UnitSpin (D i))) [∀ i, IsProbabilityMeasure (nu i)]
    (v : ℕ → ℝ) (hv : Tendsto v atTop atTop) (hvpos : ∀ i, 0<v i)
    (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    (Phi : (i : ℕ) → (Fin K → ℝ) → (Fin (n+1) → UnitSpin (D i)) → ℝ)
    (hPhi : ∀ i, Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin (D i)) ↦ Phi i p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ i x old, |Phi i x old|≤C) (k : ℕ) :
    Tendsto (fun i ↦ ∫ x : Fin K → ℝ,
      |polynomialJet (nu i) (v i) (k+1) n P (Phi i) x 0| ∂positiveCubeLaw K) atTop (𝓝 0) := by
  have H := (polynomialError_mean_tendsto_zero D K n nu v hv P hPK).const_mul
    (C*(2*(∑ j, testBounds P j))^k*((n+1).ascFactorial (k+1) : ℝ))
  simp only [mul_zero] at H
  exact squeeze_zero
    (fun i ↦ integral_nonneg (fun x ↦ abs_nonneg _))
    (fun i ↦ polynomialJet_zero_l1_le (nu i) (hvpos i) k n P hPK (hPhi i) hC (hp i)) H

/-- Fixed-cutoff, fixed-polynomial reweighting invariance. The old observable is an
arbitrary uniformly bounded measurable family.
-/
theorem polynomial_invariance_l1 (D : ℕ → ℕ) (K n : ℕ)
    (nu : (i : ℕ) → Measure (UnitSpin (D i))) [∀ i, IsProbabilityMeasure (nu i)]
    (v : ℕ → ℝ) (hv : Tendsto v atTop atTop) (hvpos : ∀ i, 0<v i)
    (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    (Phi : (i : ℕ) → (Fin K → ℝ) → (Fin (n+1) → UnitSpin (D i)) → ℝ)
    (hPhi : ∀ i, Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin (D i)) ↦ Phi i p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ i x old, |Phi i x old|≤C) (t : ℝ) :
    Tendsto (fun i ↦ ∫ x : Fin K → ℝ,
      |polynomialJet (nu i) (v i) 0 n P (Phi i) x t-
        polynomialJet (nu i) (v i) 0 n P (Phi i) x 0| ∂positiveCubeLaw K) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun i ↦ ∫ x : Fin K → ℝ,
        |polynomialJet (nu i) (v i) (k+1) n P (Phi i) x t| ∂positiveCubeLaw K) atTop (𝓝 0) := by
  let J : (i : ℕ) → (Fin K → ℝ) → ℕ → ℝ → ℝ := fun i x k y ↦
    polynomialJet (nu i) (v i) k n P (Phi i) x y
  have hPhis (i : ℕ) (x : Fin K → ℝ) : Measurable (Phi i x) := by
    convert (hPhi i).comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hJ : ∀ i x k y, HasDerivAt (J i x k) (J i x (k+1) y) y := by
    intro i x k y
    exact jet_hasDerivAt (nu i) (hvpos i).le k n (tests_measurable P) (testBounds P) (tests_bound P)
      (hPhis i) hC (hp i) x y
  have hM : ∀ i k y, Measurable (fun x ↦ J i x k y) := by
    intro i k y
    exact polynomialJet_measurable (nu i) (hvpos i).le k n P (hPhi i) y
  let B := ∑ j, testBounds P j
  let C0 := C*Real.exp (2*((n : ℝ)+1)*|t| *B)
  let A := 2*B
  have hB : 0≤B := Finset.sum_nonneg (fun j _ ↦ norm_nonneg _)
  have hC0 : 0≤C0 := mul_nonneg hC (Real.exp_nonneg _)
  have hA : 0≤A := mul_nonneg (by norm_num) hB
  have hb : ∀ i x k y, y ∈ uIcc 0 t → |J i x k y|≤C0*A^k*((n+1).ascFactorial k : ℝ) := by
    intro i x k y hy
    have hyabs : |y|≤|t| := abs_le.mpr ((uIcc_subset_Icc
      (show (0 : ℝ) ∈ Icc (-|t|) |t| from ⟨neg_nonpos.mpr (abs_nonneg _),abs_nonneg _⟩)
      (show t ∈ Icc (-|t|) |t| from ⟨neg_abs_le t,le_abs_self t⟩)) hy)
    exact jet_abs_le (nu i) (hvpos i).le k n (tests_measurable P) (testBounds P) (tests_bound P)
      (hPhis i) hC (hp i) x |t| y hyabs
  have hzero : ∀ k, Tendsto (fun i ↦ ∫ x, |J i x (k+1) 0| ∂positiveCubeLaw K) atTop (𝓝 0) :=
    positive_zero_jets_l1_tendsto_zero D K n nu v hv hvpos P hPK Phi hPhi hC hp
  exact positive_jets_imply_l1_value_invariance (fun _ : ℕ ↦ positiveCubeLaw K) J hJ hM n hC0 hA hb hzero

end
end TensorPCA.NonRSLowerProofs.SphericalGGInvariance
