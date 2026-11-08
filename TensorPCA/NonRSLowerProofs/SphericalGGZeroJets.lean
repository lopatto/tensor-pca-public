-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGJetFamily
public import TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetCubeMean
public import TensorPCA.NonRSLowerProofs.SphericalPolynomialErrorMonotonicity

/-! Polynomial zero-jet control with amplitude-conditional means, using the full-field
cube deviation budgets.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGZeroJets
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianGGPolynomialTests
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet GGFiniteReweightingJets
open SphericalGGJetFamily SphericalPolynomialFirstJetClippedBudget SphericalPolynomialFirstJetCubeMean
open scoped BigOperators
noncomputable section

def tests {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) : Fin (n+1) → ℝ → ℝ :=
  fun j ↦ extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1))

def testBounds {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) : Fin (n+1) → ℝ :=
  fun j ↦ ‖(P j).toContinuousMapOn (Icc (-1 : ℝ) 1)‖

def polynomialJet {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (k n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ) (x : Fin K → ℝ) (t : ℝ) : ℝ :=
  jet nu v k n (tests P) Phi x t

def polynomialError {N K n : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (P : Fin (n+1) → Polynomial ℝ) (x : Fin K → ℝ) : ℝ :=
  ∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x n q

theorem tests_measurable {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) :
    ∀ j, Measurable (tests P j) := fun j ↦ (extendTest_continuous _).measurable

theorem tests_bound {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) :
    ∀ j r, |tests P j r|≤testBounds P j := by
  intro j r
  simpa only [tests,testBounds,Real.norm_eq_abs] using extendTest_norm_le ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r

theorem tests_snoc_zero {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) :
    tests (Fin.snoc P 0)=Fin.snoc (tests P) (fun _ ↦ 0) := by
  funext j r
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simp [tests,extendTest]
  · simp only [tests,Fin.snoc_castSucc]

theorem testBounds_snoc_zero {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) :
    testBounds (Fin.snoc P 0)=Fin.snoc (testBounds P) 0 := by
  have hz : (0 : Polynomial ℝ).toContinuousMapOn (Icc (-1 : ℝ) 1)=0 := by ext r; simp
  funext j
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simp only [testBounds,Fin.snoc_last,hz,norm_zero]
  · simp only [testBounds,Fin.snoc_castSucc]

theorem sum_testBounds_snoc_zero {n : ℕ} (P : Fin (n+1) → Polynomial ℝ) :
    (∑ j, testBounds (Fin.snoc P 0) j)=∑ j, testBounds P j := by
  rw [testBounds_snoc_zero,GGFiniteReweightingJets.sum_snoc_zero]

theorem polynomialJet_succ {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (k n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ) (x : Fin K → ℝ) (t : ℝ) :
    polynomialJet nu v (k+1) n P Phi x t=
      polynomialJet nu v k (n+1) (Fin.snoc P 0)
        (fun x s ↦ Phi x (initial s)*firstJetInsertion n unitOverlap (tests P)
          (fun j ↦ pairMean nu v (tests P j) x) s) x t := by
  simp only [polynomialJet,tests_snoc_zero,jet_succ]

theorem polynomialError_nonneg {N K n : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (P : Fin (n+1) → Polynomial ℝ) (x : Fin K → ℝ) : 0≤polynomialError nu v P x :=
  Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun q _ ↦
    mul_nonneg (abs_nonneg _) (boundedPowerError_nonneg nu v x n q)))

theorem polynomialError_integrable {N K n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (P : Fin (n+1) → Polynomial ℝ) :
    Integrable (fun x : Fin K → ℝ ↦ polynomialError nu v P x) (positiveCubeLaw K) :=
  SphericalPolynomialFirstJetCubeMean.polynomialError_integrable nu hv n P

theorem polynomialJet_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (k n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) (t : ℝ) :
    Measurable (fun x ↦ polynomialJet nu v k n P Phi x t) :=
  jet_parameter_measurable nu hv k n (tests_measurable P) (testBounds P) (tests_bound P) hPhi measurable_const

theorem polynomialJet_one_zero_bound {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (n : ℕ) (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : ∀ x, Measurable (Phi x)) {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (hxp : ∀ p, 0<x p) :
    |polynomialJet nu v 1 n P Phi x 0|≤((n : ℝ)+1)*C*polynomialError nu v P x := by
  rw [polynomialJet,jet_one_zero_eq_actual nu hv.le n (tests_measurable P) (testBounds P) (tests_bound P) hPhi hC hp x]
  exact polynomial_firstJet_clipped_error_le nu hv x hx hxp n (Phi x) (hPhi x) hC (hp x) P hPK

theorem polynomialJet_zero_bound {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (k n : ℕ) (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : ∀ x, Measurable (Phi x)) {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (hxp : ∀ p, 0<x p) :
    |polynomialJet nu v (k+1) n P Phi x 0|≤
      C*(2*(∑ j, testBounds P j))^k*((n+1).ascFactorial (k+1) : ℝ)*polynomialError nu v P x := by
  induction k generalizing n C with
  | zero =>
    have HH := polynomialJet_one_zero_bound nu hv n P hPK hPhi hC hp x hx hxp
    convert HH using 1 <;> simp only [pow_zero,Nat.ascFactorial_succ,Nat.ascFactorial_zero,
      Nat.add_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_one] <;> ring
  | succ k ih =>
    let Phi' : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ := fun z s ↦
      Phi z (initial s)*firstJetInsertion n unitOverlap (tests P) (fun j ↦ pairMean nu v (tests P j) z) s
    have hPK' : ∀ j : Fin (n+2), ((Fin.snoc P 0 : Fin (n+2) → Polynomial ℝ) j).natDegree≤K := by
      intro j
      refine Fin.lastCases ?_ (fun l ↦ ?_) j
      · simp only [Fin.snoc_last,Polynomial.natDegree_zero]; exact Nat.zero_le _
      · simpa only [Fin.snoc_castSucc] using hPK l
    have hPhi' (z : Fin K → ℝ) : Measurable (Phi' z) :=
      inserted_test_measurable n (SphericalFirstJetPowerBudget.unitOverlap_measurable N)
        (tests_measurable P) (fun j ↦ pairMean nu v (tests P j) z) (hPhi z)
    have hp' (z : Fin K → ℝ) : ∀ s, |Phi' z s|≤C*(2*((n : ℝ)+1)*(∑ j, testBounds P j)) :=
      inserted_test_bound n unitOverlap (tests P) (fun j ↦ pairMean nu v (tests P j) z) (testBounds P)
        (tests_bound P) (fun j ↦ pairMean_abs_le nu hv.le (tests_bound P j) z) hC (hp z)
    have hB0 : 0≤∑ j, testBounds P j := Finset.sum_nonneg (fun j _ ↦ norm_nonneg _)
    have hC' : 0≤C*(2*((n : ℝ)+1)*(∑ j, testBounds P j)) :=
      mul_nonneg hC (mul_nonneg (by positivity) hB0)
    have HH := ih (n+1) (Fin.snoc P 0) hPK' hPhi' hC' hp'
    rw [sum_testBounds_snoc_zero] at HH
    have hE : polynomialError nu v (Fin.snoc P 0) x≤polynomialError nu v P x :=
      SphericalPolynomialErrorMonotonicity.polynomialError_snoc_successor_le nu hv x hxp P
    have hFactor : 0≤C*(2*((n : ℝ)+1)*(∑ j, testBounds P j))*(2*(∑ j, testBounds P j))^k*
        ((n+1+1).ascFactorial (k+1) : ℝ) := by positivity
    have HH' := HH.trans (mul_le_mul_of_nonneg_left hE hFactor)
    have hfac : (n+1).ascFactorial (k+1+1)=(n+1)*(n+2).ascFactorial (k+1) := by
      rw [Nat.ascFactorial_succ]
      exact (Nat.succ_ascFactorial (n+1) (k+1)).symm
    calc
      _ = |polynomialJet nu v (k+1) (n+1) (Fin.snoc P 0) Phi' x 0| := by rw [polynomialJet_succ]
      _ ≤ _ := HH'
      _ = _ := by rw [hfac,pow_succ]; push_cast; ring

theorem polynomialJet_abs_integrable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (k n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C) (t : ℝ) :
    Integrable (fun x ↦ |polynomialJet nu v k n P Phi x t|) (positiveCubeLaw K) := by
  have hPhis (x : Fin K → ℝ) : Measurable (Phi x) := by
    convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hM : Measurable (fun x ↦ |polynomialJet nu v k n P Phi x t|) :=
    continuous_abs.measurable.comp (polynomialJet_measurable nu hv k n P hPhi t)
  apply Integrable.of_bound hM.aestronglyMeasurable
    (C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, testBounds P j))*(2*(∑ j, testBounds P j))^k*((n+1).ascFactorial k : ℝ))
  exact Eventually.of_forall (fun x ↦ by
    simpa only [polynomialJet,Real.norm_eq_abs,abs_abs] using
      jet_abs_le nu hv k n (tests_measurable P) (testBounds P) (tests_bound P) hPhis hC hp x |t| t le_rfl)

theorem polynomialJet_zero_l1_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (k n : ℕ) (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C) :
    (∫ x, |polynomialJet nu v (k+1) n P Phi x 0| ∂positiveCubeLaw K)≤
      (C*(2*(∑ j, testBounds P j))^k*((n+1).ascFactorial (k+1) : ℝ))*
        (∫ x, polynomialError nu v P x ∂positiveCubeLaw K) := by
  have hPhis (x : Fin K → ℝ) : Measurable (Phi x) := by
    convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hpoint : ∀ᵐ x ∂positiveCubeLaw K,
      |polynomialJet nu v (k+1) n P Phi x 0|≤
        (C*(2*(∑ j, testBounds P j))^k*((n+1).ascFactorial (k+1) : ℝ))*polynomialError nu v P x := by
    apply (positiveCubeLaw_support K).mono
    intro x hx
    have hxp (p : Fin K) : 0<x p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) (hx p).1
    have hxb (p : Fin K) : |x p|≤2 := by rw [abs_of_pos (hxp p)]; linarith [(hx p).2]
    exact polynomialJet_zero_bound nu hv k n P hPK hPhis hC hp x hxb hxp
  have H := integral_mono_ae (polynomialJet_abs_integrable nu hv.le (k+1) n P hPhi hC hp 0)
    ((polynomialError_integrable nu hv.le P).const_mul _)
    hpoint
  rw [integral_const_mul] at H
  exact H


end
end TensorPCA.NonRSLowerProofs.SphericalGGZeroJets
