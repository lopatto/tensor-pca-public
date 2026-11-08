-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteReweightingPadding
public import Mathlib.Data.Nat.Factorial.Basic

/-! Higher derivatives of bounded finite-spin reweighting. Each step adds an iid replica
and multiplies by the finite GG score.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteReweightingJets
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet
open GGFiniteReweightingDerivative GGFiniteReweightingPadding
open scoped BigOperators
noncomputable section
variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

/-- Recursive literal replica formula. Recursing on the derivative order
keeps each finite index in the existing n+1-anchor convention. -/
def reweightingJet (d : Measure Ω) (G : Kernel Ω V) (overlap : V → V → ℝ) :
    (k n : ℕ) → (Fin (n+1) → ℝ → ℝ) → (Fin (n+1) → ℝ) →
      ((Fin (n+1) → V) → ℝ) → ℝ → ℝ
  | 0,n,psi,means,Phi,t => reweightingExpectation n d G overlap psi means Phi t
  | k+1,n,psi,means,Phi,t =>
      reweightingJet d G overlap k (n+1) (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0)
        (fun s ↦ Phi (initial s)*firstJetInsertion n overlap psi means s) t

theorem snoc_zero_measurable {n : ℕ} {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) : ∀ j : Fin (n+2),
      Measurable ((Fin.snoc psi (fun _ : ℝ ↦ 0) : Fin (n+2) → ℝ → ℝ) j) := by
  intro j
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simpa only [Fin.snoc_last] using (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ)))
  · simpa only [Fin.snoc_castSucc] using hpsi l

theorem snoc_zero_bounds {n : ℕ} {psi : Fin (n+1) → ℝ → ℝ} {B : Fin (n+1) → ℝ}
    (hb : ∀ j r, |psi j r|≤B j) : ∀ (j : Fin (n+2)) (r : ℝ),
      |(Fin.snoc psi (fun _ : ℝ ↦ 0) : Fin (n+2) → ℝ → ℝ) j r|≤(Fin.snoc B 0 : Fin (n+2) → ℝ) j := by
  intro j
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · intro r; simp only [Fin.snoc_last,abs_zero,le_refl]
  · simpa only [Fin.snoc_castSucc] using hb l

theorem snoc_zero_mean_bounds {n : ℕ} {means B : Fin (n+1) → ℝ}
    (hm : ∀ j, |means j|≤B j) : ∀ j : Fin (n+2),
      |(Fin.snoc means 0 : Fin (n+2) → ℝ) j|≤(Fin.snoc B 0 : Fin (n+2) → ℝ) j := by
  intro j
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simp only [Fin.snoc_last,abs_zero,le_refl]
  · simpa only [Fin.snoc_castSucc] using hm l

theorem sum_snoc_zero {n : ℕ} (B : Fin (n+1) → ℝ) :
    (∑ j : Fin (n+2), Fin.snoc B 0 j)=∑ j, B j := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,add_zero]

theorem inserted_test_measurable (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means : Fin (n+1) → ℝ) {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) :
    Measurable (fun s : Fin (n+2) → V ↦ Phi (initial s)*firstJetInsertion n overlap psi means s) :=
  (hPhi.comp (initial_measurable _)).mul (firstJetInsertion_measurable n hR hpsi means)

theorem inserted_test_bound (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means B : Fin (n+1) → ℝ)
    (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (s : Fin (n+2) → V) :
    |Phi (initial s)*firstJetInsertion n overlap psi means s|≤C*(2*((n : ℝ)+1)*(∑ j, B j)) := by
  rw [abs_mul]
  exact mul_le_mul (hp _) (firstJetInsertion_abs_le n overlap psi means B hb hm s) (abs_nonneg _) hC

theorem reweightingJet_hasDerivAt
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (k n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C) (t : ℝ) :
    HasDerivAt (reweightingJet d G overlap k n psi means Phi)
      (reweightingJet d G overlap (k+1) n psi means Phi t) t := by
  induction k generalizing n C with
  | zero =>
    exact reweightingExpectation_hasDerivAt d G n hR hpsi means B hb hm hPhi hC hp t
  | succ k ih =>
    have hb0 : 0≤∑ j, B j := Finset.sum_nonneg (fun j _ ↦ (abs_nonneg (psi j 0)).trans (hb j 0))
    have hC' : 0≤C*(2*((n : ℝ)+1)*(∑ j, B j)) := mul_nonneg hC (mul_nonneg (by positivity) hb0)
    exact ih (n+1) (snoc_zero_measurable hpsi) (Fin.snoc means 0) (Fin.snoc B 0)
      (snoc_zero_bounds hb) (snoc_zero_mean_bounds hm)
      (inserted_test_measurable n hR hpsi means hPhi) hC'
      (inserted_test_bound n overlap psi means B hb hm hC hp)

theorem reweightingJet_abs_le_mass
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (k n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C) (t : ℝ) :
    |reweightingJet d G overlap k n psi means Phi t|≤
      (C*(2*(∑ j, B j))^k*((n+1).ascFactorial k : ℝ))*
        reweightingExpectation n d G overlap psi means (fun _ ↦ 1) t := by
  induction k generalizing n C with
  | zero => simpa only [reweightingJet,pow_zero,Nat.ascFactorial_zero,Nat.cast_one,mul_one] using
      reweightingExpectation_abs_le_mass d G n hR hpsi means B hb hm hPhi hC hp t
  | succ k ih =>
    have hb0 : 0≤∑ j, B j := Finset.sum_nonneg (fun j _ ↦ (abs_nonneg (psi j 0)).trans (hb j 0))
    have hC' : 0≤C*(2*((n : ℝ)+1)*(∑ j, B j)) := mul_nonneg hC (mul_nonneg (by positivity) hb0)
    have HH := ih (n+1) (snoc_zero_measurable hpsi) (Fin.snoc means 0) (Fin.snoc B 0)
      (snoc_zero_bounds hb) (snoc_zero_mean_bounds hm)
      (inserted_test_measurable n hR hpsi means hPhi) hC'
      (inserted_test_bound n overlap psi means B hb hm hC hp)
    have hmass := reweightingExpectation_snoc_zero d G n hR hpsi means B hb hm
      (Phi := fun _ ↦ 1) measurable_const (fun _ ↦ by norm_num : ∀ old, |(1 : ℝ)|≤1) t
    simp only [sum_snoc_zero] at HH
    rw [hmass] at HH
    have hfac : (n+1).ascFactorial (k+1)=(n+1)*(n+2).ascFactorial k := by
      rw [Nat.ascFactorial_succ]
      exact (Nat.succ_ascFactorial (n+1) k).symm
    convert HH using 1 <;> first | rfl | (rw [hfac,pow_succ]; push_cast; ring)

theorem reweightingJet_abs_le
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (k n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (T t : ℝ) (ht : |t|≤T) :
    |reweightingJet d G overlap k n psi means Phi t|≤
      C*Real.exp (2*((n : ℝ)+1)*T*(∑ j, B j))*(2*(∑ j, B j))^k*((n+1).ascFactorial k : ℝ) := by
  have hb0 : 0≤∑ j, B j := Finset.sum_nonneg (fun j _ ↦ (abs_nonneg (psi j 0)).trans (hb j 0))
  have H := reweightingJet_abs_le_mass d G k n hR hpsi means B hb hm hPhi hC hp t
  have he : Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j))≤Real.exp (2*((n : ℝ)+1)*T*(∑ j, B j)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) hb0
  have hmB := (reweightingMass_le d G n hR hpsi means B hb hm t).trans he
  have hc0 : 0≤C*(2*(∑ j, B j))^k*((n+1).ascFactorial k : ℝ) := by positivity
  exact H.trans ((mul_le_mul_of_nonneg_left hmB hc0).trans_eq (by ring))

end
end TensorPCA.NonRSLowerProofs.GGFiniteReweightingJets
