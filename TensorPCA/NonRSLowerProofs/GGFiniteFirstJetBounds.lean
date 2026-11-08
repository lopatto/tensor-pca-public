-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteFirstJetPermutation

/-! Finite first-jet identities for bounded old tests and propagation of first-anchor GG
error bounds. Reweighting invariance is treated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteFirstJetBounds
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open GGFiniteFirstJet GGFiniteFirstJetPermutation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X V Ω : Type*} [MeasurableSpace X] [MeasurableSpace V] [MeasurableSpace Ω]

theorem discrepancy_test_smul (n : ℕ) (mu : Measure X) (rho : Measure ℝ)
    (f R : X → ℝ) (Q : Fin n → X → ℝ) (psi : ℝ → ℝ) (c : ℝ) :
    discrepancy n mu rho (fun s ↦ c*f s) R Q psi=c*discrepancy n mu rho f R Q psi := by
  have hFresh : (∫ s, (c*f s)*psi (R s) ∂mu)=c*(∫ s, f s*psi (R s) ∂mu) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun s ↦ by dsimp only; ring))
  have hOld (j : Fin n) : (∫ s, (c*f s)*psi (Q j s) ∂mu)=c*(∫ s, f s*psi (Q j s) ∂mu) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun s ↦ by dsimp only; ring))
  unfold discrepancy
  rw [hFresh,integral_const_mul]
  simp_rw [hOld]
  rw [← Finset.mul_sum]
  ring

theorem firstJet_expectation_first_anchor_bounded (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) {C : ℝ} (hPb : ∀ s, |Phi s|≤C)
    (psi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let means := fun j ↦ ∫ r, psi j r ∂rho
    (∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu)=
      -((n : ℝ)+1)*(∑ j : Fin (n+1), discrepancy n mu rho
        (fun s ↦ Phi (fun i ↦ s ((Equiv.swap j 0) i).castSucc))
        (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
        (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) (psi j)) := by
  dsimp only
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let means : Fin (n+1) → ℝ := fun j ↦ ∫ r, psi j r ∂rho
  let A : ℝ := max 1 C
  have hA : 0<A := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  let P : (Fin (n+1) → V) → ℝ := fun s ↦ Phi s/A
  have hPm : Measurable P := hPhi.div_const A
  have hPb1 (s : Fin (n+1) → V) : |P s|≤1 := by
    dsimp only [P]
    rw [abs_div,abs_of_pos hA]
    exact (div_le_one hA).mpr ((hPb s).trans (le_max_right 1 C))
  have H := firstJet_expectation_first_anchor d G n hR P hPm hPb1 psi hpsi B hb
  have hL : (∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu)=
      A*(∫ s, P (initial s)*firstJetInsertion n overlap psi means s ∂mu) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s ↦ by dsimp only [P]; field_simp [hA.ne'])
  have hD (j : Fin (n+1)) : discrepancy n mu rho
      (fun s ↦ Phi (fun i ↦ s ((Equiv.swap j 0) i).castSucc))
      (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) (psi j)=
      A*discrepancy n mu rho (fun s ↦ P (fun i ↦ s ((Equiv.swap j 0) i).castSucc))
      (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) (psi j) := by
    rw [← discrepancy_test_smul]
    congr 1
    funext s
    dsimp only [P]
    field_simp [hA.ne']
  change (∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu)=_
  rw [hL,H]
  dsimp only [mu,rho] at hD
  simp_rw [hD]
  rw [← Finset.mul_sum]
  ring

/-- A finite first-anchor error bound, tested on every bounded old observable,
propagates to the first jet of any test bounded by `C`.
-/
theorem firstJet_expectation_abs_le_of_first_anchor_budget
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hPb : ∀ s, |Phi s|≤C)
    (psi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (err : Fin (n+1) → ℝ)
    (hBudget : ∀ j, ∀ P : (Fin (n+1) → V) → ℝ, Measurable P → (∀ s, |P s|≤1) →
      |discrepancy n (law d G (n+2))
        (((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)) (fun s ↦ P (initial s))
        (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
        (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) (psi j)|≤err j) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let means := fun j ↦ ∫ r, psi j r ∂rho
    |∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu|≤
      ((n : ℝ)+1)*C*(∑ j, err j) := by
  dsimp only
  by_cases hzero : C=0
  · have hPhi0 : Phi=fun _ ↦ 0 := by
      funext s
      have hh : |Phi s|≤0 := by simpa only [hzero] using hPb s
      exact abs_eq_zero.mp (hh.antisymm (abs_nonneg _))
    simpa only [hPhi0,zero_mul,integral_zero,hzero,mul_zero,abs_zero] using (le_refl (0 : ℝ))
  have hCpos : 0<C := lt_of_le_of_ne hC (Ne.symm hzero)
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let means : Fin (n+1) → ℝ := fun j ↦ ∫ r, psi j r ∂rho
  let P : (Fin (n+1) → V) → ℝ := fun s ↦ Phi s/C
  have hPm : Measurable P := hPhi.div_const C
  have hPb1 (s : Fin (n+1) → V) : |P s|≤1 := by
    dsimp only [P]
    rw [abs_div,abs_of_pos hCpos]
    exact (div_le_one hCpos).mpr (hPb s)
  have H := firstJet_expectation_first_anchor d G n hR P hPm hPb1 psi hpsi B hb
  have hErr (j : Fin (n+1)) : |discrepancy n mu rho
      (fun s ↦ P (fun i ↦ s ((Equiv.swap j 0) i).castSucc))
      (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) (psi j)|≤err j := by
    have HH := hBudget j (fun old ↦ P (fun i ↦ old ((Equiv.swap j 0) i)))
      (permuted_test_measurable n (Equiv.swap j 0) hPm)
      (permuted_test_abs_le n (Equiv.swap j 0) hPb1)
    exact HH
  have hUnit : |∫ s, P (initial s)*firstJetInsertion n overlap psi means s ∂mu|≤
      ((n : ℝ)+1)*(∑ j, err j) := by
    rw [H,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤(n : ℝ)+1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ ↦ hErr j))
  have hL : (∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu)=
      C*(∫ s, P (initial s)*firstJetInsertion n overlap psi means s ∂mu) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s ↦ by dsimp only [P]; field_simp [hCpos.ne'])
  rw [hL,abs_mul,abs_of_pos hCpos]
  exact (mul_le_mul_of_nonneg_left hUnit hC).trans_eq (by ring)

end
end TensorPCA.NonRSLowerProofs.GGFiniteFirstJetBounds
