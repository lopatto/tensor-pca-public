-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.ThermalReplicaProofs

/-! Finite differential-inequality comparison for the null free-energy gap. -/
@[expose] public section
namespace TensorPCA.NullGronwallProofs
open Set ThermalReplicaProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem freeEnergyGap_le_of_replicaMean_bound {N k : ℕ} (hN : 0 < N)
    (barLam C a : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) barLam,
      t*replicaMean N k t ≤ C*(freeEnergyGap N k t+a))
    {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) barLam) :
    freeEnergyGap N k lam ≤ a*(Real.exp (C*lam)-1) := by
  let g := fun t ↦ Real.exp (-C*t)*(freeEnergyGap N k t+a)
  have hg : ∀ t, HasDerivAt g (Real.exp (-C*t)*
      (t*replicaMean N k t-C*(freeEnergyGap N k t+a))) t := by
    intro t
    have H := (((hasDerivAt_id t).const_mul (-C)).exp).mul
      ((freeEnergyGap_hasDerivAt (k := k) hN t).add_const a)
    convert H using 1
    · rfl
    · simp only [id_eq]
      ring
  have hd : Differentiable ℝ g := fun t ↦ (hg t).differentiableAt
  have ha := antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) barLam)
    hd.continuous.continuousOn hd.differentiableOn (fun t ht ↦ by
      rw [(hg t).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hbound t (interior_subset ht))))
  have H := ha (show (0 : ℝ) ∈ Icc 0 barLam from ⟨le_rfl, hlam.1.trans hlam.2⟩)
    hlam hlam.1
  simp only [g, mul_zero, Real.exp_zero, freeEnergyGap_zero, zero_add, one_mul] at H
  have Hmul := mul_le_mul_of_nonneg_left H (Real.exp_pos (C*lam)).le
  have he : Real.exp (C*lam)*Real.exp (-C*lam) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [← mul_assoc, he, one_mul] at Hmul
  linarith

theorem freeEnergyGap_le_uniform_of_replicaMean_bound {N k : ℕ} (hN : 0 < N)
    (barLam C a : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) barLam,
      t*replicaMean N k t ≤ C*(freeEnergyGap N k t+a))
    {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) barLam) :
    freeEnergyGap N k lam ≤ (Real.exp (C*barLam)-1)*a := by
  calc
    _ ≤ a*(Real.exp (C*lam)-1) := freeEnergyGap_le_of_replicaMean_bound hN barLam C a hbound hlam
    _ ≤ a*(Real.exp (C*barLam)-1) := mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlam.2 hC)) 1) ha
    _ = _ := mul_comm _ _

end
end TensorPCA.NullGronwallProofs
