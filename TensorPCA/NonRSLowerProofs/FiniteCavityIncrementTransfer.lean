-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-! A fixed positive increment gives an eventual normalized lower bound.
Residue classes retain a finite initial minimum; no pressure limit or global
linear boundedness is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityIncrementTransfer
open Filter Set
open scoped Topology
noncomputable section

theorem eventual_normalized_lower_of_increment (C : ℕ→ℝ) {M : ℕ} (hM : 0<M) {L : ℝ}
    (hInc : ∀ᶠ n : ℕ in atTop,(M : ℝ)*L≤C (n+M)-C n)
    {eta : ℝ} (heta : 0<eta) :
    ∀ᶠ n : ℕ in atTop,L-eta≤C n/(n : ℝ) := by
  classical
  obtain ⟨n0,hInc⟩ := eventually_atTop.1 hInc
  obtain ⟨B,hB⟩ := ((Set.finite_Ico n0 (n0+M)).image (fun n : ℕ => C n-(n : ℝ)*L)).bddBelow
  have hLower (n : ℕ) : n0≤n → B≤C n-(n : ℝ)*L := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hbase : n<n0+M
      · exact hB ⟨n,⟨hn,hbase⟩,rfl⟩
      · have hprev : n0≤n-M := by omega
        have hind := ih (n-M) (by omega) hprev
        have hstep := hInc (n-M) hprev
        have hnM : n-M+M=n := by omega
        rw [hnM] at hstep
        have hcast : ((n-M : ℕ) : ℝ)+(M : ℝ)=(n : ℝ) := by exact_mod_cast hnM
        have hcastL := congrArg (fun a : ℝ => a*L) hcast
        nlinarith only [hind,hstep,hcastL]
  have hLimit : Tendsto (fun n : ℕ => B/(n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop n0,eventually_gt_atTop (0 : ℕ),
    hLimit.eventually (lt_mem_nhds (show -eta<(0 : ℝ) by linarith only [heta]))] with n hn hnpos hsmall
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr hnpos
  have H : B+(n : ℝ)*L≤C n := by linarith only [hLower n hn]
  have HD := div_le_div_of_nonneg_right H hnR.le
  rw [add_div,mul_div_cancel_left₀ _ hnR.ne'] at HD
  linarith only [HD,hsmall]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityIncrementTransfer
