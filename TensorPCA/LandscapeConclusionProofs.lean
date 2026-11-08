-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.LandscapeVariationalUpperProofs
public import TensorPCA.LandscapeGlobalExtensionProofs

/-! The reviewed landscape conclusion from the explicit critical variational
certificate, scalar extension, and independently proved local branch calculus. -/
@[expose] public section
namespace TensorPCA.LandscapeConclusionProofs

open Set

theorem energy_le_mleValue (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) (hlam : 0 ≤ lam)
    (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) :
    Scalar.energy k lam m ≤ Scalar.mleValue k lam :=
  LandscapeGlobalExtensionProofs.global_energy_upper_of_critical_low k hk
    (fun _ hm0 hmC => LandscapeVariationalUpperProofs.critical_energy_le_gs k hk hm0 hmC)
    lam hlam m hm

theorem energy_zero (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    Scalar.energy k lam 0 = Scalar.gs k := by
  unfold Scalar.energy
  rw [zero_pow (show k ≠ 0 by omega), mul_zero, zero_add]
  exact PureVariationalProofs.pure_variationalValue_xiSlice_zero k hk

theorem landscape : Statements.Landscape := by
  apply CheckedReduction.landscape ScalarSelectionProofs.selectionLaws energy_le_mleValue
  · intro k hk lam _
    exact energy_zero k hk lam
  · intro k hk lam hlam habove
    exact EnergyBranchProofs.secondaryBranch_matches_mleValue k hk hlam habove
  · intro k hk lam hlam hbelow
    exact EnergyBranchProofs.secondaryBranch_below_gs k hk hlam hbelow
  · intro k hk lam hlam
    exact EnergyBranchProofs.localEnergySigns k hk hlam


end TensorPCA.LandscapeConclusionProofs
