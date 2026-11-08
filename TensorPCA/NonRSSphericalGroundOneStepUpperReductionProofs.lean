-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSSphericalGroundOneStepProofs

/-! Analytic/filter reduction of a fixed-profile physical upper to the complete variational upper. The explicit trial family is an explicit hypothesis of this reduction. No conditional result is exported as a principal theorem. -/
@[expose] public section
namespace TensorPCA.NonRSSphericalGroundOneStepUpperReductionProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

/-- Approximation from above of the actual nonempty profile infimum.
No attained minimum or selected optimizer is introduced. -/
theorem exists_profile_half_cost_lt (xi : ℝ → ℝ) (h : ℝ) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧
      (1 / 2 : ℝ) * Scalar.parisiFunctional xi h p < Scalar.variationalValue xi h + eps := by
  let S : Set ℝ := {v | ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧
    v = Scalar.parisiFunctional xi h p}
  have hSne : S.Nonempty := ⟨Scalar.parisiFunctional xi h (fun _ => 1),
    (fun _ => 1), Scalar.admissibleProfile_const zero_lt_one, rfl⟩
  have hlt : sInf S < sInf S + 2 * eps := by linarith
  obtain ⟨v, ⟨p, hp, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hSne hlt
  refine ⟨p, hp, ?_⟩
  change (1 / 2 : ℝ) * Scalar.parisiFunctional xi h p < (1 / 2 : ℝ) * sInf S + eps
  linarith

/-- The physical one-step trial upper propagates to every admissible rival
through the proved cofinal family; it does not assume that rival is a minimizer. -/
theorem eventual_expectedSliceGround_le_half_cost_add (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1)
    (hTrial : ∀ delta b q : ℝ, Scalar.FourParameterAdmissible delta 0 b q →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
        GroundState.expectedSliceGround N k m ≤
          (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0
            (Scalar.fourParameterProfile delta 0 b q) + eps)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, GroundState.expectedSliceGround N k m ≤
      (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0 p + eps := by
  obtain ⟨delta, b, q, hAd, hcost⟩ :=
    NonRSSphericalGroundOneStepProofs.xiSlice_cost_cofinal_oneStep k hk hm0 hm1 0 hp
  filter_upwards [hTrial delta b q hAd eps heps] with N hN
  linarith

/-- Conditional upper reduction only. The fixed one-step physical trial
family is a genuine intermediate comparison, not the variational conclusion. -/
theorem eventual_expectedSliceGround_le_variationalValue_add (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1)
    (hTrial : ∀ delta b q : ℝ, Scalar.FourParameterAdmissible delta 0 b q →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
        GroundState.expectedSliceGround N k m ≤
          (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0
            (Scalar.fourParameterProfile delta 0 b q) + eps)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, GroundState.expectedSliceGround N k m ≤
      Scalar.variationalValue (Scalar.xiSlice k m) 0 + eps := by
  obtain ⟨p, hp, hcost⟩ := exists_profile_half_cost_lt (Scalar.xiSlice k m) 0 (half_pos heps)
  filter_upwards [eventual_expectedSliceGround_le_half_cost_add k hk hm0 hm1 hTrial hp
    (half_pos heps)] with N hN
  linarith

theorem eventual_expectedSliceGround_succ_le_variationalValue_add (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1)
    (hTrial : ∀ delta b q : ℝ, Scalar.FourParameterAdmissible delta 0 b q →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
        GroundState.expectedSliceGround N k m ≤
          (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0
            (Scalar.fourParameterProfile delta 0 b q) + eps)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, GroundState.expectedSliceGround (n + 1) k m ≤
      Scalar.variationalValue (Scalar.xiSlice k m) 0 + eps :=
  (tendsto_add_atTop_nat 1).eventually
    (eventual_expectedSliceGround_le_variationalValue_add k hk hm0 hm1 hTrial heps)


end
end TensorPCA.NonRSSphericalGroundOneStepUpperReductionProofs
