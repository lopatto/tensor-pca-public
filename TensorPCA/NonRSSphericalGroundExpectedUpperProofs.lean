-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.SphericalParisiGroundPrimalUpper
public import TensorPCA.NonRSSphericalGroundUpperTransportProofs
public import TensorPCA.NonRSSphericalGroundTrialTransportProofs
public import TensorPCA.NonRSSphericalGroundOneStepUpperReductionProofs

/-! Unconditional upper bounds for the expected slice maximum.
The finite Gaussian one-step comparison, exact mean and functional transports,
and the proved cofinality/filter arguments are all discharged. A full ground-state limit also requires a matching physical lower bound. -/
@[expose] public section
namespace TensorPCA.NonRSSphericalGroundExpectedUpperProofs
open Set Filter
open scoped Topology
open NonRSUpperProofs
noncomputable section

theorem eventual_expectedSliceGround_le_oneStep_cost_add (k : ℕ) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (delta b q : ℝ)
    (hAd : Scalar.FourParameterAdmissible delta 0 b q) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, GroundState.expectedSliceGround N k m ≤
      (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0
        (Scalar.fourParameterProfile delta 0 b q) + eps := by
  have hfloor : 0 < (delta + b * (1 - q)) - b * (1 - q) := by
    simpa only [add_sub_cancel_right] using hAd.1
  have H := SphericalParisiGroundPrimalUpper.eventual_actual_ground_functional_upper
    (fun p : Fin k => p.val + 1) (VariationalProofs.sliceCoefficient k m)
    (VariationalProofs.sliceCoefficient_nonneg k hm) (fun p => by omega)
    (L := delta + b * (1 - q)) (α := b) (s := q)
    hAd.2.2.1 hAd.2.2.2 hfloor heps
  rw [NonRSSphericalGroundTrialTransportProofs.source_functional_eq_half_parisiFunctional
    k m hAd.1 hAd.2.2.1 hAd.2.2.2] at H
  filter_upwards [H, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  rw [NonRSSphericalGroundUpperTransportProofs.expectedSliceGround_eq_actualMaximum hNpos k hm]
  exact hN

/-- Every positive concave antitone profile gives a genuine eventual physical
mean upper, via the proved one-step cofinal family. -/
theorem eventual_expectedSliceGround_le_half_cost_add (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, GroundState.expectedSliceGround N k m ≤
      (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0 p + eps := by
  have hm : m ∈ Icc (-1 : ℝ) 1 := ⟨(abs_lt.mp hm1).1.le, (abs_lt.mp hm1).2.le⟩
  exact NonRSSphericalGroundOneStepUpperReductionProofs.eventual_expectedSliceGround_le_half_cost_add
    k hk hm0 hm1
    (fun delta b q hAd eps heps =>
      eventual_expectedSliceGround_le_oneStep_cost_add k hm delta b q hAd heps)
    hp heps

/-- The actual finite-mixture physical upper half of the required ground
formula. There is no unproved intermediate comparison left in this type. -/
theorem eventual_expectedSliceGround_le_variationalValue_add (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, GroundState.expectedSliceGround N k m ≤
      Scalar.variationalValue (Scalar.xiSlice k m) 0 + eps := by
  have hm : m ∈ Icc (-1 : ℝ) 1 := ⟨(abs_lt.mp hm1).1.le, (abs_lt.mp hm1).2.le⟩
  exact NonRSSphericalGroundOneStepUpperReductionProofs.eventual_expectedSliceGround_le_variationalValue_add
    k hk hm0 hm1
    (fun delta b q hAd eps heps =>
      eventual_expectedSliceGround_le_oneStep_cost_add k hm delta b q hAd heps)
    heps

theorem eventual_expectedSliceGround_succ_le_variationalValue_add (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm0 : 0 < |m|) (hm1 : |m| < 1) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, GroundState.expectedSliceGround (n + 1) k m ≤
      Scalar.variationalValue (Scalar.xiSlice k m) 0 + eps :=
  (tendsto_add_atTop_nat 1).eventually
    (eventual_expectedSliceGround_le_variationalValue_add k hk hm0 hm1 heps)


end
end TensorPCA.NonRSSphericalGroundExpectedUpperProofs
