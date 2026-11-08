-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed port from immutable Apache-2.0 source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalParisiSphereNetGround.lean
Only namespace/import paths are adapted to the checked local Gaussian
foundation. Definitions and proof arguments are retained. See LICENSE. -/
module

public import TensorPCA.NonRSUpperProofs.SphericalParisiSphereNetReference
public import TensorPCA.NonRSUpperProofs.SphericalParisiOneStepDualPressureLimit

/-! Physical Gaussian ground-energy transfer from the finite one-step pressure upper through internally constructed sphere nets. -/
@[expose] public section
open TensorPCA.RetainedCountProofs
noncomputable section
namespace TensorPCA.NonRSUpperProofs.SphericalParisiSphereNet
open MeasureTheory ProbabilityTheory Set Filter
open TensorPCA.RetainedCountProofs.FiniteModel PureTensorJetBounds FiniteTensorMixtureMaximum
open SphericalParisiGroundRSUpper SphericalParisiLabeledOriginalEndpoint
open SphericalParisiLabeledCovariance SphericalParisiOneStepDualScalar
open SphericalParisiOneStepDualPressureLimit
open GaussianCompactMaximum
open scoped InnerProductSpace BigOperators Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The literal Gaussian spherical maximum satisfies every positive-mass
one-step dual trial asymptotically. Nets, entropy, derivative bounds, true
Gaussian pressures and the scalar REM cancellation are proved internally. -/
theorem eventual_actual_ground_oneStepDual_upper (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    {α κ q : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        oneStepDual d c α q κ+δ := by
  let C := derivativeConstant d c
  have hC : 0 ≤ C := derivativeConstant_nonneg d c
  let ε := δ/(3*(C+1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hApprox : C*ε ≤ δ/3 := by
    have H : 3*(C+1)*ε=δ := by unfold ε;field_simp
    nlinarith
  let L := Real.log (1+2/ε)
  let β := max α (3*L/δ)+1
  have hαβ : α ≤ β := by have := le_max_left α (3*L/δ);unfold β;linarith
  have hβ : 0 < β := hα.trans_le hαβ
  have hEntropy : L/β ≤ δ/3 := by
    have H := (div_le_iff₀ hδ).mp (le_max_right α (3*L/δ))
    apply (div_le_iff₀ hβ).mpr
    unfold β
    nlinarith
  obtain ⟨μ,hμ,hGround⟩ := exists_actual_netReference_family d c hd hε hβ
  have hPressure := eventual_spin_pressure_oneStepDual_upper d c hc hd μ hμ
    hα hαβ hq hq1 hmargin (δ/3) (by positivity)
  filter_upwards [hPressure,eventually_gt_atTop (0 : ℕ)] with N hP hN
  have hG := hGround N hN
  change (∫ g,actualMaximum (N := N) d c g
    ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
    originalSpinPressure (μ N) d c β/(β*(N : ℝ))+L/β+C*ε at hG
  linarith

/- Probability-tail consumers are omitted from this mean-only port. -/
end TensorPCA.NonRSUpperProofs.SphericalParisiSphereNet

