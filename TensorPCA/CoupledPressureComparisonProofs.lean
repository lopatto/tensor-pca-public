-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianAngularComparisonProofs
public import TensorPCA.CoupledPressureModelProofs

/-! Finite-dimensional coupled interpolation on the signed
sphere window. The field definitions specify every Gaussian response and both pressure endpoints. -/
@[expose] public section
namespace TensorPCA.CoupledPressureComparisonProofs
open MeasureTheory ProbabilityTheory Set Filter CoupledGaussianKernelProofs CoupledPressureModelProofs
open GaussianSpinInterpolation GaussianAngularOuterProofs GaussianAngularComparisonProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem signedWindowProbability_support {N : ℕ} (hN : 0 < N) (u eta : ℝ) :
    ∀ᵐ xy ∂signedWindowProbability N u eta,
      ‖xy.1‖ = 1 ∧ ‖xy.2‖ = 1 ∧ xy ∈ signedPairWindow N u eta := by
  rw [signedWindowProbability_eq]
  apply Measure.ae_smul_measure
  have hx : ∀ᵐ xy : Model.Vector N × Model.Vector N
      ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hy : ∀ᵐ xy : Model.Vector N × Model.Vector N
      ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.2‖ = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hN)
  change ∀ᵐ xy ∂((Model.spherePrior N).prod (Model.spherePrior N)).restrict (signedPairWindow N u eta), _
  filter_upwards [ae_restrict_of_ae hx,ae_restrict_of_ae hy,
    ae_restrict_mem (isOpen_signedPairWindow N u eta).measurableSet] with xy hx hy hwin
  exact ⟨hx,hy,hwin⟩

/-- The actual normalized pressure comparison. The constant window-mass offset
cancels, while the fresh-level shift supplies exactly the diagonal correction. -/
theorem coupledPressure_comparison {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (heven : Even k)
    (lam : ℝ) {m u eta : ℝ} (hm : m ∈ Icc (1 : ℝ) 2) (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    coupledPressure N k lam m u eta 0 ≤ coupledPressure N k lam m u eta (Real.pi/2)-
      Coupled.theta k lam 1+(1-m)*Coupled.theta k lam u+2*Coupled.xiPrime k lam 1*eta := by
  let ν := signedWindowProbability N u eta
  let a := Coupled.xiPrime k lam u
  let d := Coupled.xiPrime k lam 1
  let B := 2*(N : ℝ)*(Coupled.theta k lam 1+Coupled.theta k lam u)-
    4*(N : ℝ)*d*eta-2*(N : ℝ)*(d-a)
  let C := 4*(N : ℝ)*Coupled.theta k lam u
  letI := signedWindowProbability_isProbabilityMeasure hN hu heta
  have hNp : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNp
  have hp : m/2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hm.1],by linarith [hm.2]⟩
  have hDiag : ∀ᵐ xy ∂ν, B ≤ coordinateCovariance (commonLinear N a xy) (commonLinear N a xy)-
      coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam xy) := by
    filter_upwards [signedWindowProbability_support hNp u eta] with xy hxy
    have H := signed_window_diagonal_lower N hk lam hu xy hxy.1 hxy.2.1 hxy.2.2
    dsimp only [B,a,d]
    linarith only [H]
  have H := angular_pressure_comparison_of_covariance_bounds ν
    (physicalLinear N k lam) (commonLinear N a)
    (physicalLinear_continuous N k lam).measurable (commonLinear_continuous N a).measurable
    (show 0 ≤ 2*|lam| *Real.sqrt N by positivity) (show 0 ≤ 2*Real.sqrt ((N : ℝ)*a) by positivity)
    (signedWindowProbability_bounds hNp lam a u eta) (m/2) hp B C hDiag
    (common_sub_physical_le N hk heven lam hu)
  have HN := div_le_div_of_nonneg_right H hNr.le
  have hConstant : ((B+(m/2-1)*C)/2)/(N : ℝ) =
      Coupled.theta k lam 1+(m-1)*Coupled.theta k lam u-2*d*eta-(d-a) := by
    dsimp only [B,C]
    field_simp [ne_of_gt hNr]
    <;> ring
  rw [sub_div,hConstant] at HN
  unfold coupledPressure
  simp only [Real.sin_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero,
    Real.sin_pi_div_two,one_pow,mul_one]
  change Real.log (signedMass N u eta)/(N : ℝ)+averagedAngularPressure ν
      (physicalLinear N k lam) (commonLinear N a) (m/2) 0/(N : ℝ) ≤
    Real.log (signedMass N u eta)/(N : ℝ)+averagedAngularPressure ν
      (physicalLinear N k lam) (commonLinear N a) (m/2) (Real.pi/2)/(N : ℝ)+(d-a)-
      Coupled.theta k lam 1+(1-m)*Coupled.theta k lam u+2*d*eta
  linarith only [HN]

/-- The literal unnormalized signed free energy is controlled by the actual
common/fresh endpoint, with the exact interpolation correction and window error. -/
theorem signed_freeEnergy_le_common_endpoint {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (heven : Even k)
    (lam : ℝ) {m u eta : ℝ} (hm : m ∈ Icc (1 : ℝ) 2) (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    PairWindowReflectionProofs.meanSignedPairFreeEnergy N k lam u eta ≤
      CoupledSignedEndpointProofs.signedCommonFreshPressure N (Coupled.xiPrime k lam u)
        (Coupled.xiPrime k lam 1) m u eta-Coupled.theta k lam 1+
          (1-m)*Coupled.theta k lam u+2*Coupled.xiPrime k lam 1*eta := by
  have hm0 : m ≠ 0 := ne_of_gt (by linarith [hm.1] : 0 < m)
  rw [← coupledPressure_zero hN lam hm0 hu heta,← coupledPressure_half_pi hN lam hm0 hu heta]
  exact coupledPressure_comparison hN hk heven lam hm hu heta

end
end TensorPCA.CoupledPressureComparisonProofs
