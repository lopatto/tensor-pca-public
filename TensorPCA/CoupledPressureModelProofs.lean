-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledSignedEndpointProofs
public import TensorPCA.GaussianAngularOuterProofs
public import Mathlib.Probability.ConditionalProbability

/-! The signed-window angular interpolation pressure. The restricted
sphere law is normalized explicitly; its logarithmic base-mass offset remains
in the pressure and cancels exactly at each endpoint. -/
@[expose] public section
namespace TensorPCA.CoupledPressureModelProofs
open MeasureTheory ProbabilityTheory Set Filter CoupledEndpointModel CoupledGaussianKernelProofs
open GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianAngularPressureProofs GaussianAngularOuterProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- Actual mass of the signed overlap window under two sphere-prior samples. -/
def signedMass (N : ℕ) (u eta : ℝ) : ℝ :=
  ((Model.spherePrior N).prod (Model.spherePrior N)).real (signedPairWindow N u eta)

/-- Actual sphere-pair probability conditioned on the positive signed window. -/
def signedWindowProbability (N : ℕ) (u eta : ℝ) : Measure (Model.Vector N × Model.Vector N) :=
  ProbabilityTheory.cond ((Model.spherePrior N).prod (Model.spherePrior N)) (signedPairWindow N u eta)

instance signedWindowProbability_finite (N : ℕ) (u eta : ℝ) :
    IsFiniteMeasure (signedWindowProbability N u eta) := by
  unfold signedWindowProbability
  infer_instance

theorem signedMass_pos {N : ℕ} (hN : 2 ≤ N) {u eta : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) : 0 < signedMass N u eta := by
  exact (ENNReal.toReal_pos_iff).mpr ⟨signedPairWindow_mass_pos hN hu heta,measure_lt_top _ _⟩

theorem signedWindowProbability_isProbabilityMeasure {N : ℕ} (hN : 2 ≤ N) {u eta : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    IsProbabilityMeasure (signedWindowProbability N u eta) := by
  exact cond_isProbabilityMeasure (signedPairWindow_mass_pos hN hu heta).ne'

theorem signedWindowProbability_eq (N : ℕ) (u eta : ℝ) :
    signedWindowProbability N u eta =
      (((Model.spherePrior N).prod (Model.spherePrior N)) (signedPairWindow N u eta))⁻¹ •
        PairWindowReflectionProofs.signedWindowLaw N u eta := rfl

theorem signedWindowProbability_bounds {N k : ℕ} (hN : 0 < N)
    (lam a u eta : ℝ) : ∀ᵐ xy ∂signedWindowProbability N u eta,
      ‖physicalLinear N k lam xy‖ ≤ 2*|lam| *Real.sqrt N ∧
      ‖commonLinear N a xy‖ ≤ 2*Real.sqrt ((N : ℝ)*a) := by
  change ∀ᵐ xy ∂_ • PairWindowReflectionProofs.signedWindowLaw N u eta, _
  apply MeasureTheory.Measure.ae_smul_measure
  apply ae_restrict_of_ae
  have hx : ∀ᵐ xy : Model.Vector N × Model.Vector N
      ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hy : ∀ᵐ xy : Model.Vector N × Model.Vector N
      ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.2‖ = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hN)
  filter_upwards [hx,hy] with xy hx hy
  exact ⟨physicalLinear_norm_le N k lam xy hx hy,commonLinear_norm_le N a xy hx hy⟩

/-- The concrete coupled interpolation pressure, including its genuine
unnormalized window mass and the annealed fresh-level shift. -/
def coupledPressure (N k : ℕ) (lam m u eta theta : ℝ) : ℝ :=
  Real.log (signedMass N u eta)/(N : ℝ)+
    averagedAngularPressure (signedWindowProbability N u eta)
      (physicalLinear N k lam) (commonLinear N (Coupled.xiPrime k lam u)) (m/2) theta/(N : ℝ)+
        (Coupled.xiPrime k lam 1-Coupled.xiPrime k lam u)*(Real.sin theta)^2

section GenericEndpoints
variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem angularLogPressure_zero (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {p : ℝ} (hp : p ≠ 0) (w : EuclideanSpace ℝ κ) :
    angularLogPressure ν A L p 0 w = logPartition ν A w := by
  have hlog (g : EuclideanSpace ℝ ι) :
      logPartition ν (angleLinear A L w g) (anglePoint 0) = logPartition ν A w := by
    unfold logPartition GaussianSpinInterpolation.moment weight
    simp only [one_mul,angleLinear_anglePoint,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,add_zero]
  unfold angularLogPressure angularNormalizer angularPower powerWeight
  simp only [hlog,integral_const,probReal_univ,one_smul,Real.log_exp]
  exact mul_div_cancel_left₀ _ hp

theorem angularNormalizer_half_pi (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    angularNormalizer ν A L p (Real.pi/2) w =
      ∫ g, Real.exp (p*logPartition ν L g) ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  unfold angularNormalizer angularPower powerWeight
  apply integral_congr_ae
  exact Eventually.of_forall (fun g ↦ by
    unfold logPartition GaussianSpinInterpolation.moment weight
    simp only [one_mul,angleLinear_anglePoint,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_add])
end GenericEndpoints

theorem moment_signedWindowProbability {ι : Type*} [Fintype ι] (N : ℕ) (u eta : ℝ)
    (L : (Model.Vector N × Model.Vector N) → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ ι) :
    GaussianSpinInterpolation.moment (signedWindowProbability N u eta) (fun _ ↦ 1) L w =
      (signedMass N u eta)⁻¹ *GaussianSpinInterpolation.moment
        (PairWindowReflectionProofs.signedWindowLaw N u eta) (fun _ ↦ 1) L w := by
  rw [signedWindowProbability_eq]
  unfold GaussianSpinInterpolation.moment
  rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  rfl

theorem logPartition_signedWindowProbability {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : 2 ≤ N) {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta)
    (L : (Model.Vector N × Model.Vector N) → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ ι)
    (hM : 0 < GaussianSpinInterpolation.moment
      (PairWindowReflectionProofs.signedWindowLaw N u eta) (fun _ ↦ 1) L w) :
    logPartition (signedWindowProbability N u eta) L w =
      logPartition (PairWindowReflectionProofs.signedWindowLaw N u eta) L w-Real.log (signedMass N u eta) := by
  unfold logPartition
  rw [moment_signedWindowProbability,Real.log_mul (inv_ne_zero (signedMass_pos hN hu heta).ne') hM.ne',Real.log_inv]
  ring

/-- The actual physical endpoint restores the unnormalized signed free energy. -/
theorem coupledPressure_zero {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ) {m u eta : ℝ}
    (hm : m ≠ 0) (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    coupledPressure N k lam m u eta 0 = PairWindowReflectionProofs.meanSignedPairFreeEnergy N k lam u eta := by
  have hp : m/2 ≠ 0 := div_ne_zero hm (by norm_num)
  have heq (w : Model.Tensor N k) :
      logPartition (signedWindowProbability N u eta) (physicalLinear N k lam) w =
        Real.log (PairWindowReflectionProofs.signedPairPartition N k lam u eta w)-Real.log (signedMass N u eta) := by
    rw [logPartition_signedWindowProbability hN hu heta _ _ (by
      rw [← PairWindowReflectionProofs.signedPairPartition_eq_moment]
      exact PairWindowReflectionProofs.signedPairPartition_pos hN lam hu heta w)]
    rw [logPartition,← PairWindowReflectionProofs.signedPairPartition_eq_moment]
  unfold coupledPressure averagedAngularPressure
  simp only [angularLogPressure_zero _ _ _ hp,Real.sin_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero]
  rw [show SYK.standardGaussianMeasureOnEuclidean (Fin k → Fin N) = Model.noiseLaw N k from map_pi_eq_stdGaussian]
  simp_rw [heq]
  rw [integral_sub (PairWindowReflectionProofs.log_signedPairPartition_integrable hN lam hu heta) (integrable_const _),
    integral_const,probReal_univ,one_smul]
  unfold PairWindowReflectionProofs.meanSignedPairFreeEnergy
  rw [integral_div]
  ring

theorem common_logPartition_signedWindowProbability {N : ℕ} (hN : 2 ≤ N)
    (a : ℝ) {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) (g : Model.Vector N) :
    logPartition (signedWindowProbability N u eta) (commonLinear N a) g =
      Real.log (signedCommonPartition N a u eta g)-Real.log (signedMass N u eta) := by
  rw [logPartition_signedWindowProbability hN hu heta _ _ (by
    rw [← CoupledSignedEndpointProofs.signedCommonPartition_eq_moment]
    exact CoupledSignedEndpointProofs.signedCommonPartition_pos hN a hu heta g)]
  rw [logPartition,← CoupledSignedEndpointProofs.signedCommonPartition_eq_moment]

/-- Exact fractional-power normalization at the common endpoint. -/
theorem angularNormalizer_signed_half_pi {N k : ℕ} (hN : 2 ≤ N) (lam a p : ℝ)
    {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) (w : Model.Tensor N k) :
    angularNormalizer (signedWindowProbability N u eta) (physicalLinear N k lam) (commonLinear N a)
      p (Real.pi/2) w = Real.exp (-p*Real.log (signedMass N u eta))*
        (∫ g, Real.exp (p*Real.log (signedCommonPartition N a u eta g)) ∂stdGaussian (Model.Vector N)) := by
  rw [angularNormalizer_half_pi]
  rw [show SYK.standardGaussianMeasureOnEuclidean (Fin N) = stdGaussian (Model.Vector N) from map_pi_eq_stdGaussian]
  simp_rw [common_logPartition_signedWindowProbability hN a hu heta]
  have he (g : Model.Vector N) :
      Real.exp (p*(Real.log (signedCommonPartition N a u eta g)-Real.log (signedMass N u eta))) =
        Real.exp (-p*Real.log (signedMass N u eta))*Real.exp (p*Real.log (signedCommonPartition N a u eta g)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul]

/-- The normalized interpolation's common endpoint is the literal signed
fractional moment, with its base-mass power cancelled exactly. -/
theorem coupledPressure_half_pi {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ) {m u eta : ℝ}
    (hm : m ≠ 0) (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    coupledPressure N k lam m u eta (Real.pi/2) =
      CoupledSignedEndpointProofs.signedCommonFreshPressure N (Coupled.xiPrime k lam u)
        (Coupled.xiPrime k lam 1) m u eta := by
  let a := Coupled.xiPrime k lam u
  let p := m/2
  let J := ∫ g, Real.exp (p*Real.log (signedCommonPartition N a u eta g)) ∂stdGaussian (Model.Vector N)
  have hp : p ≠ 0 := div_ne_zero hm (by norm_num)
  have : IsProbabilityMeasure (signedWindowProbability N u eta) := signedWindowProbability_isProbabilityMeasure hN hu heta
  have hNorm := angularNormalizer_pos (signedWindowProbability N u eta)
    (physicalLinear N k lam) (commonLinear N a)
    (physicalLinear_continuous N k lam).measurable (commonLinear_continuous N a).measurable
    (show 0 ≤ 2*|lam| *Real.sqrt N by positivity) (show 0 ≤ 2*Real.sqrt ((N : ℝ)*a) by positivity)
    (signedWindowProbability_bounds (k := k) (by omega) lam a u eta) p (Real.pi/2) 0
  rw [angularNormalizer_signed_half_pi hN lam a p hu heta 0] at hNorm
  have hJ : 0 < J := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hNorm
  have hlog (w : Model.Tensor N k) :
      angularLogPressure (signedWindowProbability N u eta) (physicalLinear N k lam) (commonLinear N a)
        p (Real.pi/2) w = -Real.log (signedMass N u eta)+Real.log J/p := by
    unfold angularLogPressure
    rw [angularNormalizer_signed_half_pi hN lam a p hu heta w,
      Real.log_mul (Real.exp_ne_zero _) hJ.ne',Real.log_exp]
    field_simp
  unfold coupledPressure averagedAngularPressure
  change Real.log (signedMass N u eta)/(N : ℝ)+
    (∫ w : Model.Tensor N k, angularLogPressure (signedWindowProbability N u eta)
      (physicalLinear N k lam) (commonLinear N a) p (Real.pi/2) w ∂SYK.standardGaussianMeasureOnEuclidean (Fin k → Fin N))/(N : ℝ)+
      (Coupled.xiPrime k lam 1-a)*(Real.sin (Real.pi/2))^2 = _
  simp_rw [hlog]
  simp only [integral_const,probReal_univ,one_smul,Real.sin_pi_div_two,one_pow,mul_one]
  unfold CoupledSignedEndpointProofs.signedCommonFreshPressure
  change _ = Coupled.xiPrime k lam 1-a+Real.log J/p/(N : ℝ)
  ring

end
end TensorPCA.CoupledPressureModelProofs
