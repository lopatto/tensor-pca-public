-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledEndpointModel
public import TensorPCA.CoupledEndpointBoundProofs
public import TensorPCA.CoupledRadialEndpointProofs

/-! Regularity and pressure bounds for the unnormalized signed common
field. All radial/comparison inputs are discharged by the physical endpoint
construction, with the fresh-level shift kept explicitly. -/
@[expose] public section
namespace TensorPCA.CoupledSignedEndpointProofs
open Set Filter MeasureTheory ProbabilityTheory CoupledEndpointModel
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem commonLinear_bound_signedWindow {N : ℕ} (hN : 0 < N) (a u eta : ℝ) :
    ∀ᵐ xy ∂PairWindowReflectionProofs.signedWindowLaw N u eta,
      ‖CoupledGaussianKernelProofs.commonLinear N a xy‖ ≤ 2*Real.sqrt ((N : ℝ)*a) := by
  apply ae_restrict_of_ae
  have hx : ∀ᵐ xy : Model.Vector N × Model.Vector N
      ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hy : ∀ᵐ xy : Model.Vector N × Model.Vector N
      ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.2‖ = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hN)
  filter_upwards [hx,hy] with xy hx hy
  exact CoupledGaussianKernelProofs.commonLinear_norm_le N a xy hx hy

theorem signedCommonPartition_eq_moment (N : ℕ) (a u eta : ℝ) (g : Model.Vector N) :
    signedCommonPartition N a u eta g = GaussianSpinInterpolation.moment
      (PairWindowReflectionProofs.signedWindowLaw N u eta) (fun _ => 1)
        (CoupledGaussianKernelProofs.commonLinear N a) g := by
  unfold signedCommonPartition GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
  apply integral_congr_ae
  filter_upwards [] with xy
  simp only [one_mul,CoupledGaussianKernelProofs.commonLinear,
    smul_apply,innerSL_apply_apply,smul_eq_mul]

theorem signedCommonPartition_pos {N : ℕ} (hN : 2 ≤ N) (a : ℝ)
    {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) (g : Model.Vector N) :
    0 < signedCommonPartition N a u eta g := by
  have : NeZero (PairWindowReflectionProofs.signedWindowLaw N u eta) := ⟨fun hz =>
    (CoupledGaussianKernelProofs.signedPairWindow_mass_pos hN hu heta).ne'
      (Measure.restrict_eq_zero.mp hz)⟩
  rw [signedCommonPartition_eq_moment]
  exact GaussianSpinInterpolation.moment_one_pos
    (PairWindowReflectionProofs.signedWindowLaw N u eta)
    (CoupledGaussianKernelProofs.commonLinear N a)
    (CoupledGaussianKernelProofs.commonLinear_continuous N a).measurable
    (commonLinear_bound_signedWindow (by omega) a u eta) g

theorem signedCommonPartition_continuous {N : ℕ} (hN : 0 < N) (a u eta : ℝ) :
    Continuous (signedCommonPartition N a u eta) := by
  have he : signedCommonPartition N a u eta = GaussianSpinInterpolation.moment
      (PairWindowReflectionProofs.signedWindowLaw N u eta) (fun _ => 1)
        (CoupledGaussianKernelProofs.commonLinear N a) :=
    funext (signedCommonPartition_eq_moment N a u eta)
  rw [he]
  exact (GaussianSpinInterpolation.moment_contDiff
    (PairWindowReflectionProofs.signedWindowLaw N u eta) (fun _ => 1)
    (CoupledGaussianKernelProofs.commonLinear N a) measurable_const
    (CoupledGaussianKernelProofs.commonLinear_continuous N a).measurable
    zero_le_one (by positivity)
    ((commonLinear_bound_signedWindow hN a u eta).mono (fun xy hxy => ⟨by norm_num,hxy⟩))).continuous

theorem signedCommon_log_power_continuous {N : ℕ} (hN : 2 ≤ N) (a p : ℝ)
    {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    Continuous (fun g => Real.exp (p*Real.log (signedCommonPartition N a u eta g))) := by
  exact Real.continuous_exp.comp
    (((signedCommonPartition_continuous (N := N) (by omega) a u eta).log
      (fun g => (signedCommonPartition_pos hN a hu heta g).ne')).const_mul p)

def signedCommonFreshPressure (N : ℕ) (a d m u eta : ℝ) : ℝ :=
  d-a+Real.log (∫ g, Real.exp ((m/2)*Real.log (signedCommonPartition N a u eta g))
    ∂stdGaussian (Model.Vector N))/(m/2)/(N : ℝ)

theorem signedCommonFreshPressure_le_gaussian {N : ℕ} (hN : 2 ≤ N)
    {a d L m u eta : ℝ} (ha : 0 ≤ a) (hd : a ≤ d) (hL : 0 ≤ L)
    (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L)
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    Integrable (fun g => Real.exp ((m/2)*Real.log (signedCommonPartition N a u eta g)))
      (stdGaussian (Model.Vector N)) ∧
    signedCommonFreshPressure N a d m u eta ≤
      Real.log (∫ g, Real.exp ((m/2)*Real.log
        (CoupledGaussianIntegralProofs.endpointMoment N a d L g))
        ∂stdGaussian (Model.Vector N))/(m/2)/(N : ℝ)-L*u+L*eta-
          2*Real.log (gaussianTailMass N (1+d)).toReal/(N : ℝ) := by
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hNp
  have hp : 0 < m/2 := by linarith
  have hP : 0 < 1+a-L := by nlinarith
  let t := (gaussianTailMass N (1+d)).toReal
  have ht : 0 < t := (ChiSquareTailProofs.chiSquare_tail_lower hNp (by linarith : 1 ≤ 1+d)).1
  let C := Real.exp (-(N : ℝ)*(d-a)-(N : ℝ)*L*u+(N : ℝ)*L*eta)/t^2
  have hC : 0 < C := div_pos (Real.exp_pos _) (sq_pos_of_pos ht)
  have hCmul : Real.exp ((N : ℝ)*(d-a))*C =
      Real.exp (-(N : ℝ)*L*u+(N : ℝ)*L*eta)/t^2 := by
    calc
      _ = (Real.exp ((N : ℝ)*(d-a))*
          Real.exp (-(N : ℝ)*(d-a)-(N : ℝ)*L*u+(N : ℝ)*L*eta))/t^2 := by dsimp [C]; ring
      _ = _ := by
        rw [← Real.exp_add]
        rw [show (N : ℝ)*(d-a)+
          (-(N : ℝ)*(d-a)-(N : ℝ)*L*u+(N : ℝ)*L*eta) =
          -(N : ℝ)*L*u+(N : ℝ)*L*eta by ring]
  have hpoint (g : Model.Vector N) : signedCommonPartition N a u eta g ≤
      C*CoupledGaussianIntegralProofs.endpointMoment N a d L g := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos ((N : ℝ)*(d-a)))).mp
    calc
      _ ≤ Real.exp (-(N : ℝ)*L*u+(N : ℝ)*L*eta)/t^2 *
          CoupledGaussianIntegralProofs.endpointMoment N a d L g :=
        CoupledRadialEndpointProofs.signed_common_radial_bound hNp ha hd hL hP u eta g
      _ = _ := by rw [← mul_assoc,hCmul]
  obtain ⟨hiZ,H⟩ := CoupledEndpointBoundProofs.log_fractional_moment_mono
    (stdGaussian (Model.Vector N)) (signedCommonPartition N a u eta)
    (CoupledGaussianIntegralProofs.endpointMoment N a d L) hC hp.le
    (signedCommonPartition_pos hN a hu heta)
    (CoupledGaussianIntegralProofs.endpointMoment_pos N ha hd hL hP)
    (signedCommon_log_power_continuous hN a (m/2) hu heta).aestronglyMeasurable
    (CoupledGaussianIntegralProofs.endpoint_outer_integrable N ha hd hL hm hmargin) hpoint
  refine ⟨hiZ,?_⟩
  have hlogC : Real.log C =
      -(N : ℝ)*(d-a)-(N : ℝ)*L*u+(N : ℝ)*L*eta-2*Real.log t := by
    dsimp only [C]
    rw [Real.log_div (Real.exp_ne_zero _) (sq_pos_of_pos ht).ne',Real.log_exp,Real.log_pow]
    norm_num
  have Hn := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right H hp.le) hn.le
  rw [hlogC] at Hn
  have he (J : ℝ) :
      ((m/2)*(-(N : ℝ)*(d-a)-(N : ℝ)*L*u+(N : ℝ)*L*eta-2*Real.log t)+J)/(m/2)/(N : ℝ) =
      -(d-a)-L*u+L*eta-2*Real.log t/(N : ℝ)+J/(m/2)/(N : ℝ) := by
    field_simp [hp.ne',hn.ne']
  rw [he] at Hn
  unfold signedCommonFreshPressure
  change _ ≤ _-L*u+L*eta-2*Real.log t/(N : ℝ)
  linarith

theorem signedCommonFreshPressure_bound {N : ℕ} (hN : 2 ≤ N)
    {a d L m u eta : ℝ} (ha : 0 ≤ a) (hd : a ≤ d) (hL : 0 ≤ L)
    (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L)
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    signedCommonFreshPressure N a d m u eta ≤
      d-L*u+L*eta-(1/2 : ℝ)*Real.log (CoupledMatrixProofs.A3 a L).det+
        (1/m)*Real.log ((1+a-L)/(1+(1-m)*a-L))+
          4*Real.log (1+d)/(N : ℝ)+
            2*RadialTailBounds.tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have H := (signedCommonFreshPressure_le_gaussian hN ha hd hL hm hmargin hu heta).2
  exact H.trans (CoupledEndpointBoundProofs.gaussian_radial_endpoint_numeric_bound
    (by omega) ha hd hL hm hmargin u eta)

theorem signedCommonFreshPressure_uniform_bound {N : ℕ} (hN : 2 ≤ N)
    {a d L m u eta B : ℝ} (ha : 0 ≤ a) (hd : a ≤ d) (hL : L ∈ Icc (0 : ℝ) 1)
    (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L) (hB : 1+d ≤ B)
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    signedCommonFreshPressure N a d m u eta ≤
      d-L*u-(1/2 : ℝ)*Real.log (CoupledMatrixProofs.A3 a L).det+
        (1/m)*Real.log ((1+a-L)/(1+(1-m)*a-L))+
          CoupledEndpointBoundProofs.endpointErrorConstant B*eta+
            CoupledEndpointBoundProofs.endpointErrorConstant B*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have H := (signedCommonFreshPressure_le_gaussian hN ha hd hL.1 hm hmargin hu heta).2
  exact H.trans (CoupledEndpointBoundProofs.gaussian_radial_endpoint_numeric_uniform
    (by omega) ha hd hL hm hmargin hB u heta.le)


end
end TensorPCA.CoupledSignedEndpointProofs
