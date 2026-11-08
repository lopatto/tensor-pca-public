-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledGaussianIntegralProofs
public import TensorPCA.ChiSquareTailProofs

/-! Numerical and logarithmic estimates for the coupled Gaussian endpoint and its Gaussian radial tail. -/
@[expose] public section
namespace TensorPCA.CoupledEndpointBoundProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem actual_tail_log_cost {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    -2*Real.log ((stdGaussian (Model.Vector N)).real
        {g | (N : ℝ)*b ≤ ‖g‖^2})/(N : ℝ) ≤
      b-1-Real.log b+4*Real.log b/(N : ℝ)+
        2*RadialTailBounds.tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have H := (ChiSquareTailProofs.chiSquare_tail_lower hN hb).2
  change -(1/2 : ℝ)*(b-1-Real.log b)-2*Real.log b/(N : ℝ)-
    RadialTailBounds.tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      (1/(N : ℝ))*Real.log ((stdGaussian (Model.Vector N)).real
        {g | (N : ℝ)*b ≤ ‖g‖^2}) at H
  ring_nf at H ⊢
  linarith

def endpointErrorConstant (B : ℝ) : ℝ :=
  1+2*RadialTailBounds.tailLogConstant+4*Real.log B/Real.log 2

theorem endpointErrorConstant_pos {B : ℝ} (hB : 1 ≤ B) : 0 < endpointErrorConstant B := by
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold endpointErrorConstant
  have H := RadialTailBounds.tailLogConstant_pos
  positivity

theorem endpointErrorConstant_ge_one {B : ℝ} (hB : 1 ≤ B) :
    1 ≤ endpointErrorConstant B := by
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have H := RadialTailBounds.tailLogConstant_pos
  have hcoef : 0 ≤ 4*Real.log B/Real.log 2 := div_nonneg (by positivity) hlog2.le
  unfold endpointErrorConstant
  linarith

theorem uniform_endpoint_error {N : ℕ} (hN : 0 < N) {b B : ℝ}
    (hb : 1 ≤ b) (hbB : b ≤ B) :
    4*Real.log b/(N : ℝ)+
      2*RadialTailBounds.tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
        endpointErrorConstant B*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (hb.trans hbB)
  have hlogb : Real.log b ≤ Real.log B := Real.log_le_log (by linarith) hbB
  have hlogN : Real.log 2 ≤ Real.log ((N : ℝ)+1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hcoef : 0 ≤ 4*Real.log B/Real.log 2 := div_nonneg (by positivity) hlog2.le
  have H := mul_le_mul_of_nonneg_left hlogN hcoef
  rw [div_mul_cancel₀ _ hlog2.ne'] at H
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  unfold endpointErrorConstant
  nlinarith [hlogN]

theorem exp_mul_log_mono_bound {Z I C p : ℝ} (hZ : 0 < Z) (hI : 0 < I)
    (hC : 0 < C) (hp : 0 ≤ p) (hbound : Z ≤ C*I) :
    Real.exp (p*Real.log Z) ≤ Real.exp (p*Real.log C)*Real.exp (p*Real.log I) := by
  have H := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.log_le_log hZ hbound) hp)
  rw [Real.log_mul hC.ne' hI.ne',mul_add,Real.exp_add] at H
  exact H

theorem log_fractional_moment_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z I : Ω → ℝ)
    {C p : ℝ} (hC : 0 < C) (hp : 0 ≤ p)
    (hZ : ∀ x, 0 < Z x) (hI : ∀ x, 0 < I x)
    (hZm : AEStronglyMeasurable (fun x => Real.exp (p*Real.log (Z x))) μ)
    (hiI : Integrable (fun x => Real.exp (p*Real.log (I x))) μ)
    (hbound : ∀ x, Z x ≤ C*I x) :
    Integrable (fun x => Real.exp (p*Real.log (Z x))) μ ∧
      Real.log (∫ x, Real.exp (p*Real.log (Z x)) ∂μ) ≤
        p*Real.log C+Real.log (∫ x, Real.exp (p*Real.log (I x)) ∂μ) := by
  have hpoint (x : Ω) := exp_mul_log_mono_bound (hZ x) (hI x) hC hp (hbound x)
  have hiR := hiI.const_mul (Real.exp (p*Real.log C))
  have hiZ : Integrable (fun x => Real.exp (p*Real.log (Z x))) μ := by
    apply hiR.mono' hZm
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpoint x
  refine ⟨hiZ,?_⟩
  have H := Real.log_le_log (integral_exp_pos hiZ) (integral_mono hiZ hiR hpoint)
  rw [integral_const_mul,
    Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos hiI).ne',Real.log_exp] at H
  exact H

theorem gaussian_radial_endpoint_numeric_bound {N : ℕ} (hN : 0 < N)
    {a d L m : ℝ} (ha : 0 ≤ a) (hd : a ≤ d) (hL : 0 ≤ L) (hm : 1 ≤ m)
    (hmargin : 0 < 1+(1-m)*a-L) (u eta : ℝ) :
    Real.log (∫ g, Real.exp ((m/2)*Real.log
      (CoupledGaussianIntegralProofs.endpointMoment N a d L g))
      ∂stdGaussian (Model.Vector N))/(m/2)/(N : ℝ)-L*u+L*eta-
        2*Real.log ((stdGaussian (Model.Vector N)).real
          {g | (N : ℝ)*(1+d) ≤ ‖g‖^2})/(N : ℝ) ≤
      d-L*u+L*eta-(1/2 : ℝ)*Real.log (CoupledMatrixProofs.A3 a L).det+
        (1/m)*Real.log ((1+a-L)/(1+(1-m)*a-L))+
          4*Real.log (1+d)/(N : ℝ)+
            2*RadialTailBounds.tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  rw [CoupledGaussianIntegralProofs.endpoint_outer_log_normalized hN ha hd hL hm hmargin]
  have H := actual_tail_log_cost hN (show 1 ≤ 1+d by linarith)
  ring_nf at H ⊢
  linarith

theorem gaussian_radial_endpoint_numeric_uniform {N : ℕ} (hN : 0 < N)
    {a d L m B : ℝ} (ha : 0 ≤ a) (hd : a ≤ d) (hL : L ∈ Icc (0 : ℝ) 1)
    (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L) (hB : 1+d ≤ B)
    (u : ℝ) {eta : ℝ} (heta : 0 ≤ eta) :
    Real.log (∫ g, Real.exp ((m/2)*Real.log
      (CoupledGaussianIntegralProofs.endpointMoment N a d L g))
      ∂stdGaussian (Model.Vector N))/(m/2)/(N : ℝ)-L*u+L*eta-
        2*Real.log ((stdGaussian (Model.Vector N)).real
          {g | (N : ℝ)*(1+d) ≤ ‖g‖^2})/(N : ℝ) ≤
      d-L*u-(1/2 : ℝ)*Real.log (CoupledMatrixProofs.A3 a L).det+
        (1/m)*Real.log ((1+a-L)/(1+(1-m)*a-L))+
          endpointErrorConstant B*eta+
            endpointErrorConstant B*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have hb : 1 ≤ 1+d := by linarith
  have H := gaussian_radial_endpoint_numeric_bound hN ha hd hL.1 hm hmargin u eta
  have He := uniform_endpoint_error hN hb hB
  have HL : L*eta ≤ endpointErrorConstant B*eta :=
    mul_le_mul_of_nonneg_right (hL.2.trans (endpointErrorConstant_ge_one (hb.trans hB))) heta
  linarith


end
end TensorPCA.CoupledEndpointBoundProofs
