-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticOrderedPropagation
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSuffixGood
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootEnvelope

/-! The ordered finite spherical log-step tower dominates the conditional joint-good
Gaussian spine. The probability recursion is proved from the Gaussian kernels.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalLower
open MeasureTheory ProbabilityTheory
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticLogSteps
open FiniteGaussianQuadraticSphericalStages FiniteGaussianQuadraticOrderedPropagation
open FiniteGaussianQuadraticSuffixGood FiniteGaussianQuadraticTerminalGood
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sphericalStage_probability_lower {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B C eps : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (hC : 0≤ C) (heps : 0≤ eps) (i : Fin (d+1)) (h : Model.Vector M) :
    suffixGoodProbability M hx hDelta hB C eps i h≤
      Real.exp (stageMass x i*(sphericalStage M x Delta i h-envelope M x Delta B i h-
        (M : ℝ)*((B-1)/2-eps*(C+|B-1|/2)))) :=
  ordered_probability_propagation hM hx hMono hx1 hDelta hB hC heps
    (suffixGoodProbability M hx hDelta hB C eps)
    (suffixGoodProbability_measurable M hx hDelta hB C eps)
    (suffixGoodProbability_mem_Icc M hx hDelta hB C eps)
    (suffixGoodProbability_terminal M hx hDelta hB C eps)
    (suffixGoodProbability_recursion M hx hDelta hB C eps) i h

theorem terminalGoodProbability_le_spherical_root {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B C eps : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (hC : 0≤ C) (heps : 0≤ eps) (h : Model.Vector M) :
    terminalGoodProbability M hx hDelta hB C eps h≤
      Real.exp (stageMass x 0*(sphericalStage M x Delta 0 h-envelope M x Delta B 0 h-
        (M : ℝ)*((B-1)/2-eps*(C+|B-1|/2)))) := by
  have HP := sphericalStage_probability_lower hM hx hMono hx1 hDelta hB hC heps
    (⟨0,Nat.zero_lt_succ d⟩ : Fin (d+1)) h
  simpa only [suffixGoodProbability_zero] using HP

theorem spherical_root_lower_of_good {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B C eps : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (hC : 0≤ C) (heps : 0≤ eps) (h : Model.Vector M)
    (hgood : (1 : ℝ)/2≤terminalGoodProbability M hx hDelta hB C eps h) :
    envelope M x Delta B 0 h+(M : ℝ)*((B-1)/2-eps*(C+|B-1|/2))-
      Real.log 2/stageMass x 0≤sphericalStage M x Delta 0 h := by
  have HM := stageMass_pos hx 0
  have HP := hgood.trans (terminalGoodProbability_le_spherical_root hM hx hMono hx1 hDelta hB hC heps h)
  have HL := Real.log_le_log (by norm_num : (0 : ℝ)<1/2) HP
  rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at HL
  apply (mul_le_mul_iff_right₀ HM).mp
  have heq : (envelope M x Delta B 0 h+(M : ℝ)*((B-1)/2-eps*(C+|B-1|/2))-
      Real.log 2/stageMass x 0)*stageMass x 0=
      stageMass x 0*(envelope M x Delta B 0 h+(M : ℝ)*((B-1)/2-eps*(C+|B-1|/2)))-Real.log 2 := by
    field_simp
    <;> ring
  nlinarith only [HL,heq]

theorem normalized_spherical_root_lower_of_good {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B C eps : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B)
    (hC : 0≤ C) (heps : 0≤ eps) (h : Model.Vector M)
    (hgood : (1 : ℝ)/2≤terminalGoodProbability M hx hDelta hB C eps h) :
    envelope M x Delta B 0 h/(M : ℝ)+((B-1)/2-eps*(C+|B-1|/2))-
      Real.log 2/((M : ℝ)*stageMass x 0)≤sphericalStage M x Delta 0 h/(M : ℝ) := by
  have HM : (0 : ℝ)<M := by exact_mod_cast hM
  have H := div_le_div_of_nonneg_right
    (spherical_root_lower_of_good hM hx hMono hx1 hDelta hB hC heps h hgood) HM.le
  convert H using 1 <;> field_simp <;> ring

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalLower
