-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLinearMGF
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticStep

/-! Depth-uniform propagation of two affine exponential error barriers through the
Gaussian log step. No mass gap is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianAffineBarrier
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz OneStepGaussianStepTiltMoment
open OneStepGaussianStepWeightedStability OneStepGaussianTiltLinearMGF
open FiniteGaussianQuadraticStep
open scoped RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def affineBarrier {N : ℕ} (lambda : Model.Vector N) (b a : ℝ) (x : Model.Vector N) : ℝ :=
  b*Real.exp (inner ℝ lambda x)+a*Real.exp (inner ℝ (-lambda) x)

theorem affineBarrier_nonneg {N : ℕ} (lambda : Model.Vector N) {b a : ℝ}
    (hb : 0≤b) (ha : 0≤a) (x : Model.Vector N) : 0≤affineBarrier lambda b a x := by
  exact add_nonneg (mul_nonneg hb (Real.exp_pos _).le) (mul_nonneg ha (Real.exp_pos _).le)

theorem affineBarrier_scale {N : ℕ} (lambda : Model.Vector N) (r b a : ℝ) (x : Model.Vector N) :
    affineBarrier lambda (r*b) (r*a) x=r*affineBarrier lambda b a x := by
  unfold affineBarrier
  ring

theorem isotropic_state_exp_integrable {N : ℕ} {L : ℝ≥0} {K : Model.Vector N→ℝ}
    (hK : LipschitzWith L K) (Delta mass : ℝ) (x lambda : Model.Vector N) :
    Integrable (fun g : Model.Vector N => Real.exp (inner ℝ lambda (x+shift N Delta g)))
      (gaussianTilt (shift N Delta) mass K x) := by
  convert (tilted_linear_exp_integrable hK (shift N Delta) mass x (Real.sqrt Delta •lambda)).const_mul
    (Real.exp (inner ℝ lambda x)) using 1
  funext g
  simp only [shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    inner_add_right,inner_smul_right,real_inner_smul_left,Real.exp_add]

theorem isotropic_state_exp_mgf_le {N : ℕ} {L : ℝ≥0} {K : Model.Vector N→ℝ}
    (hK : LipschitzWith L K) {Delta : ℝ} (hDelta : 0≤Delta)
    (mass : ℝ) (x lambda : Model.Vector N) :
    (∫g : Model.Vector N,Real.exp (inner ℝ lambda (x+shift N Delta g))
      ∂gaussianTilt (shift N Delta) mass K x)≤
      Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖)*Real.exp (inner ℝ lambda x) := by
  have H := isotropic_tilted_linear_mgf_le hK hDelta mass x lambda
  calc
    _ = Real.exp (inner ℝ lambda x)*(∫g : Model.Vector N,
        Real.exp (inner ℝ lambda (Real.sqrt Delta •g))∂gaussianTilt (shift N Delta) mass K x) := by
      simp_rw [inner_add_right,Real.exp_add]
      exact integral_const_mul _ _
    _ ≤ Real.exp (inner ℝ lambda x)*Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖) :=
      mul_le_mul_of_nonneg_left H (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem isotropic_barrier_integrable {N : ℕ} {L : ℝ≥0} {K : Model.Vector N→ℝ}
    (hK : LipschitzWith L K) (Delta mass : ℝ) (x lambda : Model.Vector N) (b a : ℝ) :
    Integrable (fun g : Model.Vector N => affineBarrier lambda b a (x+shift N Delta g))
      (gaussianTilt (shift N Delta) mass K x) :=
  ((isotropic_state_exp_integrable hK Delta mass x lambda).const_mul b).add
    ((isotropic_state_exp_integrable hK Delta mass x (-lambda)).const_mul a)

theorem isotropic_barrier_mgf_le {N : ℕ} {L : ℝ≥0} {K : Model.Vector N→ℝ}
    (hK : LipschitzWith L K) {Delta : ℝ} (hDelta : 0≤Delta)
    (mass : ℝ) (x lambda : Model.Vector N) {b a : ℝ} (hb : 0≤b) (ha : 0≤a) :
    (∫g : Model.Vector N,affineBarrier lambda b a (x+shift N Delta g)
      ∂gaussianTilt (shift N Delta) mass K x)≤
      Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖)*affineBarrier lambda b a x := by
  have HP := isotropic_state_exp_mgf_le hK hDelta mass x lambda
  have HN := isotropic_state_exp_mgf_le hK hDelta mass x (-lambda)
  simp only [norm_neg] at HN
  unfold affineBarrier
  rw [integral_add ((isotropic_state_exp_integrable hK Delta mass x lambda).const_mul b)
    ((isotropic_state_exp_integrable hK Delta mass x (-lambda)).const_mul a),integral_const_mul,integral_const_mul]
  have H := add_le_add (mul_le_mul_of_nonneg_left HP hb) (mul_le_mul_of_nonneg_left HN ha)
  exact H.trans_eq (by ring)

theorem normalized_difference_abs_le_affineBarrier {N : ℕ} {L : ℝ≥0} {F G : Model.Vector N→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G) {Delta : ℝ} (hDelta : 0≤Delta)
    (mass : ℝ) (x lambda : Model.Vector N) {b a : ℝ} (hb : 0≤b) (ha : 0≤a)
    (hFG : ∀y,|F y-G y|≤affineBarrier lambda b a y) :
    |∫g : Model.Vector N,normalizedWeight (shift N Delta) mass F x g*
      (F (x+shift N Delta g)-G (x+shift N Delta g))∂stdGaussian (Model.Vector N)|≤
      Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖)*affineBarrier lambda b a x := by
  have hEq : (∫g : Model.Vector N,normalizedWeight (shift N Delta) mass F x g*
      (F (x+shift N Delta g)-G (x+shift N Delta g))∂stdGaussian (Model.Vector N))=
      ∫g : Model.Vector N,(F (x+shift N Delta g)-G (x+shift N Delta g))
        ∂gaussianTilt (shift N Delta) mass F x := by
    unfold gaussianTilt
    rw [integral_tilted]
    rfl
  have hAbs : Integrable (fun g : Model.Vector N => |F (x+shift N Delta g)-G (x+shift N Delta g)|)
      (gaussianTilt (shift N Delta) mass F x) := by
    apply (integrable_tilted_iff (shifted_exp_integrable hF (shift N Delta) mass x) _).mpr
    simpa only [smul_eq_mul] using weighted_difference_integrable hF hG (shift N Delta) mass x
  rw [hEq]
  calc
    _ ≤ ∫g : Model.Vector N,|F (x+shift N Delta g)-G (x+shift N Delta g)|
        ∂gaussianTilt (shift N Delta) mass F x := abs_integral_le_integral_abs
    _ ≤ ∫g : Model.Vector N,affineBarrier lambda b a (x+shift N Delta g)
        ∂gaussianTilt (shift N Delta) mass F x :=
      integral_mono hAbs (isotropic_barrier_integrable hF Delta mass x lambda b a) (fun g => hFG _)
    _ ≤ _ := isotropic_barrier_mgf_le hF hDelta mass x lambda hb ha

theorem gaussianLogStep_affineBarrier {N : ℕ} {L : ℝ≥0} {F G : Model.Vector N→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G) {Delta : ℝ} (hDelta : 0≤Delta)
    (mass : ℝ) (x lambda : Model.Vector N) {b a : ℝ} (hb : 0≤b) (ha : 0≤a)
    (hFG : ∀y,|F y-G y|≤affineBarrier lambda b a y) :
    |gaussianLogStep (shift N Delta) mass F x-gaussianLogStep (shift N Delta) mass G x|≤
      Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖)*affineBarrier lambda b a x := by
  have hFB := normalized_difference_abs_le_affineBarrier hF hG hDelta mass x lambda hb ha hFG
  have hGB := normalized_difference_abs_le_affineBarrier hG hF hDelta mass x lambda hb ha
    (fun y => by simpa only [abs_sub_comm] using hFG y)
  by_cases hm : mass=0
  · subst mass
    simp only [gaussianLogStep,↓reduceIte]
    rw [← integral_sub (shifted_integrable hF (shift N Delta) x) (shifted_integrable hG (shift N Delta) x)]
    simpa [normalizedWeight,gaussianNormalizer] using hFB
  let R := Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖)*affineBarrier lambda b a x
  have hFU : mass*(∫g : Model.Vector N,normalizedWeight (shift N Delta) mass F x g*
      (F (x+shift N Delta g)-G (x+shift N Delta g))∂stdGaussian (Model.Vector N))≤|mass| *R :=
    (le_abs_self _).trans ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left hFB (abs_nonneg mass)))
  have hGU : mass*(∫g : Model.Vector N,normalizedWeight (shift N Delta) mass G x g*
      (G (x+shift N Delta g)-F (x+shift N Delta g))∂stdGaussian (Model.Vector N))≤|mass| *R :=
    (le_abs_self _).trans ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left hGB (abs_nonneg mass)))
  have H1 := (logNormalizer_sub_le_weighted_difference hF hG (shift N Delta) mass x).trans hFU
  have H2 := (logNormalizer_sub_le_weighted_difference hG hF (shift N Delta) mass x).trans hGU
  have HA : |Real.log (gaussianNormalizer (shift N Delta) mass F x)-
      Real.log (gaussianNormalizer (shift N Delta) mass G x)|≤|mass| *R := abs_le.mpr ⟨by linarith,H1⟩
  simp only [gaussianLogStep,if_neg hm]
  rw [← sub_div,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hm)).mpr (by simpa only [R,mul_comm] using HA)

theorem gaussianLogStep_affineBarrier_unit_mass {N : ℕ} {L : ℝ≥0} {F G : Model.Vector N→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G) {Delta mass : ℝ} (hDelta : 0≤Delta)
    (hmass : |mass|≤1) (x lambda : Model.Vector N) (hLambda : ‖lambda‖≤(L : ℝ))
    {b a : ℝ} (hb : 0≤b) (ha : 0≤a)
    (hFG : ∀y,|F y-G y|≤affineBarrier lambda b a y) :
    |gaussianLogStep (shift N Delta) mass F x-gaussianLogStep (shift N Delta) mass G x|≤
      Real.exp (3/2*(L : ℝ)^2*Delta)*affineBarrier lambda b a x := by
  have hNormSq : ‖lambda‖^2≤(L : ℝ)^2 := by nlinarith [norm_nonneg lambda,L.coe_nonneg]
  have hVar := mul_le_mul_of_nonneg_left hNormSq hDelta
  have hMass : |mass| *(L : ℝ)≤(L : ℝ) := by nlinarith [L.coe_nonneg]
  have hDrift := mul_le_mul
    (mul_le_mul_of_nonneg_right hMass hDelta) hLambda (norm_nonneg lambda) (mul_nonneg L.coe_nonneg hDelta)
  have hExp : Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖)≤
      Real.exp (3/2*(L : ℝ)^2*Delta) := Real.exp_le_exp.mpr (by nlinarith)
  exact (gaussianLogStep_affineBarrier hF hG hDelta mass x lambda hb ha hFG).trans
    (mul_le_mul_of_nonneg_right hExp (affineBarrier_nonneg lambda hb ha x))

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianAffineBarrier
