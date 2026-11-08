-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz
public import TensorPCA.NonRSUpperProofs.GaussianNormConcentration
public import Mathlib.Analysis.Convex.Integral

/-! A sharp small-mass bound for the literal Gaussian log step. All integrability and
positive-normalizer facts follow from the terminal Lipschitz bound; the zero-mass
step is the Gaussian mean.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianStepSmallMass
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianStepLipschitz
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem shifted_lipschitz {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E) (x : E) :
    LipschitzWith ((L : ℝ)*‖T‖).toNNReal (fun g ↦ F (x+T g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg (norm_nonneg T))]
  have H := hF.dist_le_mul (x+T g) (x+T h)
  have HT : dist (x+T g) (x+T h) ≤ ‖T‖*dist g h := by
    simpa only [dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub] using T.le_opNorm (g-h)
  exact H.trans ((mul_le_mul_of_nonneg_left HT L.coe_nonneg).trans_eq (by ring))

theorem gaussianLogStep_sub_zero_bounds {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E)
    {mass : ℝ} (hmass : 0 ≤ mass) (x : E) :
    0 ≤ gaussianLogStep T mass F x-gaussianLogStep T 0 F x ∧
      gaussianLogStep T mass F x-gaussianLogStep T 0 F x ≤
        mass*(L : ℝ)^2*‖T‖^2/2 := by
  by_cases hm : mass = 0
  · subst mass
    simp
  have hmass' : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hm)
  let mean := ∫ g : Model.Vector N, F (x+T g) ∂stdGaussian (Model.Vector N)
  have hInt := shifted_integrable hF T x
  have hExp := shifted_exp_integrable hF T mass x
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ ↦ Set.mem_univ _)) (hInt.const_mul mass) hExp
  rw [integral_const_mul] at hJ
  have hLow : mass*mean ≤ Real.log (gaussianNormalizer T mass F x) := by
    have H := Real.log_le_log (Real.exp_pos _) hJ
    simpa only [Real.log_exp,gaussianNormalizer,mean] using H
  have hMGF := NonRSUpperProofs.GaussianNormConcentration.centered_lipschitz_mgf_le
    (fun g : Model.Vector N ↦ F (x+T g))
    (mul_nonneg L.coe_nonneg (norm_nonneg T)) (shifted_lipschitz hF T x) mass
  have hM : (∫ g : Model.Vector N, Real.exp (mass*(F (x+T g)-mean))
      ∂stdGaussian (Model.Vector N)) ≤ Real.exp (((L : ℝ)*‖T‖)^2*mass^2/2) := by
    simpa only [mgf,SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian,mean] using hMGF
  have hCenter : gaussianNormalizer T mass F x = Real.exp (mass*mean)*
      (∫ g : Model.Vector N, Real.exp (mass*(F (x+T g)-mean)) ∂stdGaussian (Model.Vector N)) := by
    rw [← integral_const_mul]
    unfold gaussianNormalizer
    congr 1
    funext g
    rw [← Real.exp_add]
    congr 1
    ring
  have hUpExp : gaussianNormalizer T mass F x ≤
      Real.exp (mass*mean+((L : ℝ)*‖T‖)^2*mass^2/2) := by
    rw [hCenter,Real.exp_add]
    exact mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
  have hUp := Real.log_le_log (gaussianNormalizer_pos hF T mass x) hUpExp
  rw [Real.log_exp] at hUp
  simp only [gaussianLogStep,if_neg hm,if_pos rfl]
  change 0 ≤ Real.log (gaussianNormalizer T mass F x)/mass-mean ∧
    Real.log (gaussianNormalizer T mass F x)/mass-mean ≤ mass*(L : ℝ)^2*‖T‖^2/2
  constructor
  · exact sub_nonneg.mpr ((le_div_iff₀ hmass').mpr (by simpa only [mul_comm] using hLow))
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hmass').mpr
    nlinarith

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianStepSmallMass
