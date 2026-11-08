-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- Centered finite-step tilt argument adapted from CascadeDerivPi.lean at
-- pmaronow/arbitrary-rsb-palomar@5162e2d15b440ce46fd322f20eb429468d601948
-- (Apache-2.0). Uses the existing exact Gaussian norm-moment envelope.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz
public import TensorPCA.GaussianPowerMomentBounds
public import Mathlib.MeasureTheory.Measure.Tilted

/-! Uniform Gaussian tilt moments for arbitrary Lipschitz terminals. The center and the
terminal's additive constant cancel from the normalized density. The Gaussian shift
can take values in any real normed space.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianStepTiltMoment
open MeasureTheory ProbabilityTheory Filter OneStepGaussianStepLipschitz
open GaussianPowerMomentBounds
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianTilt {N : ℕ} (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (F : E → ℝ) (x : E) :
    Measure (Model.Vector N) :=
  (stdGaussian (Model.Vector N)).tilted (fun g ↦ mass*F (x+T g))

def normalizedWeight {N : ℕ} (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (F : E → ℝ)
    (x : E) (g : Model.Vector N) : ℝ := Real.exp (mass*F (x+T g))/gaussianNormalizer T mass F x

private theorem exp_norm_integrable (N : ℕ) (c : ℝ) :
    Integrable (fun g : Model.Vector N ↦ Real.exp (c*‖g‖)) (stdGaussian (Model.Vector N)) := by
  simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] using
    SYK.integrable_exp_mul_norm (ι := Fin N) c

private theorem norm_exp_integrable (N : ℕ) (c : ℝ) :
    Integrable (fun g : Model.Vector N ↦ ‖g‖*Real.exp (c*‖g‖)) (stdGaussian (Model.Vector N)) := by
  simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] using
    norm_mul_exp_integrable (ι := Fin N) c

theorem exp_center_bounds {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) {c : ℝ}
    (hc : |mass| *(L : ℝ)*‖T‖ ≤ c) (g : Model.Vector N) :
    Real.exp (mass*F x)*Real.exp (-c*‖g‖) ≤ Real.exp (mass*F (x+T g)) ∧
      Real.exp (mass*F (x+T g)) ≤ Real.exp (mass*F x)*Real.exp (c*‖g‖) := by
  have h : |mass*(F (x+T g)-F x)| ≤ c*‖g‖ := by
    rw [abs_mul]
    calc
      _ ≤ |mass| *((L : ℝ)*‖T‖*‖g‖) :=
        mul_le_mul_of_nonneg_left (shifted_deviation hF T x g) (abs_nonneg mass)
      _ = (|mass| *(L : ℝ)*‖T‖)*‖g‖ := by ring
      _ ≤ c*‖g‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg g)
  constructor <;> rw [← Real.exp_add] <;> apply Real.exp_le_exp.mpr
  · nlinarith [(abs_le.mp h).1]
  · nlinarith [(abs_le.mp h).2]

theorem normalizedWeight_le {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) {c : ℝ}
    (hc : |mass| *(L : ℝ)*‖T‖ ≤ c) (g : Model.Vector N) :
    normalizedWeight T mass F x g ≤ Real.exp (c*‖g‖)/
      (∫ z : Model.Vector N, Real.exp (-c*‖z‖) ∂stdGaussian (Model.Vector N)) := by
  have hz := gaussianNormalizer_pos hF T mass x
  have hlo := integral_exp_pos (exp_norm_integrable N (-c))
  have he := Real.exp_pos (mass*F x)
  have hden : Real.exp (mass*F x)*
      (∫ z : Model.Vector N, Real.exp (-c*‖z‖) ∂stdGaussian (Model.Vector N)) ≤
        gaussianNormalizer T mass F x := by
    unfold gaussianNormalizer
    rw [← integral_const_mul]
    exact integral_mono ((exp_norm_integrable N (-c)).const_mul _)
      (shifted_exp_integrable hF T mass x) (fun z ↦ (exp_center_bounds hF T mass x hc z).1)
  unfold normalizedWeight
  calc
    _ ≤ (Real.exp (mass*F x)*Real.exp (c*‖g‖))/gaussianNormalizer T mass F x :=
      div_le_div_of_nonneg_right (exp_center_bounds hF T mass x hc g).2 hz.le
    _ ≤ (Real.exp (mass*F x)*Real.exp (c*‖g‖))/(Real.exp (mass*F x)*
        (∫ z : Model.Vector N, Real.exp (-c*‖z‖) ∂stdGaussian (Model.Vector N))) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos he hlo) hden
    _ = _ := by field_simp [he.ne',hlo.ne']

theorem gaussianTilt_probability {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) :
    IsProbabilityMeasure (gaussianTilt T mass F x) :=
  isProbabilityMeasure_tilted (shifted_exp_integrable hF T mass x)

theorem weighted_norm_integrable {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) {c : ℝ}
    (hc : |mass| *(L : ℝ)*‖T‖ ≤ c) :
    Integrable (fun g : Model.Vector N ↦ Real.exp (mass*F (x+T g))*‖g‖)
      (stdGaussian (Model.Vector N)) := by
  have hi := (norm_exp_integrable N c).const_mul (Real.exp (mass*F x))
  have hA : Continuous (fun g : Model.Vector N ↦ mass*F (x+T g)) :=
    (hF.continuous.comp (continuous_const.add T.continuous)).const_mul mass
  apply hi.mono' ((Real.continuous_exp.comp hA).mul continuous_norm).aestronglyMeasurable
  apply Eventually.of_forall
  intro g
  change ‖Real.exp (mass*F (x+T g))*‖g‖‖ ≤ Real.exp (mass*F x)*(‖g‖*Real.exp (c*‖g‖))
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (mass*F (x+T g))*‖g‖)]
  exact (mul_le_mul_of_nonneg_right (exp_center_bounds hF T mass x hc g).2 (norm_nonneg g)).trans_eq
    (by ring)

theorem gaussianTilt_norm_integrable {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) :
    Integrable (fun g : Model.Vector N ↦ ‖g‖) (gaussianTilt T mass F x) := by
  unfold gaussianTilt
  apply (integrable_tilted_iff (shifted_exp_integrable hF T mass x) (fun g ↦ ‖g‖)).mpr
  simpa only [smul_eq_mul] using weighted_norm_integrable hF T mass x (le_refl (|mass| *(L : ℝ)*‖T‖))

theorem gaussianTilt_norm_integral_le {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) {c : ℝ}
    (hc : |mass| *(L : ℝ)*‖T‖ ≤ c) :
    (∫ g : Model.Vector N, ‖g‖ ∂gaussianTilt T mass F x) ≤ gaussianTiltNormBound (Fin N) c := by
  let lo := ∫ z : Model.Vector N, Real.exp (-c*‖z‖) ∂stdGaussian (Model.Vector N)
  have hleft : Integrable (fun g : Model.Vector N ↦ normalizedWeight T mass F x g*‖g‖)
      (stdGaussian (Model.Vector N)) := by
    apply ((weighted_norm_integrable hF T mass x hc).div_const (gaussianNormalizer T mass F x)).congr
    exact Eventually.of_forall (fun g ↦ by dsimp only [normalizedWeight]; ring)
  have hright : Integrable (fun g : Model.Vector N ↦ (Real.exp (c*‖g‖)/lo)*‖g‖)
      (stdGaussian (Model.Vector N)) := by
    apply ((norm_exp_integrable N c).div_const lo).congr
    exact Eventually.of_forall (fun g ↦ by dsimp only; ring)
  have hm := integral_mono hleft hright (fun g ↦
    mul_le_mul_of_nonneg_right (normalizedWeight_le hF T mass x hc g) (norm_nonneg g))
  have heq : (fun g : Model.Vector N ↦ (Real.exp (c*‖g‖)/lo)*‖g‖) =
      (fun g ↦ (‖g‖*Real.exp (c*‖g‖))/lo) := by funext g; ring
  rw [heq,integral_div] at hm
  have htilt : (∫ g : Model.Vector N, ‖g‖ ∂gaussianTilt T mass F x) =
      ∫ g : Model.Vector N, normalizedWeight T mass F x g*‖g‖ ∂stdGaussian (Model.Vector N) := by
    unfold gaussianTilt
    rw [integral_tilted]
    rfl
  rw [htilt]
  convert hm using 1
  unfold gaussianTiltNormBound lo
  simp only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]

theorem gaussianTilt_norm_integral_le_exact {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) :
    (∫ g : Model.Vector N, ‖g‖ ∂gaussianTilt T mass F x) ≤
      gaussianTiltNormBound (Fin N) (|mass| *(L : ℝ)*‖T‖) :=
  gaussianTilt_norm_integral_le hF T mass x le_rfl

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianStepTiltMoment
