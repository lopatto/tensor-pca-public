-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepTiltMoment

/-! Gaussian log-step terminal stability with a normalized density envelope independent
of the terminal, its additive constant and the center.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianStepWeightedStability
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianStepLipschitz OneStepGaussianStepTiltMoment
open GaussianPowerMomentBounds
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def densityEnvelope (N : ℕ) (c : ℝ) (g : Model.Vector N) : ℝ :=
  Real.exp (c*‖g‖)/(∫z : Model.Vector N,Real.exp (-c*‖z‖)∂stdGaussian (Model.Vector N))

theorem gaussian_exp_norm_integrable (N : ℕ) (c : ℝ) :
    Integrable (fun g : Model.Vector N => Real.exp (c*‖g‖)) (stdGaussian (Model.Vector N)) := by
  simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using
    SYK.integrable_exp_mul_norm (ι := Fin N) c

theorem gaussian_norm_exp_norm_integrable (N : ℕ) (c : ℝ) :
    Integrable (fun g : Model.Vector N => ‖g‖*Real.exp (c*‖g‖)) (stdGaussian (Model.Vector N)) := by
  simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using
    norm_mul_exp_integrable (ι := Fin N) c

theorem densityEnvelope_nonneg (N : ℕ) (c : ℝ) (g : Model.Vector N) :
    0≤densityEnvelope N c g := by
  exact div_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem shifted_difference_growth {N : ℕ} {L K : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N→L[ℝ]E) (x : E) (g : Model.Vector N) :
    |F (x+T g)-G (x+T g)|≤(|F x|+|G x|)+((L : ℝ)+(K : ℝ))*‖T‖*‖g‖ := by
  have H := (abs_sub (F (x+T g)) (G (x+T g))).trans
    (add_le_add (shifted_linear_growth hF T x g) (shifted_linear_growth hG T x g))
  linarith

theorem weighted_difference_integrable {N : ℕ} {L K : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) :
    Integrable (fun g : Model.Vector N =>
      Real.exp (mass*F (x+T g))*|F (x+T g)-G (x+T g)|) (stdGaussian (Model.Vector N)) := by
  let C := |F x|+|G x|
  let D := ((L : ℝ)+(K : ℝ))*‖T‖
  have hi := ((shifted_exp_integrable hF T mass x).const_mul C).add
    ((weighted_norm_integrable hF T mass x le_rfl).const_mul D)
  have hFm : Continuous (fun g : Model.Vector N => F (x+T g)) :=
    hF.continuous.comp (continuous_const.add T.continuous)
  have hGm : Continuous (fun g : Model.Vector N => G (x+T g)) :=
    hG.continuous.comp (continuous_const.add T.continuous)
  apply hi.mono' (((Real.continuous_exp.comp (hFm.const_mul mass)).mul (hFm.sub hGm).abs).aestronglyMeasurable)
  apply ae_of_all
  intro g
  change ‖Real.exp (mass*F (x+T g))*|F (x+T g)-G (x+T g)|‖≤
    C*Real.exp (mass*F (x+T g))+D*(Real.exp (mass*F (x+T g))*‖g‖)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp (mass*F (x+T g))*(C+D*‖g‖) :=
      mul_le_mul_of_nonneg_left (shifted_difference_growth hF hG T x g) (Real.exp_pos _).le
    _ = _ := by dsimp only [C,D,Pi.add_apply]; ring

theorem signed_weighted_difference_integrable {N : ℕ} {L K : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) :
    Integrable (fun g : Model.Vector N =>
      Real.exp (mass*F (x+T g))*(F (x+T g)-G (x+T g))) (stdGaussian (Model.Vector N)) := by
  have hFm : Continuous (fun g : Model.Vector N => F (x+T g)) :=
    hF.continuous.comp (continuous_const.add T.continuous)
  have hGm : Continuous (fun g : Model.Vector N => G (x+T g)) :=
    hG.continuous.comp (continuous_const.add T.continuous)
  apply (weighted_difference_integrable hF hG T mass x).mono'
    (((Real.continuous_exp.comp (hFm.const_mul mass)).mul (hFm.sub hGm)).aestronglyMeasurable)
  apply ae_of_all
  intro g
  change ‖Real.exp (mass*F (x+T g))*(F (x+T g)-G (x+T g))‖≤
    Real.exp (mass*F (x+T g))*|F (x+T g)-G (x+T g)|
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]

/-- Exponential tangent inequality under the F tilt.
-/
theorem logNormalizer_sub_le_weighted_difference {N : ℕ} {L K : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) :
    Real.log (gaussianNormalizer T mass F x)-Real.log (gaussianNormalizer T mass G x)≤
      mass*(∫g : Model.Vector N,normalizedWeight T mass F x g*(F (x+T g)-G (x+T g))
        ∂stdGaussian (Model.Vector N)) := by
  let ZF := gaussianNormalizer T mass F x
  let ZG := gaussianNormalizer T mass G x
  let C := Real.log ZF-Real.log ZG
  let I := ∫g : Model.Vector N,Real.exp (mass*F (x+T g))*(F (x+T g)-G (x+T g))
    ∂stdGaussian (Model.Vector N)
  have hZF : 0<ZF := gaussianNormalizer_pos hF T mass x
  have hZG : 0<ZG := gaussianNormalizer_pos hG T mass x
  have hInt := (signed_weighted_difference_integrable hF hG T mass x).const_mul mass
  have hLeft := ((shifted_exp_integrable hF T mass x).const_mul (1+C)).sub hInt
  have hRight := (shifted_exp_integrable hG T mass x).const_mul (Real.exp C)
  have H := integral_mono hLeft hRight (fun g => by
    have HE := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (mass*(G (x+T g)-F (x+T g))+C)) (Real.exp_pos (mass*F (x+T g))).le
    have hExp : Real.exp (mass*(G (x+T g)-F (x+T g))+C)*Real.exp (mass*F (x+T g))=
        Real.exp C*Real.exp (mass*G (x+T g)) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    rw [hExp] at HE
    convert HE using 1 <;> dsimp only [Pi.sub_apply] <;> ring)
  simp only [Pi.sub_apply] at H
  rw [integral_sub ((shifted_exp_integrable hF T mass x).const_mul (1+C)) hInt,
    integral_const_mul,integral_const_mul,integral_const_mul] at H
  change (1+C)*ZF-mass*I≤Real.exp C*ZG at H
  have hExpC : Real.exp C=ZF/ZG := by
    dsimp only [C]
    rw [Real.exp_sub,Real.exp_log hZF,Real.exp_log hZG]
  rw [hExpC,div_mul_cancel₀ _ hZG.ne'] at H
  have hW : (∫g : Model.Vector N,normalizedWeight T mass F x g*(F (x+T g)-G (x+T g))
      ∂stdGaussian (Model.Vector N))=I/ZF := by
    rw [← integral_div]
    apply integral_congr_ae
    apply ae_of_all
    intro g
    dsimp only [normalizedWeight,ZF,I]
    ring
  rw [hW]
  change C≤mass*(I/ZF)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hZF).mpr
  change C*ZF≤mass*I
  linarith

theorem densityEnvelope_pos (N : ℕ) (c : ℝ) (g : Model.Vector N) :
    0<densityEnvelope N c g :=
  div_pos (Real.exp_pos _) (integral_exp_pos (gaussian_exp_norm_integrable N (-c)))

theorem envelope_difference_integrable {N : ℕ} {L K : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N→L[ℝ]E) (c : ℝ) (x : E) :
    Integrable (fun g : Model.Vector N => densityEnvelope N c g*|F (x+T g)-G (x+T g)|)
      (stdGaussian (Model.Vector N)) := by
  let lo := ∫g : Model.Vector N,Real.exp (-c*‖g‖)∂stdGaussian (Model.Vector N)
  let C := |F x|+|G x|
  let D := ((L : ℝ)+(K : ℝ))*‖T‖
  have hlo : 0<lo := integral_exp_pos (gaussian_exp_norm_integrable N (-c))
  have hi := (((gaussian_exp_norm_integrable N c).const_mul C).add
    ((gaussian_norm_exp_norm_integrable N c).const_mul D)).div_const lo
  have hFm : Continuous (fun g : Model.Vector N => F (x+T g)) :=
    hF.continuous.comp (continuous_const.add T.continuous)
  have hGm : Continuous (fun g : Model.Vector N => G (x+T g)) :=
    hG.continuous.comp (continuous_const.add T.continuous)
  have hD : Continuous (fun g : Model.Vector N => densityEnvelope N c g) :=
    (Real.continuous_exp.comp (continuous_norm.const_mul c)).div_const lo
  apply hi.mono' (hD.mul (hFm.sub hGm).abs).aestronglyMeasurable
  apply ae_of_all
  intro g
  change ‖(Real.exp (c*‖g‖)/lo)*|F (x+T g)-G (x+T g)|‖≤
    (C*Real.exp (c*‖g‖)+D*(‖g‖*Real.exp (c*‖g‖)))/lo
  rw [Real.norm_of_nonneg (by positivity)]
  have HP := mul_le_mul_of_nonneg_left (shifted_difference_growth hF hG T x g)
    (Real.exp_pos (c*‖g‖)).le
  have HR : Real.exp (c*‖g‖)*|F (x+T g)-G (x+T g)|≤
      C*Real.exp (c*‖g‖)+D*(‖g‖*Real.exp (c*‖g‖)) := HP.trans_eq (by dsimp only [C,D]; ring)
  convert div_le_div_of_nonneg_right HR hlo.le using 1 <;> ring

theorem normalized_difference_abs_le {N : ℕ} {L : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G)
    (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) {c : ℝ}
    (hc : |mass| *(L : ℝ)*‖T‖≤c) :
    |∫g : Model.Vector N,normalizedWeight T mass F x g*(F (x+T g)-G (x+T g))
      ∂stdGaussian (Model.Vector N)|≤
      ∫g : Model.Vector N,densityEnvelope N c g*|F (x+T g)-G (x+T g)|
        ∂stdGaussian (Model.Vector N) := by
  have hZF := gaussianNormalizer_pos hF T mass x
  have hAbs : Integrable (fun g : Model.Vector N =>
      normalizedWeight T mass F x g*|F (x+T g)-G (x+T g)|) (stdGaussian (Model.Vector N)) := by
    convert (weighted_difference_integrable hF hG T mass x).div_const (gaussianNormalizer T mass F x) using 1
    funext g
    dsimp only [normalizedWeight]
    ring
  calc
    _ ≤ ∫g : Model.Vector N,|normalizedWeight T mass F x g*(F (x+T g)-G (x+T g))|
        ∂stdGaussian (Model.Vector N) := abs_integral_le_integral_abs
    _ = ∫g : Model.Vector N,normalizedWeight T mass F x g*|F (x+T g)-G (x+T g)|
        ∂stdGaussian (Model.Vector N) := by
      apply integral_congr_ae
      apply ae_of_all
      intro g
      dsimp only
      have hw : 0≤normalizedWeight T mass F x g := div_nonneg (Real.exp_pos _).le hZF.le
      rw [abs_mul,abs_of_nonneg hw]
    _ ≤ _ := integral_mono hAbs (envelope_difference_integrable hF hG T c x)
      (fun g => mul_le_mul_of_nonneg_right (normalizedWeight_le hF T mass x hc g) (abs_nonneg _))

/-- Center-independent, mass-uniform terminal stability. All integrability
and positive-normalizer clauses are consequences of the Lipschitz inputs. -/
theorem gaussianLogStep_weighted_stability {N : ℕ} {L : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G)
    (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) {c : ℝ}
    (hc : |mass| *(L : ℝ)*‖T‖≤c) :
    |gaussianLogStep T mass F x-gaussianLogStep T mass G x|≤
      ∫g : Model.Vector N,densityEnvelope N c g*|F (x+T g)-G (x+T g)|
        ∂stdGaussian (Model.Vector N) := by
  by_cases hm : mass=0
  · subst mass
    simp only [gaussianLogStep,↓reduceIte]
    rw [← integral_sub (shifted_integrable hF T x) (shifted_integrable hG T x)]
    simpa [normalizedWeight,gaussianNormalizer] using normalized_difference_abs_le hF hG T 0 x hc
  let R := ∫g : Model.Vector N,densityEnvelope N c g*|F (x+T g)-G (x+T g)|
    ∂stdGaussian (Model.Vector N)
  let muF := ∫g : Model.Vector N,normalizedWeight T mass F x g*(F (x+T g)-G (x+T g))
    ∂stdGaussian (Model.Vector N)
  let muG := ∫g : Model.Vector N,normalizedWeight T mass G x g*(G (x+T g)-F (x+T g))
    ∂stdGaussian (Model.Vector N)
  have hFbound : |muF|≤R := normalized_difference_abs_le hF hG T mass x hc
  have hGbound : |muG|≤R := by
    simpa only [abs_sub_comm] using normalized_difference_abs_le hG hF T mass x hc
  have hFU : mass*muF≤|mass| *R := calc
    _ ≤ |mass*muF| := le_abs_self _
    _ = |mass| *|muF| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hFbound (abs_nonneg mass)
  have hGU : mass*muG≤|mass| *R := calc
    _ ≤ |mass*muG| := le_abs_self _
    _ = |mass| *|muG| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hGbound (abs_nonneg mass)
  have hFT := (logNormalizer_sub_le_weighted_difference hF hG T mass x).trans hFU
  have hGT := (logNormalizer_sub_le_weighted_difference hG hF T mass x).trans hGU
  have hAbs : |Real.log (gaussianNormalizer T mass F x)-Real.log (gaussianNormalizer T mass G x)|≤|mass| *R :=
    abs_le.mpr ⟨by linarith,hFT⟩
  simp only [gaussianLogStep,if_neg hm]
  rw [← sub_div,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hm)).mpr (by simpa only [R,mul_comm] using hAbs)

theorem gaussianLogStep_weighted_stability_unit_mass {N : ℕ} {L : ℝ≥0} {F G : E→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G)
    (T : Model.Vector N→L[ℝ]E) {mass : ℝ} (hmass : |mass|≤1) (x : E) :
    |gaussianLogStep T mass F x-gaussianLogStep T mass G x|≤
      ∫g : Model.Vector N,densityEnvelope N ((L : ℝ)*‖T‖) g*|F (x+T g)-G (x+T g)|
        ∂stdGaussian (Model.Vector N) := by
  apply gaussianLogStep_weighted_stability hF hG T mass x
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass L.coe_nonneg) (norm_nonneg T)


end
end TensorPCA.NonRSLowerProofs.OneStepGaussianStepWeightedStability
