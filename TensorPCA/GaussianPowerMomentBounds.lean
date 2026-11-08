-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPowerGibbsProofs

/-! Uniform common-disorder norm moments for bounded-feature Gaussian power tilts. -/
@[expose] public section
namespace TensorPCA.GaussianPowerMomentBounds
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι]

theorem norm_mul_exp_integrable (c : ℝ) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖g‖*Real.exp (c*‖g‖))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc : Continuous (fun g : EuclideanSpace ℝ ι ↦ ‖g‖*Real.exp (c*‖g‖)) := by fun_prop
  apply (SYK.integrable_exp_mul_norm (c+1)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun g ↦ by
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    have he : ‖g‖ ≤ Real.exp ‖g‖ := by linarith [Real.add_one_le_exp ‖g‖]
    exact (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans_eq (by
      rw [← Real.exp_add]
      congr 1
      ring))

def gaussianTiltNormBound (ι : Type*) [Fintype ι] (c : ℝ) : ℝ :=
  (∫ g : EuclideanSpace ℝ ι, ‖g‖*Real.exp (c*‖g‖) ∂SYK.standardGaussianMeasureOnEuclidean ι) /
    (∫ g : EuclideanSpace ℝ ι, Real.exp (-c*‖g‖) ∂SYK.standardGaussianMeasureOnEuclidean ι)

theorem gaussianTiltNormBound_nonneg (c : ℝ) : 0 ≤ gaussianTiltNormBound ι c := by
  exact div_nonneg (integral_nonneg (fun g ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))
    (integral_nonneg (fun _ ↦ (Real.exp_pos _).le))

theorem powerWeight_ge_exp_neg_norm (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) (g : EuclideanSpace ℝ ι) :
    Real.exp (-(|p| *K)*‖g‖) ≤ powerWeight ν L p g := by
  have habs : |p*logPartition ν L g| ≤ (|p| *K)*‖g‖ := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_logPartition_le ν L hL hb g) (abs_nonneg p)
  apply Real.exp_le_exp.mpr
  have H := (neg_le_neg habs).trans (neg_abs_le (p*logPartition ν L g))
  simpa only [neg_mul] using H

theorem powerWeight_mul_norm_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    Integrable (fun g ↦ powerWeight ν L p g*‖g‖) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply (norm_mul_exp_integrable (|p| *K)).mono'
    ((powerWeight_contDiff ν L hL hK hb p).continuous.mul continuous_norm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun g ↦ by
    change ‖powerWeight ν L p g*‖g‖‖ ≤ ‖g‖*Real.exp ((|p| *K)*‖g‖)
    rw [Real.norm_of_nonneg (mul_nonneg (powerWeight_pos ν L p g).le (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (powerWeight_le_exp_norm ν L hL hb p g) (norm_nonneg _)).trans_eq
      (mul_comm _ _))

theorem powerTilt_norm_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    Integrable (fun g ↦ ‖g‖) (powerTilt ν L p) := by
  have hz := powerWeight_integral_pos ν L hL hK hb p
  have hm := ((powerWeight_contDiff ν L hL hK hb p).continuous.measurable.div_const
    (∫ g, powerWeight ν L p g ∂SYK.standardGaussianMeasureOnEuclidean ι)).ennreal_ofReal
  unfold powerTilt
  apply (integrable_withDensity_iff hm (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mpr
  apply ((powerWeight_mul_norm_integrable ν L hL hK hb p).div_const
    (∫ g, powerWeight ν L p g ∂SYK.standardGaussianMeasureOnEuclidean ι)).congr
  exact Filter.Eventually.of_forall (fun g ↦ by
    change (powerWeight ν L p g*‖g‖)/(∫ u, powerWeight ν L p u ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      ‖g‖*(ENNReal.ofReal (powerWeight ν L p g/
        (∫ u, powerWeight ν L p u ∂SYK.standardGaussianMeasureOnEuclidean ι))).toReal
    rw [ENNReal.toReal_ofReal (div_pos (powerWeight_pos ν L p g) hz).le]
    ring)

theorem powerTilt_norm_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    (∫ g, ‖g‖ ∂powerTilt ν L p) ≤ gaussianTiltNormBound ι (|p| *K) := by
  have hz := powerWeight_integral_pos ν L hL hK hb p
  have hlo : 0 < ∫ g : EuclideanSpace ℝ ι, Real.exp (-(|p| *K)*‖g‖)
      ∂SYK.standardGaussianMeasureOnEuclidean ι := integral_exp_pos
    (SYK.integrable_exp_mul_norm (-(|p| *K)))
  have hden := integral_mono_ae (SYK.integrable_exp_mul_norm (-(|p| *K)))
    (powerWeight_integrable ν L hL hK hb p)
      (Filter.Eventually.of_forall (powerWeight_ge_exp_neg_norm ν L hL hb p))
  have hnum := integral_mono_ae (powerWeight_mul_norm_integrable ν L hL hK hb p)
    (norm_mul_exp_integrable (|p| *K)) (Filter.Eventually.of_forall (fun g ↦
      (mul_le_mul_of_nonneg_right (powerWeight_le_exp_norm ν L hL hb p g) (norm_nonneg _)).trans_eq
        (mul_comm _ _)))
  rw [powerTilt_integral_eq ν L hL hK hb p]
  exact (div_le_div_of_nonneg_right hnum hz.le).trans
    (div_le_div_of_nonneg_left
      (integral_nonneg (fun g ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)) hlo hden)

end
end TensorPCA.GaussianPowerMomentBounds
