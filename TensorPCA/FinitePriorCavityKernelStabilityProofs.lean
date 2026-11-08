-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityKernelDerivativeProofs
public import TensorPCA.GaussianGibbsChangeOfMeasureProofs
public import TensorPCA.GaussianZeroChannelProofs

/-! Dimension-free Bayesian free-energy comparison from cross kernels. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityKernelStabilityProofs
open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs GaussianSideChannelProofs
open GaussianTwoChannelFreeEnergyProofs GaussianReplicaTransportProofs GaussianReplicaMomentProofs GaussianPosteriorCovarianceProofs
open FinitePriorCavityComparisonProofs FinitePriorCavityKernelDerivativeProofs GaussianGibbsChangeOfMeasureProofs GaussianZeroChannelProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def posteriorPairMean (q : Measure Omega) [IsProbabilityMeasure q] (F : Omega → E)
    (f : Omega × Omega → ℝ) (y : E) : ℝ :=
  ∫ z, f z ∂(posteriorKernel q F y).prod (posteriorKernel q F y)

theorem measurable_posteriorPairMean (q : Measure Omega) [IsProbabilityMeasure q] (F : Omega → E)
    (hF : Measurable F) (f : Omega × Omega → ℝ) (hf : Measurable f) : Measurable (posteriorPairMean q F f) := by
  letI := posteriorKernel_isMarkov q F hF
  have H := hf.stronglyMeasurable.integral_kernel (κ := posteriorKernel q F ×ₖ posteriorKernel q F)
  change Measurable (fun y ↦ ∫ z, f z ∂(posteriorKernel q F y).prod (posteriorKernel q F y))
  simpa only [Kernel.prod_apply] using H.measurable

theorem norm_posteriorPairMean_le (q : Measure Omega) [IsProbabilityMeasure q] (F : Omega → E)
    (hF : Measurable F) (f : Omega × Omega → ℝ) {L : ℝ} (hfL : ∀ z, |f z| ≤ L) (y : E) :
    ‖posteriorPairMean q F f y‖ ≤ L := by
  letI := posteriorKernel_isMarkov q F hF
  simpa only [posteriorPairMean,probReal_univ,mul_one,Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hfL) :
      ‖∫ z, f z ∂(posteriorKernel q F y).prod (posteriorKernel q F y)‖ ≤ L*((posteriorKernel q F y).prod (posteriorKernel q F y)).real Set.univ)

theorem posteriorPairMean_integrable (q : Measure Omega) [IsProbabilityMeasure q] (F : Omega → E)
    (hF : Measurable F) (f : Omega × Omega → ℝ) (hf : Measurable f) {L : ℝ} (hfL : ∀ z, |f z| ≤ L) :
    Integrable (posteriorPairMean q F f) (mixtureLaw q F) := by
  letI := mixtureLaw_probability q F hF
  exact Integrable.of_bound (measurable_posteriorPairMean q F hF f hf).aestronglyMeasurable L
    (Filter.Eventually.of_forall (norm_posteriorPairMean_le q F hF f hfL))

omit [MeasurableSpace Omega] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_planted_bias_le {C : ℝ} (hC : 0 ≤ C) (v shift : E) (hv : ‖v‖ ≤ C) (hs : ‖shift‖ ≤ C) :
    |inner ℝ v shift-‖v‖^2/2| ≤ (3/2 : ℝ)*C^2 := by
  have hi : |inner ℝ v shift| ≤ C^2 :=
    (abs_real_inner_le_norm v shift).trans (by simpa only [pow_two] using mul_le_mul hv hs (norm_nonneg _) hC)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have H := abs_sub_le (inner ℝ v shift) 0 (‖v‖^2/2)
  simp only [sub_zero,zero_sub,abs_neg] at H
  rw [abs_of_nonneg (div_nonneg (sq_nonneg ‖v‖) (by norm_num : (0 : ℝ) ≤ 2))] at H
  linarith only [hi,hsq,H]

theorem posterior_pair_absolute_bound (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C) (hFB : ∀ x, ‖F x‖ ≤ C)
    (f : Omega × Omega → ℝ) (hf : Measurable f) {L : ℝ} (hfL : ∀ z, |f z| ≤ L) :
    (∫ y, posteriorPairMean q F (fun z ↦ |f z|) y ∂mixtureLaw q F) ≤
      Real.exp (22*C^2)*Real.sqrt (∫ z, (f z)^2 ∂q.prod q) := by
  have hf2 : MemLp f 2 (q.prod q) := MemLp.of_bound hf.aestronglyMeasurable L (Filter.Eventually.of_forall hfL)
  have hFixed (X : Omega) :
      (∫ W, posteriorPairMean q F (fun z ↦ |f z|) (F X+W) ∂stdGaussian E) ≤
        Real.exp (22*C^2)*Real.sqrt (∫ z, (f z)^2 ∂q.prod q) := by
    let b : Omega → ℝ := fun x ↦ inner ℝ (F x) (F X)-‖F x‖^2/2
    have hb : Measurable b := (continuous_inner.measurable.comp (hF.prodMk measurable_const)).sub ((hF.norm.pow_const 2).div_const 2)
    have hbB : ∀ᵐ x ∂q, |b x| ≤ (3/2 : ℝ)*C^2 :=
      Filter.Eventually.of_forall (fun x ↦ abs_planted_bias_le hC (F x) (F X) (hFB x) (hFB X))
    have H := tilted_pair_observable_bound q F b hF hb (Filter.Eventually.of_forall hFB) hbB f hf2
    dsimp only [b] at H
    simp_rw [tiltedLaw_eq_posteriorKernel q F hF (F X)] at H
    have he : 4*((3/2 : ℝ)*C^2)+16*C^2 = 22*C^2 := by ring
    simpa only [posteriorPairMean,he] using H
  have hfAbs : Measurable (fun z ↦ |f z|) := by simpa only [Real.norm_eq_abs] using hf.norm
  have hm := measurable_posteriorPairMean q F hF (fun z ↦ |f z|) hfAbs
  have hObs : Measurable (fun z : Omega × E ↦ F z.1+z.2) := (hF.comp measurable_fst).add measurable_snd
  have hi : Integrable (fun z : Omega × E ↦ posteriorPairMean q F (fun z ↦ |f z|) (F z.1+z.2)) (q.prod (stdGaussian E)) :=
    Integrable.of_bound (hm.comp hObs).aestronglyMeasurable L (Filter.Eventually.of_forall
      (fun z ↦ norm_posteriorPairMean_le q F hF (fun z ↦ |f z|) (fun z ↦ by simpa only [abs_abs] using hfL z) (F z.1+z.2)))
  unfold mixtureLaw
  rw [integral_map hObs.aemeasurable hm.aestronglyMeasurable,integral_prod _ hi]
  have H := integral_mono_ae hi.integral_prod_left (integrable_const (Real.exp (22*C^2)*Real.sqrt (∫ z, (f z)^2 ∂q.prod q)))
    (Filter.Eventually.of_forall hFixed)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem posterior_pair_expectation_bound (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C) (hFB : ∀ x, ‖F x‖ ≤ C)
    (f : Omega × Omega → ℝ) (hf : Measurable f) {L : ℝ} (hfL : ∀ z, |f z| ≤ L) :
    |∫ y, posteriorPairMean q F f y ∂mixtureLaw q F| ≤
      Real.exp (22*C^2)*Real.sqrt (∫ z, (f z)^2 ∂q.prod q) := by
  have hfAbs : Measurable (fun z ↦ |f z|) := by simpa only [Real.norm_eq_abs] using hf.norm
  have hi := posteriorPairMean_integrable q F hF f hf hfL
  have hiAbs := posteriorPairMean_integrable q F hF (fun z ↦ |f z|) hfAbs
    (fun z ↦ by simpa only [abs_abs] using hfL z)
  have hInner (y : E) : |posteriorPairMean q F f y| ≤ posteriorPairMean q F (fun z ↦ |f z|) y :=
    abs_integral_le_integral_abs
  calc
    _ ≤ ∫ y, |posteriorPairMean q F f y| ∂mixtureLaw q F := abs_integral_le_integral_abs
    _ ≤ ∫ y, posteriorPairMean q F (fun z ↦ |f z|) y ∂mixtureLaw q F :=
      integral_mono_ae hi.abs hiAbs (Filter.Eventually.of_forall hInner)
    _ ≤ _ := posterior_pair_absolute_bound q F hF hC hFB f hf hfL

section Kernel
variable {iota kappa : Type*} [Fintype iota] [Fintype kappa] [DecidableEq iota] [DecidableEq kappa]

theorem measurable_kernelDifference (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) : Measurable (kernelDifference A B) :=
  (continuous_inner.measurable.comp ((hA.comp measurable_fst).prodMk (hA.comp measurable_snd))).sub
    (continuous_inner.measurable.comp ((hB.comp measurable_fst).prodMk (hB.comp measurable_snd)))

theorem abs_kernelDifference_le (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, ‖B x‖ ≤ CB)
    (p : Omega × Omega) : |kernelDifference A B p| ≤ CA^2+CB^2 := by
  have h1 : |inner ℝ (A p.1) (A p.2)| ≤ CA^2 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [pow_two] using mul_le_mul (hbA p.1) (hbA p.2) (norm_nonneg _) hCA)
  have h2 : |inner ℝ (B p.1) (B p.2)| ≤ CB^2 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [pow_two] using mul_le_mul (hbB p.1) (hbB p.2) (norm_nonneg _) hCB)
  have H := abs_sub_le (inner ℝ (A p.1) (A p.2)) 0 (inner ℝ (B p.1) (B p.2))
  simp only [sub_zero,zero_sub,abs_neg] at H
  exact H.trans (add_le_add h1 h2)

/-- The actual posterior cross-kernel expectation along the true Bayesian
interpolation is controlled by its base-law L2 error, uniformly in the parameter
and ambient Gaussian dimensions. -/
theorem guerraPath_kernel_bound (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, ‖B x‖ ≤ CB) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |∫ y, ∫ p, kernelDifference A B p
      ∂(posteriorKernel q (interpolatedSignal A B t) y).prod (posteriorKernel q (interpolatedSignal A B t) y)
      ∂mixtureLaw q (interpolatedSignal A B t)| ≤
      Real.exp (22*(CA+CB)^2)*Real.sqrt (∫ p, (kernelDifference A B p)^2 ∂q.prod q) := by
  exact posterior_pair_expectation_bound q (interpolatedSignal A B t) (measurable_interpolatedSignal A B hA hB t)
    (add_nonneg hCA hCB) (interpolatedSignal_norm_le A B hCA hCB hbA hbB ht)
    (kernelDifference A B) (measurable_kernelDifference A B hA hB) (abs_kernelDifference_le A B hCA hCB hbA hbB)
end Kernel

end
end TensorPCA.FinitePriorCavityKernelStabilityProofs
