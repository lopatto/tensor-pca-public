-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianSideChannelProofs
public import TensorPCA.GaussianChannelInformationProofs

/-! # Bounded-prior channel differentiation with a Gaussian side observation -/
@[expose] public section

namespace TensorPCA.GaussianConditionalChannelDerivativeProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianPosteriorCovarianceProofs GaussianBoundedIMMSEProofs GaussianSideChannelProofs
open scoped RealInnerProductSpace ENNReal Topology

variable {Omega iota D : Type*} [MeasurableSpace Omega] [Fintype iota]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

noncomputable def conditionalFreeEnergy (mu : Measure Omega) [SFinite mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (lam : ℝ) (v : D) : ℝ :=
  mixtureFreeEnergy (posteriorKernel mu B v) (fun x ↦ lam • A x)

noncomputable def conditionalPosteriorSecondMoment (mu : Measure Omega) [SFinite mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (lam : ℝ) (v : D) : ℝ :=
  ∫ z : Omega × EuclideanSpace ℝ iota,
    ‖∫ x, A x ∂combinedPosteriorKernel mu (fun x ↦ lam • A x) B (v,lam • A z.1+z.2)‖^2
      ∂(posteriorKernel mu B v).prod (stdGaussian (EuclideanSpace ℝ iota))

theorem measurable_conditionalFreeEnergy (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (lam : ℝ) : Measurable (conditionalFreeEnergy mu A B lam) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hF : Measurable (fun x ↦ lam • A x) := (continuous_const_smul lam).measurable.comp hA
  have hObs : Measurable (fun p : D × (Omega × EuclideanSpace ℝ iota) ↦
      (p.1, lam • A p.2.1+p.2.2)) :=
    measurable_fst.prodMk (((continuous_const_smul lam).measurable.comp
      (hA.comp measurable_snd.fst)).add measurable_snd.snd)
  have hf := ((measurable_conditionalLikelihood mu (fun x ↦ lam • A x) B hF hB).log.comp hObs).stronglyMeasurable
  have hm := (hf.integral_kernel_prod_right'
    (κ := posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian (EuclideanSpace ℝ iota)))).measurable
  convert hm using 1
  funext v
  rw [Kernel.prod_apply, Kernel.const_apply]
  exact mixtureFreeEnergy_scale_eq_integral (posteriorKernel mu B v) A hA lam

theorem measurable_conditionalPosteriorSecondMoment (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (lam : ℝ) : Measurable (conditionalPosteriorSecondMoment mu A B lam) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hMean : StronglyMeasurable (fun p : D × EuclideanSpace ℝ iota ↦
      ∫ x, A x ∂combinedPosteriorKernel mu (fun x ↦ lam • A x) B p) :=
    hA.stronglyMeasurable.integral_kernel
  have hObs : Measurable (fun p : D × (Omega × EuclideanSpace ℝ iota) ↦
      (p.1, lam • A p.2.1+p.2.2)) :=
    measurable_fst.prodMk (((continuous_const_smul lam).measurable.comp
      (hA.comp measurable_snd.fst)).add measurable_snd.snd)
  have hf := ((hMean.measurable.comp hObs).norm.pow_const 2).stronglyMeasurable
  have hm := (hf.integral_kernel_prod_right'
    (κ := posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian (EuclideanSpace ℝ iota)))).measurable
  convert hm using 1
  funext v
  rw [Kernel.prod_apply, Kernel.const_apply]
  rfl

theorem hasDerivAt_conditionalFreeEnergy [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v : D) :
    HasDerivAt (fun t ↦ conditionalFreeEnergy mu A B t v)
      (lam*conditionalPosteriorSecondMoment mu A B lam v) lam := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hF : Measurable (fun x ↦ lam • A x) := (continuous_const_smul lam).measurable.comp hA
  have hb : ∀ᵐ x ∂posteriorKernel mu B v, ‖A x‖ ≤ K :=
    (posteriorKernel_absolutelyContinuous mu B hB v).ae_le hAB
  have h := hasDerivAt_mixtureFreeEnergy_scale (posteriorKernel mu B v) A hA hK hb lam
  convert h using 1
  · rfl
  · apply congrArg (fun r : ℝ ↦ lam*r)
    unfold conditionalPosteriorSecondMoment
    apply integral_congr_ae
    refine .of_forall fun z ↦ ?_
    change ‖∫ x, A x ∂combinedPosteriorKernel mu (fun x ↦ lam • A x) B (v,lam • A z.1+z.2)‖^2 = _
    rw [combinedPosteriorKernel_apply mu (fun x ↦ lam • A x) B hF hB,
      ← posteriorKernel_apply (posteriorKernel mu B v) (fun x ↦ lam • A x) hF]
    rfl

theorem conditionalPosteriorSecondMoment_bounds (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {K : ℝ} (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v : D) :
    0 ≤ conditionalPosteriorSecondMoment mu A B lam v ∧
      conditionalPosteriorSecondMoment mu A B lam v ≤ K^2 := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hF : Measurable (fun x ↦ lam • A x) := (continuous_const_smul lam).measurable.comp hA
  have hb : ∀ᵐ x ∂posteriorKernel mu B v, ‖A x‖ ≤ K :=
    (posteriorKernel_absolutelyContinuous mu B hB v).ae_le hAB
  have hMean (z : Omega × EuclideanSpace ℝ iota) :
      ‖∫ x, A x ∂combinedPosteriorKernel mu (fun x ↦ lam • A x) B (v,lam • A z.1+z.2)‖ ≤ K := by
    rw [combinedPosteriorKernel_apply mu (fun x ↦ lam • A x) B hF hB,
      ← posteriorKernel_apply (posteriorKernel mu B v) (fun x ↦ lam • A x) hF]
    exact norm_posteriorMean_le (posteriorKernel mu B v) _ hF A hb _
  unfold conditionalPosteriorSecondMoment
  refine ⟨integral_nonneg (fun z ↦ sq_nonneg _), ?_⟩
  have hi := integral_mono_of_nonneg
    (μ := (posteriorKernel mu B v).prod (stdGaussian (EuclideanSpace ℝ iota)))
    (.of_forall fun z : Omega × EuclideanSpace ℝ iota ↦ sq_nonneg
      ‖∫ x, A x ∂combinedPosteriorKernel mu (fun x ↦ lam • A x) B (v,lam • A z.1+z.2)‖)
    (integrable_const (K^2))
    (.of_forall fun z ↦ pow_le_pow_left₀ (norm_nonneg _) (hMean z) 2)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

theorem conditionalFreeEnergy_bounds (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {K : ℝ} (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v : D) :
    0 ≤ conditionalFreeEnergy mu A B lam v ∧ conditionalFreeEnergy mu A B lam v ≤ lam^2*K^2/2 := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hF : Measurable (fun x ↦ lam • A x) := (continuous_const_smul lam).measurable.comp hA
  have hb : ∀ᵐ x ∂posteriorKernel mu B v, ‖A x‖ ≤ K :=
    (posteriorKernel_absolutelyContinuous mu B hB v).ae_le hAB
  have hFB : ∀ᵐ x ∂posteriorKernel mu B v, ‖lam • A x‖ ≤ |lam| * K := by
    filter_upwards [hb] with x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg lam)
  have hF2 : MemLp (fun x ↦ lam • A x) 2 (posteriorKernel mu B v) :=
    MemLp.of_bound hF.aestronglyMeasurable (|lam| * K) hFB
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hi : (∫ x, ‖lam • A x‖^2 ∂posteriorKernel mu B v) ≤ lam^2*K^2 := by
    have hh := integral_mono_ae (hF2.integrable_norm_pow (by decide : 2 ≠ 0)) (integrable_const (lam^2*K^2))
      (hb.mono fun x hx ↦ by
        change ‖lam • A x‖^2 ≤ lam^2*K^2
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) (sq_nonneg lam))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  exact (GaussianChannelInformationProofs.mixtureFreeEnergy_le_half_energy
    (posteriorKernel mu B v) _ hF hF2).trans (by nlinarith)

/-- The remaining noise channel can be differentiated after averaging over
the actual fixed side-output law, with an explicit uniform constant bound. -/
theorem hasDerivAt_integral_conditionalFreeEnergy [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    HasDerivAt (fun t ↦ ∫ v, conditionalFreeEnergy mu A B t v ∂mixtureLaw mu B)
      (lam * ∫ v, conditionalPosteriorSecondMoment mu A B lam v ∂mixtureLaw mu B) lam := by
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have hInt : Integrable (conditionalFreeEnergy mu A B lam) (mixtureLaw mu B) := by
    apply Integrable.of_bound (measurable_conditionalFreeEnergy mu A B hA hB lam).aestronglyMeasurable
      (lam^2*K^2/2)
    exact .of_forall fun v ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (conditionalFreeEnergy_bounds mu A B hA hB hAB lam v).1]
      exact (conditionalFreeEnergy_bounds mu A B hA hB hAB lam v).2
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mixtureLaw mu B) (s := Metric.ball lam 1)
    (F' := fun t v ↦ t*conditionalPosteriorSecondMoment mu A B t v)
    (bound := fun _ ↦ (|lam|+1)*K^2) (Metric.ball_mem_nhds lam zero_lt_one)
    (.of_forall fun t ↦ (measurable_conditionalFreeEnergy mu A B hA hB t).aestronglyMeasurable)
    hInt ((measurable_conditionalPosteriorSecondMoment mu A B hA hB lam).const_mul lam).aestronglyMeasurable
    ?_ (integrable_const _) (.of_forall fun v t _ ↦ hasDerivAt_conditionalFreeEnergy mu A B hA hB hK hAB t v)).2
  · simpa only [integral_const_mul] using h
  · exact .of_forall fun v t ht ↦ by
      have hs := conditionalPosteriorSecondMoment_bounds mu A B hA hB hAB t v
      have ht' := GaussianSpinInterpolation.norm_le_of_mem_ball ht
      simp only [Real.norm_eq_abs] at ht'
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
      exact mul_le_mul ht' hs.2 hs.1 (by positivity)


end TensorPCA.GaussianConditionalChannelDerivativeProofs
