-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianConditionalChannelDerivativeProofs

/-! # Two-channel free energy and conditional decomposition -/
@[expose] public section

namespace TensorPCA.GaussianTwoChannelFreeEnergyProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianMixtureStabilityProofs GaussianPosteriorIBPProofs GaussianSideChannelProofs
open GaussianConditionalChannelDerivativeProofs
open scoped RealInnerProductSpace ENNReal

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem abs_logLikelihood_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) {K : ℝ} (hK : 0 ≤ K)
    (hFB : ∀ᵐ x ∂mu, ‖F x‖ ≤ K) (y : E) :
    |Real.log (mixtureLikelihood mu F y)| ≤ (K+K^2)*(‖y‖+1) := by
  rw [← moment_augmentedField mu F y]
  change |GaussianSpinInterpolation.logPartition mu (augmentedField F) (y,-(1:ℝ)/2)| ≤ _
  apply (GaussianSpinInterpolation.abs_logPartition_le mu (augmentedField F)
    (measurable_augmentedField F hF) (augmentedField_ae_bound mu F hK hFB) (y,-(1:ℝ)/2)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Prod.norm_def]
  apply max_le
  · linarith
  · norm_num
    linarith [norm_nonneg y]

theorem integrable_logLikelihood_experiment (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) {K : ℝ} (hFB : ∀ᵐ x ∂mu, ‖F x‖ ≤ K) :
    Integrable (fun z : Omega × E ↦ Real.log (mixtureLikelihood mu F (F z.1+z.2)))
      (mu.prod (stdGaussian E)) := by
  have hF2 : MemLp F 2 mu := MemLp.of_bound hF.aestronglyMeasurable K hFB
  have hL := (measurable_mixtureLikelihood mu F hF).log
  have hObs : Measurable (fun z : Omega × E ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  exact (integrable_map_measure hL.aestronglyMeasurable hObs.aemeasurable).mp
    (integrable_mixtureLogLikelihood mu F hF hF2)

theorem mixtureFreeEnergy_eq_integral_experiment (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    mixtureFreeEnergy mu F = ∫ z : Omega × E,
      Real.log (mixtureLikelihood mu F (F z.1+z.2)) ∂mu.prod (stdGaussian E) := by
  have hL := (measurable_mixtureLikelihood mu F hF).log
  have hObs : Measurable (fun z : Omega × E ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  rw [mixtureFreeEnergy_eq_integral mu F hF, mixtureLaw,
    integral_map hObs.aemeasurable hL.aestronglyMeasurable]

theorem integral_abs_logLikelihood_experiment_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) {K : ℝ} (hK : 0 ≤ K)
    (hFB : ∀ᵐ x ∂mu, ‖F x‖ ≤ K) :
    (∫ z : Omega × E, |Real.log (mixtureLikelihood mu F (F z.1+z.2))| ∂mu.prod (stdGaussian E)) ≤
      (K+K^2)*(K+(∫ w : E, ‖w‖ ∂stdGaussian E)+1) := by
  have hn : Integrable (fun w : E ↦ ‖w‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have hBInt : Integrable (fun z : Omega × E ↦ (K+K^2)*(K+‖z.2‖+1)) (mu.prod (stdGaussian E)) :=
    (((integrable_const K).add (hn.comp_snd mu)).add (integrable_const 1)).const_mul _
  have hz : ∀ᵐ z : Omega × E ∂mu.prod (stdGaussian E), ‖F z.1‖ ≤ K :=
    Measure.quasiMeasurePreserving_fst.ae hFB
  have hbound : ∀ᵐ z : Omega × E ∂mu.prod (stdGaussian E),
      |Real.log (mixtureLikelihood mu F (F z.1+z.2))| ≤ (K+K^2)*(K+‖z.2‖+1) := by
    filter_upwards [hz] with z hz
    have hnorm : ‖F z.1+z.2‖+1 ≤ K+‖z.2‖+1 := by
      linarith [norm_add_le (F z.1) z.2]
    exact (abs_logLikelihood_le mu F hF hK hFB (F z.1+z.2)).trans
      (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hh := integral_mono_ae (integrable_logLikelihood_experiment mu F hF hFB).abs hBInt
    hbound
  rw [integral_const_mul, integral_add ((integrable_const K).fun_add (hn.comp_snd mu)) (integrable_const 1),
    integral_add (integrable_const K) (hn.comp_snd mu)] at hh
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_fun_snd] using hh

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

/-- The literal log partition along the actual two independent noisy
observations, averaged over their common planted signal and both noises. -/
noncomputable def twoChannelFreeEnergy (mu : Measure Omega) (A : Omega → E) (B : Omega → D) : ℝ :=
  ∫ z : (Omega × D) × E,
    Real.log (combinedLikelihood mu A B (A z.1.1+z.2) (B z.1.1+z.1.2))
      ∂(mu.prod (stdGaussian D)).prod (stdGaussian E)

theorem integrable_sideConditionalLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) :
    Integrable (fun p : D × (Omega × E) ↦
      Real.log (mixtureLikelihood (posteriorKernel mu B p.1) A (A p.2.1+p.2.2)))
      ((mixtureLaw mu B) ⊗ₘ (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E))) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have hObs : Measurable (fun p : D × (Omega × E) ↦ (p.1,A p.2.1+p.2.2)) :=
    measurable_fst.prodMk ((hA.comp measurable_snd.fst).add measurable_snd.snd)
  have hf : Measurable (fun p : D × (Omega × E) ↦
      Real.log (mixtureLikelihood (posteriorKernel mu B p.1) A (A p.2.1+p.2.2))) := by
    simpa only [Function.comp_def] using (measurable_conditionalLikelihood mu A B hA hB).log.comp hObs
  refine (Measure.integrable_compProd_iff hf.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine .of_forall fun v ↦ ?_
    rw [Kernel.prod_apply, Kernel.const_apply]
    exact integrable_logLikelihood_experiment (posteriorKernel mu B v) A hA
      ((posteriorKernel_absolutelyContinuous mu B hB v).ae_le hAB)
  · have hm := hf.norm.stronglyMeasurable.integral_kernel_prod_right'
      (κ := posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E))
    apply Integrable.of_bound hm.aestronglyMeasurable
      ((K+K^2)*(K+(∫ w : E, ‖w‖ ∂stdGaussian E)+1))
    refine .of_forall fun v ↦ ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun z ↦ norm_nonneg _), Kernel.prod_apply, Kernel.const_apply]
    simpa only [Real.norm_eq_abs] using integral_abs_logLikelihood_experiment_le
      (posteriorKernel mu B v) A hA hK ((posteriorKernel_absolutelyContinuous mu B hB v).ae_le hAB)

/-- Exact chain decomposition of the literal actual two-channel free energy.
Every log integrability premise is discharged from bounded measurable signals. -/
theorem twoChannelFreeEnergy_eq_conditional (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA)
    (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) :
    twoChannelFreeEnergy mu A B = mixtureFreeEnergy mu B +
      ∫ v, mixtureFreeEnergy (posteriorKernel mu B v) A ∂mixtureLaw mu B := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  let kappa := posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E)
  let side := (mixtureLaw mu B) ⊗ₘ kappa
  have hL := (measurable_mixtureLikelihood mu B hB).log
  have hIntL := integrable_mixtureLogLikelihood mu B hB (MemLp.of_bound hB.aestronglyMeasurable KB hBB)
  have hFirst : Integrable (fun p : D × (Omega × E) ↦ Real.log (mixtureLikelihood mu B p.1)) side := by
    have hf : Measurable (fun p : D × (Omega × E) ↦ Real.log (mixtureLikelihood mu B p.1)) :=
      hL.comp measurable_fst
    refine (Measure.integrable_compProd_iff (μ := mixtureLaw mu B) (κ := kappa)
      hf.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact .of_forall fun v ↦ by
        change Integrable (fun _ : Omega × E ↦ Real.log (mixtureLikelihood mu B v)) (kappa v)
        exact integrable_const _
    · simpa only [integral_const, probReal_univ, one_smul] using hIntL.norm
  have hSecond := integrable_sideConditionalLogLikelihood mu A B hA hB hKA hAB
  have hSide : (∫ p : D × (Omega × E),
      Real.log (combinedLikelihood mu A B (A p.2.1+p.2.2) p.1) ∂side) =
      mixtureFreeEnergy mu B + ∫ v, mixtureFreeEnergy (posteriorKernel mu B v) A ∂mixtureLaw mu B := by
    calc
      _ = ∫ p : D × (Omega × E), Real.log (mixtureLikelihood mu B p.1) +
          Real.log (mixtureLikelihood (posteriorKernel mu B p.1) A (A p.2.1+p.2.2)) ∂side :=
        integral_congr_ae (.of_forall fun p ↦ log_combinedLikelihood_factor mu A B hA hB _ _)
      _ = (∫ p : D × (Omega × E), Real.log (mixtureLikelihood mu B p.1) ∂side) +
          ∫ p : D × (Omega × E),
            Real.log (mixtureLikelihood (posteriorKernel mu B p.1) A (A p.2.1+p.2.2)) ∂side :=
        integral_add hFirst hSecond
      _ = _ := by
        rw [Measure.integral_compProd hFirst, Measure.integral_compProd hSecond]
        simp only [integral_const, probReal_univ, one_smul, Kernel.prod_apply, Kernel.const_apply]
        rw [← mixtureFreeEnergy_eq_integral mu B hB]
        congr 1
        apply integral_congr_ae
        exact .of_forall fun v ↦ (mixtureFreeEnergy_eq_integral_experiment (posteriorKernel mu B v) A hA).symm
  have hM : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,(z.1.1,z.2))) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk (measurable_fst.fst.prodMk measurable_snd)
  have hPair : Measurable (fun p : D × (Omega × E) ↦ (A p.2.1+p.2.2,p.1)) :=
    ((hA.comp measurable_snd.fst).add measurable_snd.snd).prodMk measurable_fst
  have hLog : Measurable (fun p : D × (Omega × E) ↦
      Real.log (combinedLikelihood mu A B (A p.2.1+p.2.2) p.1)) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      (measurable_combinedLikelihood mu A B hA hB).log.comp hPair
  rw [show side = (mixtureLaw mu B) ⊗ₘ
    (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E)) from rfl,
    sideExperiment_eq_actualLaw mu B hB, integral_map hM.aemeasurable hLog.aestronglyMeasurable] at hSide
  exact hSide

theorem hasDerivAt_twoChannelFreeEnergy_scale {iota : Type*} [Fintype iota]
    [StandardBorelSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA)
    (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) (lam : ℝ) :
    HasDerivAt (fun t ↦ twoChannelFreeEnergy mu (fun x ↦ t • A x) B)
      (lam * ∫ v, conditionalPosteriorSecondMoment mu A B lam v ∂mixtureLaw mu B) lam := by
  have h := (hasDerivAt_integral_conditionalFreeEnergy mu A B hA hB hKA hAB lam).const_add
    (mixtureFreeEnergy mu B)
  convert h using 1
  funext t
  have hF : Measurable (fun x ↦ t • A x) := (continuous_const_smul t).measurable.comp hA
  have hFB : ∀ᵐ x ∂mu, ‖t • A x‖ ≤ |t| * KA := by
    filter_upwards [hAB] with x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  exact twoChannelFreeEnergy_eq_conditional mu (fun x ↦ t • A x) B hF hB
    (mul_nonneg (abs_nonneg t) hKA) hFB hBB


end TensorPCA.GaussianTwoChannelFreeEnergyProofs
