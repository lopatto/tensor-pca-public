-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianTwoChannelFreeEnergyProofs

/-! # Joint calculus for the two channel strengths -/
@[expose] public section

namespace TensorPCA.GaussianTwoStrengthCalculusProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianPosteriorIBPProofs GaussianBoundedChannelDerivativeProofs GaussianSideChannelProofs
open GaussianTwoChannelFreeEnergyProofs GaussianSpinInterpolation
open scoped RealInnerProductSpace

variable {Omega E D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

noncomputable def doubleField (A : Omega → E) (B : Omega → D) (x : Omega) :
    ((E × ℝ) × (D × ℝ)) →L[ℝ] ℝ :=
  (augmentedField A x).comp (ContinuousLinearMap.fst ℝ (E × ℝ) (D × ℝ)) +
    (augmentedField B x).comp (ContinuousLinearMap.snd ℝ (E × ℝ) (D × ℝ))

theorem doubleField_apply (A : Omega → E) (B : Omega → D) (x : Omega) (u : (E × ℝ) × (D × ℝ)) :
    doubleField A B x u = inner ℝ (A x) u.1.1+‖A x‖^2*u.1.2 +
      (inner ℝ (B x) u.2.1+‖B x‖^2*u.2.2) := by
  simp [doubleField, augmentedField_apply]

theorem measurable_doubleField (A : Omega → E) (B : Omega → D)
    (hA : Measurable A) (hB : Measurable B) : Measurable (doubleField A B) := by
  have h1 : Continuous (fun f : (E × ℝ) →L[ℝ] ℝ ↦
      f.comp (ContinuousLinearMap.fst ℝ (E × ℝ) (D × ℝ))) := continuous_id.clm_comp continuous_const
  have h2 : Continuous (fun f : (D × ℝ) →L[ℝ] ℝ ↦
      f.comp (ContinuousLinearMap.snd ℝ (E × ℝ) (D × ℝ))) := continuous_id.clm_comp continuous_const
  exact (h1.measurable.comp (measurable_augmentedField A hA)).add
    (h2.measurable.comp (measurable_augmentedField B hB))

theorem norm_doubleField_le (A : Omega → E) (B : Omega → D) (x : Omega) :
    ‖doubleField A B x‖ ≤ (‖A x‖+‖A x‖^2)+(‖B x‖+‖B x‖^2) := by
  unfold doubleField
  apply (norm_add_le ((augmentedField A x).comp (ContinuousLinearMap.fst ℝ (E × ℝ) (D × ℝ)))
    ((augmentedField B x).comp (ContinuousLinearMap.snd ℝ (E × ℝ) (D × ℝ)))).trans
  apply add_le_add
  · exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ (E × ℝ) (D × ℝ)))).trans
      (norm_augmentedField_le A x)
  · exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ (E × ℝ) (D × ℝ)))).trans
      (norm_augmentedField_le B x)

noncomputable def doubleInput (p : ℝ × ℝ) (z : (Omega × D) × E)
    (A : Omega → E) (B : Omega → D) : (E × ℝ) × (D × ℝ) :=
  (plantedInput p.1 (A z.1.1) z.2, plantedInput p.2 (B z.1.1) z.1.2)

theorem moment_doubleInput (mu : Measure Omega) (A : Omega → E) (B : Omega → D)
    (p : ℝ × ℝ) (z : (Omega × D) × E) :
    GaussianSpinInterpolation.moment mu (fun _ ↦ 1) (doubleField A B) (doubleInput p z A B) =
      combinedLikelihood mu (fun x ↦ p.1 • A x) (fun x ↦ p.2 • B x)
        (p.1 • A z.1.1+z.2) (p.2 • B z.1.1+z.1.2) := by
  unfold GaussianSpinInterpolation.moment combinedLikelihood
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simp only [weight, one_mul, doubleField_apply, doubleInput, plantedInput, mixtureWeight,
      inner_add_right, real_inner_smul_left, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Real.exp_add]
    congr 1
    ring

theorem twoChannelFreeEnergy_eq_doublePartition (mu : Measure Omega)
    (A : Omega → E) (B : Omega → D) (p : ℝ × ℝ) :
    twoChannelFreeEnergy mu (fun x ↦ p.1 • A x) (fun x ↦ p.2 • B x) =
      ∫ z : (Omega × D) × E, logPartition mu (doubleField A B) (doubleInput p z A B)
        ∂(mu.prod (stdGaussian D)).prod (stdGaussian E) := by
  unfold twoChannelFreeEnergy logPartition
  apply integral_congr_ae
  exact .of_forall fun z ↦ congrArg Real.log (moment_doubleInput mu A B p z).symm

noncomputable def doubleInputDerivative (p : ℝ × ℝ) (z : (Omega × D) × E)
    (A : Omega → E) (B : Omega → D) : (ℝ × ℝ) →L[ℝ] ((E × ℝ) × (D × ℝ)) :=
  (((ContinuousLinearMap.toSpanSingleton ℝ (plantedInputDerivative p.1 (A z.1.1) z.2)).comp
    (ContinuousLinearMap.fst ℝ ℝ ℝ))).prod
  ((ContinuousLinearMap.toSpanSingleton ℝ (plantedInputDerivative p.2 (B z.1.1) z.1.2)).comp
    (ContinuousLinearMap.snd ℝ ℝ ℝ))

omit [MeasurableSpace Omega] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
theorem hasFDerivAt_doubleInput (p : ℝ × ℝ) (z : (Omega × D) × E)
    (A : Omega → E) (B : Omega → D) :
    HasFDerivAt (fun t ↦ doubleInput t z A B) (doubleInputDerivative p z A B) p := by
  exact (((hasDerivAt_plantedInput p.1 (A z.1.1) z.2).hasFDerivAt).comp p hasFDerivAt_fst).prodMk
    (((hasDerivAt_plantedInput p.2 (B z.1.1) z.1.2).hasFDerivAt).comp p hasFDerivAt_snd)

theorem doubleField_ae_bound (mu : Measure Omega) (A : Omega → E) (B : Omega → D)
    {KA KB : ℝ} (hA : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) :
    ∀ᵐ x ∂mu, ‖doubleField A B x‖ ≤ (KA+KA^2)+(KB+KB^2) := by
  filter_upwards [hA,hB] with x hx hy
  exact (norm_doubleField_le A B x).trans (add_le_add
    (add_le_add hx (pow_le_pow_left₀ (norm_nonneg _) hx 2))
    (add_le_add hy (pow_le_pow_left₀ (norm_nonneg _) hy 2)))

omit [MeasurableSpace Omega] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
theorem norm_doubleInputDerivative_le (p : ℝ × ℝ) (z : (Omega × D) × E)
    (A : Omega → E) (B : Omega → D) :
    ‖doubleInputDerivative p z A B‖ ≤
      (2*|p.1| * ‖A z.1.1‖+‖z.2‖+|p.1|) +
        (2*|p.2| * ‖B z.1.1‖+‖z.1.2‖+|p.2|) := by
  have h1 : ‖(ContinuousLinearMap.toSpanSingleton ℝ (plantedInputDerivative p.1 (A z.1.1) z.2)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)‖ ≤ ‖plantedInputDerivative p.1 (A z.1.1) z.2‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ))
  have h2 : ‖(ContinuousLinearMap.toSpanSingleton ℝ (plantedInputDerivative p.2 (B z.1.1) z.1.2)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ ≤ ‖plantedInputDerivative p.2 (B z.1.1) z.1.2‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ))
  rw [doubleInputDerivative, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  apply max_le
  · exact ((h1.trans (norm_plantedInputDerivative_le p.1 (A z.1.1) z.2))).trans
      (le_add_of_nonneg_right (by positivity))
  · exact ((h2.trans (norm_plantedInputDerivative_le p.2 (B z.1.1) z.1.2))).trans
      (le_add_of_nonneg_left (by positivity))

theorem measurable_doubleInput (A : Omega → E) (B : Omega → D)
    (hA : Measurable A) (hB : Measurable B) (p : ℝ × ℝ) :
    Measurable (fun z : (Omega × D) × E ↦ doubleInput p z A B) :=
  ((measurable_plantedInput A hA p.1).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    ((measurable_plantedInput B hB p.2).comp measurable_fst)

theorem measurable_doubleInputDerivative (A : Omega → E) (B : Omega → D)
    (hA : Measurable A) (hB : Measurable B) (p : ℝ × ℝ) :
    Measurable (fun z : (Omega × D) × E ↦ doubleInputDerivative p z A B) := by
  have hs1 : Continuous (fun d : E × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ d) :=
    (ContinuousLinearMap.toSpanSingletonCLE : (E × ℝ) ≃L[ℝ] (ℝ →L[ℝ] (E × ℝ))).continuous
  have hs2 : Continuous (fun d : D × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ d) :=
    (ContinuousLinearMap.toSpanSingletonCLE : (D × ℝ) ≃L[ℝ] (ℝ →L[ℝ] (D × ℝ))).continuous
  have hc1 := hs1.clm_comp (continuous_const (y := ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hc2 := hs2.clm_comp (continuous_const (y := ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hp : Continuous (fun q : ((ℝ × ℝ) →L[ℝ] (E × ℝ)) × ((ℝ × ℝ) →L[ℝ] (D × ℝ)) ↦
      q.1.prod q.2) := (ContinuousLinearMap.prodₗᵢ ℝ).continuous
  exact hp.measurable.comp ((hc1.measurable.comp
    ((measurable_plantedInputDerivative A hA p.1).comp (measurable_fst.fst.prodMk measurable_snd))).prodMk
    (hc2.measurable.comp ((measurable_plantedInputDerivative B hB p.2).comp measurable_fst)))

noncomputable def doubleLogDerivative (mu : Measure Omega) (A : Omega → E) (B : Omega → D)
    (p : ℝ × ℝ) (z : (Omega × D) × E) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (score mu (doubleField A B) (doubleInput p z A B)).comp (doubleInputDerivative p z A B)

theorem measurable_doubleLogDerivative (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) (p : ℝ × ℝ) :
    Measurable (doubleLogDerivative mu A B p) := by
  have hs := score_continuous mu (doubleField A B) (measurable_doubleField A B hA hB)
    (by positivity : 0 ≤ (KA+KA^2)+(KB+KB^2)) (doubleField_ae_bound mu A B hAB hBB)
  have hc : Continuous (fun q : (((E × ℝ) × (D × ℝ)) →L[ℝ] ℝ) ×
      ((ℝ × ℝ) →L[ℝ] ((E × ℝ) × (D × ℝ))) ↦ q.1.comp q.2) :=
    continuous_fst.clm_comp continuous_snd
  exact hc.measurable.comp (((hs.measurable.comp (measurable_doubleInput A B hA hB p))).prodMk
    (measurable_doubleInputDerivative A B hA hB p))

theorem hasFDerivAt_doubleLogPartition (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB)
    (p : ℝ × ℝ) (z : (Omega × D) × E) :
    HasFDerivAt (fun t ↦ logPartition mu (doubleField A B) (doubleInput t z A B))
      (doubleLogDerivative mu A B p z) p := by
  have hd := logPartition_hasFDerivAt mu (doubleField A B) (measurable_doubleField A B hA hB)
    (by positivity : 0 ≤ (KA+KA^2)+(KB+KB^2)) (doubleField_ae_bound mu A B hAB hBB)
    (doubleInput p z A B)
  simpa only [Function.comp_def, doubleLogDerivative] using hd.comp p (hasFDerivAt_doubleInput p z A B)

theorem integrable_doubleInput (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) (p : ℝ × ℝ) :
    Integrable (fun z : (Omega × D) × E ↦ doubleInput p z A B)
      ((mu.prod (stdGaussian D)).prod (stdGaussian E)) := by
  have hAI := ((Integrable.of_bound hA.aestronglyMeasurable KA hAB).comp_fst (stdGaussian D)).comp_fst (stdGaussian E)
  have hBI := ((Integrable.of_bound hB.aestronglyMeasurable KB hBB).comp_fst (stdGaussian D)).comp_fst (stdGaussian E)
  have hWA : Integrable (fun z : (Omega × D) × E ↦ z.2)
      ((mu.prod (stdGaussian D)).prod (stdGaussian E)) := IsGaussian.integrable_id.comp_snd _
  have hWB : Integrable (fun z : (Omega × D) × E ↦ z.1.2)
      ((mu.prod (stdGaussian D)).prod (stdGaussian E)) :=
    (show Integrable (fun z : Omega × D ↦ z.2) (mu.prod (stdGaussian D)) from
      IsGaussian.integrable_id.comp_snd mu).comp_fst (stdGaussian E)
  simpa only [doubleInput, plantedInput, Pi.smul_apply] using
    (((Integrable.smul (p.1^2) hAI).fun_add (Integrable.smul p.1 hWA)).prodMk (integrable_const (-(p.1^2)/2))).prodMk
      (((Integrable.smul (p.2^2) hBI).fun_add (Integrable.smul p.2 hWB)).prodMk (integrable_const (-(p.2^2)/2)))

theorem integrable_doubleLogPartition (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) (p : ℝ × ℝ) :
    Integrable (fun z : (Omega × D) × E ↦ logPartition mu (doubleField A B) (doubleInput p z A B))
      ((mu.prod (stdGaussian D)).prod (stdGaussian E)) := by
  have hc := (logPartition_contDiff mu (doubleField A B) (measurable_doubleField A B hA hB)
    (by positivity : 0 ≤ (KA+KA^2)+(KB+KB^2)) (doubleField_ae_bound mu A B hAB hBB)).continuous
  apply ((integrable_doubleInput mu A B hA hB hAB hBB p).norm.const_mul ((KA+KA^2)+(KB+KB^2))).mono'
    ((hc.measurable.comp (measurable_doubleInput A B hA hB p)).aestronglyMeasurable)
  exact .of_forall fun z ↦ by
    simpa only [Real.norm_eq_abs, Function.comp_def] using abs_logPartition_le mu (doubleField A B)
      (measurable_doubleField A B hA hB) (doubleField_ae_bound mu A B hAB hBB) (doubleInput p z A B)

/-- Joint differentiability is checked under the actual common prior and both
independent Gaussian noises. The dominating operator norm is a constant plus
the two Gaussian norms, uniform on a parameter neighborhood. -/
theorem differentiableAt_twoChannelFreeEnergy (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ ↦
      twoChannelFreeEnergy mu (fun x ↦ q.1 • A x) (fun x ↦ q.2 • B x)) p := by
  let base := (mu.prod (stdGaussian D)).prod (stdGaussian E)
  let L := (KA+KA^2)+(KB+KB^2)
  let M := ‖p‖+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hWA : Integrable (fun z : (Omega × D) × E ↦ ‖z.2‖) base :=
    (show Integrable (fun w : E ↦ ‖w‖) (stdGaussian E) from IsGaussian.integrable_id.norm).comp_snd _
  have hWB : Integrable (fun z : (Omega × D) × E ↦ ‖z.1.2‖) base :=
    ((show Integrable (fun w : D ↦ ‖w‖) (stdGaussian D) from IsGaussian.integrable_id.norm).comp_snd mu).comp_fst
      (stdGaussian E)
  have hBoundInt : Integrable (fun z : (Omega × D) × E ↦
      L*((2*M*KA+‖z.2‖+M)+(2*M*KB+‖z.1.2‖+M))) base :=
    ((((integrable_const (2*M*KA)).add hWA).add (integrable_const M)).add
      (((integrable_const (2*M*KB)).add hWB).add (integrable_const M))).const_mul L
  have hc := (logPartition_contDiff mu (doubleField A B) (measurable_doubleField A B hA hB)
    hL (doubleField_ae_bound mu A B hAB hBB)).continuous
  have hDiff := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := base) (s := Metric.ball p 1) (F' := doubleLogDerivative mu A B)
    (bound := fun z : (Omega × D) × E ↦ L*((2*M*KA+‖z.2‖+M)+(2*M*KB+‖z.1.2‖+M)))
    (Metric.ball_mem_nhds p zero_lt_one)
    (.of_forall fun q ↦ (hc.measurable.comp (measurable_doubleInput A B hA hB q)).aestronglyMeasurable)
    (integrable_doubleLogPartition mu A B hA hB hKA hKB hAB hBB p)
    (measurable_doubleLogDerivative mu A B hA hB hKA hKB hAB hBB p).aestronglyMeasurable
    (bound_integrable := hBoundInt)
    (h_diff := .of_forall fun z q _ ↦ hasFDerivAt_doubleLogPartition mu A B hA hB hKA hKB hAB hBB q z)
  have hAT : ∀ᵐ z : (Omega × D) × E ∂base, ‖A z.1.1‖ ≤ KA :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hAB)
  have hBT : ∀ᵐ z : (Omega × D) × E ∂base, ‖B z.1.1‖ ≤ KB :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hBB)
  have hb : ∀ᵐ z : (Omega × D) × E ∂base, ∀ q ∈ Metric.ball p 1,
      ‖doubleLogDerivative mu A B q z‖ ≤ L*((2*M*KA+‖z.2‖+M)+(2*M*KB+‖z.1.2‖+M)) := by
    filter_upwards [hAT,hBT] with z hzA hzB q hq
    have hqn : ‖q‖ ≤ M := norm_le_of_mem_ball hq
    have hq1 : |q.1| ≤ M := (norm_fst_le q).trans hqn
    have hq2 : |q.2| ≤ M := (norm_snd_le q).trans hqn
    have hd : ‖doubleInputDerivative q z A B‖ ≤
        (2*M*KA+‖z.2‖+M)+(2*M*KB+‖z.1.2‖+M) :=
      (norm_doubleInputDerivative_le q z A B).trans (by gcongr)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
      (norm_score_le mu (doubleField A B) (measurable_doubleField A B hA hB) hL
        (doubleField_ae_bound mu A B hAB hBB) (doubleInput q z A B)) hd (norm_nonneg _) hL)
  convert (hDiff hb).differentiableAt using 1
  funext q
  exact twoChannelFreeEnergy_eq_doublePartition mu A B q


end TensorPCA.GaussianTwoStrengthCalculusProofs
