-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianBoundedChannelDerivativeProofs

/-! # Bounded-prior Gaussian I-MMSE

The signal has no constant-norm restriction. Posterior squared norms and the
posterior signal second moment are kept distinct until the Gaussian covariance
trace cancels the latter.
-/
@[expose] public section

namespace TensorPCA.GaussianBoundedIMMSEProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianPosteriorCovarianceProofs GaussianBoundedChannelDerivativeProofs
open scoped RealInnerProductSpace ENNReal

theorem integrable_observable_posterior {Omega E V : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (a : Omega → V) (ha : StronglyMeasurable a) {C : ℝ}
    (haB : ∀ᵐ x ∂mu, ‖a x‖ ≤ C) (y : E) : Integrable a (posteriorKernel mu F y) := by
  have : IsMarkovKernel (posteriorKernel mu F) := posteriorKernel_isMarkov mu F hF
  have hac : posteriorKernel mu F y ≪ mu := by
    rw [posteriorKernel_apply mu F hF]
    exact withDensity_absolutelyContinuous mu _
  exact Integrable.of_bound ha.aestronglyMeasurable C (hac.ae_le haB)

theorem posteriorMean_inner {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (A : Omega → E) (hA : Measurable A) {K : ℝ}
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (y d : E) :
    posteriorMean mu F (fun x ↦ inner ℝ (A x) d) y = inner ℝ (posteriorMean mu F A y) d := by
  have hi := integrable_observable_posterior mu F hF A hA.stronglyMeasurable hAB y
  have h := (innerSL ℝ d).integral_comp_comm hi
  simpa only [innerSL_apply_apply, real_inner_comm, posteriorMean] using h

theorem memLp_posteriorMean_comp {Omega E V Z : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace Z]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (a : Omega → V) (ha : StronglyMeasurable a) {C : ℝ}
    (haB : ∀ᵐ x ∂mu, ‖a x‖ ≤ C) (nu : Measure Z) [IsFiniteMeasure nu]
    (obs : Z → E) (hObs : Measurable obs) (p : ℝ≥0∞) :
    MemLp (fun z ↦ posteriorMean mu F a (obs z)) p nu :=
  MemLp.of_bound ((stronglyMeasurable_posteriorMean mu F a ha).comp_measurable hObs).aestronglyMeasurable
    C (.of_forall fun z ↦ norm_posteriorMean_le mu F hF a haB (obs z))

variable {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]

noncomputable def coordinateObservable (A : Omega → EuclideanSpace ℝ iota) (i : iota)
    (x : Omega) : ℝ := by
  classical
  exact inner ℝ (A x) (EuclideanSpace.single i 1)

theorem measurable_coordinateObservable (A : Omega → EuclideanSpace ℝ iota)
    (hA : Measurable A) (i : iota) : Measurable (coordinateObservable A i) := by
  classical
  change Measurable (fun x ↦ inner ℝ (A x) (EuclideanSpace.single i 1))
  simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
    (innerSL ℝ (EuclideanSpace.single i 1 : EuclideanSpace ℝ iota)).continuous.measurable.comp hA

theorem coordinateObservable_abs_le (mu : Measure Omega)
    (A : Omega → EuclideanSpace ℝ iota) {K : ℝ} (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (i : iota) :
    ∀ᵐ x ∂mu, |coordinateObservable A i x| ≤ K := by
  classical
  filter_upwards [hAB] with x hx
  have hi : |coordinateObservable A i x| ≤ ‖A x‖ := by
    simpa [coordinateObservable] using norm_inner_le_norm (𝕜 := ℝ) (A x) (EuclideanSpace.single i 1)
  exact hi.trans hx

omit [MeasurableSpace Omega] in
theorem sum_coordinateObservable_sq (A : Omega → EuclideanSpace ℝ iota) (x : Omega) :
    ∑ i, coordinateObservable A i x ^ 2 = ‖A x‖^2 := by
  classical
  simpa only [coordinateObservable, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun iota ℝ).sum_sq_inner_left (A x)

theorem sum_posteriorMean_coordinate_sq (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F A : Omega → EuclideanSpace ℝ iota) (hF : Measurable F) (hA : Measurable A) {K : ℝ}
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (y : EuclideanSpace ℝ iota) :
    ∑ i, posteriorMean mu F (coordinateObservable A i) y ^ 2 = ‖posteriorMean mu F A y‖^2 := by
  classical
  change (∑ i, posteriorMean mu F (fun x ↦ inner ℝ (A x) (EuclideanSpace.single i 1)) y ^ 2) = _
  simp_rw [posteriorMean_inner mu F hF A hA hAB]
  simpa only [EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun iota ℝ).sum_sq_inner_left (posteriorMean mu F A y)

theorem posteriorMean_const_mul (mu : Measure Omega) [SFinite mu]
    (F : Omega → EuclideanSpace ℝ iota) (a : Omega → ℝ) (c : ℝ) (y : EuclideanSpace ℝ iota) :
    posteriorMean mu F (fun x ↦ c*a x) y = c*posteriorMean mu F a y :=
  integral_const_mul c a

theorem sum_posteriorMean_coordinate_secondMoment (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F A : Omega → EuclideanSpace ℝ iota) (hF : Measurable F) (hA : Measurable A) {K : ℝ}
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (y : EuclideanSpace ℝ iota) :
    ∑ i, posteriorMean mu F (fun x ↦ coordinateObservable A i x ^ 2) y =
      posteriorMean mu F (fun x ↦ ‖A x‖^2) y := by
  classical
  have hi (i : iota) : Integrable (fun x ↦ coordinateObservable A i x ^ 2)
      (posteriorKernel mu F y) := by
    apply integrable_observable_posterior mu F hF _
      ((measurable_coordinateObservable A hA i).pow_const 2).stronglyMeasurable
    filter_upwards [coordinateObservable_abs_le mu A hAB i] with x hx
    simpa only [norm_pow, Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (coordinateObservable A i x)) hx 2)
  change (∑ i, ∫ x, coordinateObservable A i x ^ 2 ∂posteriorKernel mu F y) = _
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
  apply integral_congr_ae
  exact .of_forall fun x ↦ sum_coordinateObservable_sq A x

theorem coordinate_gaussian_ibp (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v : EuclideanSpace ℝ iota) (i : iota) :
    (∫ w, w i * posteriorMean mu (fun x ↦ lam • A x) (coordinateObservable A i) (v+w)
      ∂stdGaussian (EuclideanSpace ℝ iota)) =
      ∫ w, lam * (posteriorMean mu (fun x ↦ lam • A x)
          (fun x ↦ coordinateObservable A i x ^ 2) (v+w) -
        posteriorMean mu (fun x ↦ lam • A x) (coordinateObservable A i) (v+w) ^ 2)
        ∂stdGaussian (EuclideanSpace ℝ iota) := by
  classical
  have hFB : ∀ᵐ x ∂mu, ‖lam • A x‖ ≤ |lam| * K := by
    filter_upwards [hAB] with x hx
    simpa only [norm_smul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hx (abs_nonneg lam)
  have hF : Measurable (fun x ↦ lam • A x) := by
    exact (continuous_const_smul lam).measurable.comp hA
  have h := posteriorMean_gaussian_ibp mu (fun x ↦ lam • A x) hF
    (coordinateObservable A i) (measurable_coordinateObservable A hA i) hK
    (mul_nonneg (abs_nonneg lam) hK) (coordinateObservable_abs_le mu A hAB i) hFB
    v (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] at h
  rw [h]
  apply integral_congr_ae
  refine .of_forall fun w ↦ ?_
  dsimp only
  have hmul : (fun x ↦ coordinateObservable A i x * inner ℝ (lam • A x) (EuclideanSpace.single i 1)) =
      (fun x ↦ lam * coordinateObservable A i x ^ 2) := by
    funext x
    simp only [coordinateObservable, real_inner_smul_left]
    ring
  have hlin : (fun x ↦ inner ℝ (lam • A x) (EuclideanSpace.single i 1)) =
      (fun x ↦ lam * coordinateObservable A i x) := by
    funext x
    simp only [coordinateObservable, real_inner_smul_left]
  rw [hmul, hlin, posteriorMean_const_mul, posteriorMean_const_mul]
  ring

theorem integrable_gaussian_coordinate_response (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F A : Omega → EuclideanSpace ℝ iota) (hF : Measurable F) (hA : Measurable A)
    {K : ℝ} (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K)
    (v : EuclideanSpace ℝ iota) (i : iota) :
    Integrable (fun w : EuclideanSpace ℝ iota ↦
      w i * posteriorMean mu F (coordinateObservable A i) (v+w))
      (stdGaussian (EuclideanSpace ℝ iota)) := by
  have ha := measurable_coordinateObservable A hA i
  have hb : ∀ᵐ x ∂mu, ‖coordinateObservable A i x‖ ≤ K := by
    simpa only [Real.norm_eq_abs] using coordinateObservable_abs_le mu A hAB i
  have hpm := (stronglyMeasurable_posteriorMean mu F (coordinateObservable A i) ha.stronglyMeasurable).measurable
  have hObs : Measurable (fun w : EuclideanSpace ℝ iota ↦ v+w) :=
    (continuous_const.add continuous_id).measurable
  have hp := hpm.comp hObs
  have hn : Integrable (fun w : EuclideanSpace ℝ iota ↦ ‖w‖) (stdGaussian (EuclideanSpace ℝ iota)) :=
    IsGaussian.integrable_id.norm
  apply (hn.mul_const K).mono'
    (((PiLp.continuous_apply 2 (fun _ : iota ↦ ℝ) i).measurable).mul hp).aestronglyMeasurable
  exact .of_forall fun w ↦ by
    change ‖w i * posteriorMean mu F (coordinateObservable A i) (v+w)‖ ≤ ‖w‖ * K
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i)
      (norm_posteriorMean_le mu F hF (coordinateObservable A i) hb (v+w)) (norm_nonneg _) (norm_nonneg _)

theorem integral_noise_inner_posteriorMean (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v : EuclideanSpace ℝ iota) :
    (∫ w, inner ℝ (posteriorMean mu (fun x ↦ lam • A x) A (v+w)) w
      ∂stdGaussian (EuclideanSpace ℝ iota)) =
      lam * ∫ w, posteriorMean mu (fun x ↦ lam • A x) (fun x ↦ ‖A x‖^2) (v+w) -
        ‖posteriorMean mu (fun x ↦ lam • A x) A (v+w)‖^2
        ∂stdGaussian (EuclideanSpace ℝ iota) := by
  classical
  let F : Omega → EuclideanSpace ℝ iota := fun x ↦ lam • A x
  have hF : Measurable F := (continuous_const_smul lam).measurable.comp hA
  have hObs : Measurable (fun w : EuclideanSpace ℝ iota ↦ v+w) :=
    (continuous_const.add continuous_id).measurable
  have hi (i : iota) := integrable_gaussian_coordinate_response mu F A hF hA hAB v i
  have hd (i : iota) : Integrable (fun w : EuclideanSpace ℝ iota ↦
      lam*(posteriorMean mu F (fun x ↦ coordinateObservable A i x ^ 2) (v+w) -
        posteriorMean mu F (coordinateObservable A i) (v+w)^2))
      (stdGaussian (EuclideanSpace ℝ iota)) := by
    have ha := measurable_coordinateObservable A hA i
    have hb : ∀ᵐ x ∂mu, ‖coordinateObservable A i x‖ ≤ K := by
      simpa only [Real.norm_eq_abs] using coordinateObservable_abs_le mu A hAB i
    have hb2 : ∀ᵐ x ∂mu, ‖coordinateObservable A i x ^ 2‖ ≤ K^2 := by
      filter_upwards [hb] with x hx
      simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hm := memLp_posteriorMean_comp mu F hF (coordinateObservable A i) ha.stronglyMeasurable
      hb (stdGaussian (EuclideanSpace ℝ iota)) _ hObs 2
    have hm2 : Integrable (fun w : EuclideanSpace ℝ iota ↦
        posteriorMean mu F (coordinateObservable A i) (v+w)^2)
        (stdGaussian (EuclideanSpace ℝ iota)) := by
      simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow (by decide : 2 ≠ 0)
    have hs := memLp_posteriorMean_comp mu F hF (fun x ↦ coordinateObservable A i x^2)
      (ha.pow_const 2).stronglyMeasurable hb2 (stdGaussian (EuclideanSpace ℝ iota)) _ hObs 1
    exact ((hs.integrable (by norm_num)).sub' hm2).const_mul lam
  calc
    _ = ∫ w, ∑ i, w i * posteriorMean mu F (coordinateObservable A i) (v+w)
        ∂stdGaussian (EuclideanSpace ℝ iota) := by
      apply integral_congr_ae
      refine .of_forall fun w ↦ ?_
      change inner ℝ (posteriorMean mu F A (v+w)) w =
        ∑ i, w i * posteriorMean mu F (fun x ↦ inner ℝ (A x) (EuclideanSpace.single i 1)) (v+w)
      simp_rw [posteriorMean_inner mu F hF A hA hAB]
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
        conj_trivial, one_mul, mul_comm] using
        ((EuclideanSpace.basisFun iota ℝ).sum_inner_mul_inner (posteriorMean mu F A (v+w)) w).symm
    _ = ∑ i, ∫ w, w i * posteriorMean mu F (coordinateObservable A i) (v+w)
        ∂stdGaussian (EuclideanSpace ℝ iota) := integral_finsetSum Finset.univ (fun i _ ↦ hi i)
    _ = ∑ i, ∫ w, lam*(posteriorMean mu F (fun x ↦ coordinateObservable A i x^2) (v+w) -
        posteriorMean mu F (coordinateObservable A i) (v+w)^2)
        ∂stdGaussian (EuclideanSpace ℝ iota) := by
      apply Finset.sum_congr rfl
      intro i _
      exact coordinate_gaussian_ibp mu A hA hK hAB lam v i
    _ = ∫ w, ∑ i, lam*(posteriorMean mu F (fun x ↦ coordinateObservable A i x^2) (v+w) -
        posteriorMean mu F (coordinateObservable A i) (v+w)^2)
        ∂stdGaussian (EuclideanSpace ℝ iota) := (integral_finsetSum Finset.univ (fun i _ ↦ hd i)).symm
    _ = ∫ w, lam*(posteriorMean mu F (fun x ↦ ‖A x‖^2) (v+w) -
        ‖posteriorMean mu F A (v+w)‖^2) ∂stdGaussian (EuclideanSpace ℝ iota) := by
      apply integral_congr_ae
      exact .of_forall fun w ↦ by
        dsimp only
        rw [← Finset.mul_sum, Finset.sum_sub_distrib,
          sum_posteriorMean_coordinate_secondMoment mu F A hF hA hAB,
          sum_posteriorMean_coordinate_sq mu F A hF hA hAB]
    _ = _ := integral_const_mul lam _

theorem norm_sq_ae_bound (mu : Measure Omega) (A : Omega → EuclideanSpace ℝ iota) {K : ℝ}
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) : ∀ᵐ x ∂mu, ‖‖A x‖^2‖ ≤ K^2 := by
  filter_upwards [hAB] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

theorem plantedLogDerivative_eq (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (z : Omega × EuclideanSpace ℝ iota) :
    plantedLogDerivative mu A lam z =
      (2*lam)*inner ℝ (A z.1) (posteriorMean mu (fun x ↦ lam • A x) A (lam • A z.1+z.2)) +
      inner ℝ (posteriorMean mu (fun x ↦ lam • A x) A (lam • A z.1+z.2)) z.2 -
      lam*posteriorMean mu (fun x ↦ lam • A x) (fun x ↦ ‖A x‖^2) (lam • A z.1+z.2) := by
  let F : Omega → EuclideanSpace ℝ iota := fun x ↦ lam • A x
  have hF : Measurable F := (continuous_const_smul lam).measurable.comp hA
  have hIntA := integrable_observable_posterior mu F hF A hA.stronglyMeasurable hAB (lam • A z.1+z.2)
  have hIntS := integrable_observable_posterior mu F hF (fun x ↦ ‖A x‖^2)
    (hA.norm.pow_const 2).stronglyMeasurable (norm_sq_ae_bound mu A hAB) (lam • A z.1+z.2)
  rw [plantedLogDerivative, score_plantedInput_eq_posteriorMean mu A hA hK hAB]
  change (∫ x, inner ℝ (A x) ((2*lam) • A z.1+z.2) - lam*‖A x‖^2
    ∂posteriorKernel mu F (lam • A z.1+z.2)) = _
  rw [integral_sub (hIntA.inner_const _) (hIntS.const_mul lam), integral_const_mul]
  change posteriorMean mu F (fun x ↦ inner ℝ (A x) ((2*lam) • A z.1+z.2)) (lam • A z.1+z.2) -
    lam*posteriorMean mu F (fun x ↦ ‖A x‖^2) (lam • A z.1+z.2) = _
  rw [posteriorMean_inner mu F hF A hA hAB]
  rw [inner_add_right, real_inner_smul_right,
    real_inner_comm (posteriorMean mu F A (lam • A z.1+z.2)) (A z.1)]

theorem integral_plantedLogDerivative [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    (∫ z, plantedLogDerivative mu A lam z ∂mu.prod (stdGaussian (EuclideanSpace ℝ iota))) =
      lam * ∫ z : Omega × EuclideanSpace ℝ iota,
        ‖posteriorMean mu (fun x ↦ lam • A x) A (lam • A z.1+z.2)‖^2
        ∂mu.prod (stdGaussian (EuclideanSpace ℝ iota)) := by
  let F : Omega → EuclideanSpace ℝ iota := fun x ↦ lam • A x
  let obs : Omega × EuclideanSpace ℝ iota → EuclideanSpace ℝ iota := fun z ↦ F z.1+z.2
  let base := mu.prod (stdGaussian (EuclideanSpace ℝ iota))
  have hF : Measurable F := (continuous_const_smul lam).measurable.comp hA
  have hObs : Measurable obs := (hF.comp measurable_fst).add measurable_snd
  have hA2 : MemLp A 2 mu := MemLp.of_bound hA.aestronglyMeasurable K hAB
  have hT2 : MemLp (fun z : Omega × EuclideanSpace ℝ iota ↦ A z.1) 2 base :=
    hA2.comp_fst (stdGaussian (EuclideanSpace ℝ iota))
  have hP2 := memLp_posteriorMean_comp mu F hF A hA.stronglyMeasurable hAB base obs hObs 2
  have hSquare : Integrable (fun z ↦ ‖posteriorMean mu F A (obs z)‖^2) base :=
    hP2.integrable_norm_pow (by decide : 2 ≠ 0)
  have hSecond : Integrable (fun z ↦ posteriorMean mu F (fun x ↦ ‖A x‖^2) (obs z)) base :=
    (memLp_posteriorMean_comp mu F hF (fun x ↦ ‖A x‖^2)
      (hA.norm.pow_const 2).stronglyMeasurable (norm_sq_ae_bound mu A hAB) base obs hObs 1).integrable (by norm_num)
  have hCross : Integrable (fun z ↦ inner ℝ (A z.1) (posteriorMean mu F A (obs z))) base := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hT2.toLp (fun z ↦ A z.1))
      (hP2.toLp (fun z ↦ posteriorMean mu F A (obs z)))).congr
    filter_upwards [hT2.coeFn_toLp, hP2.coeFn_toLp] with z ht hp
    rw [ht, hp]
  have hn : Integrable (fun z : Omega × EuclideanSpace ℝ iota ↦ ‖z.2‖) base :=
    (show Integrable (fun w : EuclideanSpace ℝ iota ↦ ‖w‖)
      (stdGaussian (EuclideanSpace ℝ iota)) from IsGaussian.integrable_id.norm).comp_snd mu
  have hNoise : Integrable (fun z : Omega × EuclideanSpace ℝ iota ↦
      inner ℝ (posteriorMean mu F A (obs z)) z.2) base := by
    have hp := (stronglyMeasurable_posteriorMean mu F A hA.stronglyMeasurable).comp_measurable hObs
    apply (hn.const_mul K).mono' (hp.aestronglyMeasurable.inner measurable_snd.aestronglyMeasurable)
    exact .of_forall fun z ↦ by
      change ‖inner ℝ (posteriorMean mu F A (obs z)) z.2‖ ≤ K*‖z.2‖
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_posteriorMean_le mu F hF A hAB (obs z)) (norm_nonneg _))
  have hIBP : (∫ z, inner ℝ (posteriorMean mu F A (obs z)) z.2 ∂base) =
      lam*((∫ z, posteriorMean mu F (fun x ↦ ‖A x‖^2) (obs z) ∂base) -
        ∫ z, ‖posteriorMean mu F A (obs z)‖^2 ∂base) := by
    rw [integral_prod _ hNoise]
    change (∫ x, ∫ w, inner ℝ (posteriorMean mu (fun x ↦ lam • A x) A (lam • A x+w)) w
      ∂stdGaussian (EuclideanSpace ℝ iota) ∂mu) = _
    simp_rw [integral_noise_inner_posteriorMean mu A hA hK hAB lam]
    rw [integral_const_mul, ← integral_prod _ (hSecond.sub' hSquare), integral_sub hSecond hSquare]
  have hNish := integral_latent_inner_posteriorMean mu F hF A hA.stronglyMeasurable hA2
  change (∫ z, inner ℝ (A z.1) (posteriorMean mu F A (obs z)) ∂base) =
    ∫ z, ‖posteriorMean mu F A (obs z)‖^2 ∂base at hNish
  simp_rw [plantedLogDerivative_eq mu A hA hK hAB lam]
  rw [integral_sub ((hCross.const_mul (2*lam)).fun_add hNoise) (hSecond.const_mul lam),
    integral_add (hCross.const_mul (2*lam)) hNoise,
    integral_const_mul, integral_const_mul, hNish, hIBP]
  ring

theorem mixtureFreeEnergy_scale_eq_integral (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) (lam : ℝ) :
    mixtureFreeEnergy mu (fun x ↦ lam • A x) =
      ∫ z : Omega × EuclideanSpace ℝ iota,
        Real.log (mixtureLikelihood mu (fun x ↦ lam • A x) (lam • A z.1+z.2))
        ∂mu.prod (stdGaussian (EuclideanSpace ℝ iota)) := by
  have hF : Measurable (fun x ↦ lam • A x) := (continuous_const_smul lam).measurable.comp hA
  have hObs : Measurable (fun z : Omega × EuclideanSpace ℝ iota ↦ lam • A z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  have hL := (measurable_mixtureLikelihood mu (fun x ↦ lam • A x) hF).log
  rw [GaussianMixtureStabilityProofs.mixtureFreeEnergy_eq_integral mu _ hF, mixtureLaw,
    integral_map hObs.aemeasurable hL.aestronglyMeasurable]

/-- Actual bounded-prior I-MMSE at raw channel strength, valid for every real
strength and without a constant-norm assumption on the prior signal. -/
theorem hasDerivAt_mixtureFreeEnergy_scale [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    HasDerivAt (fun t ↦ mixtureFreeEnergy mu (fun x ↦ t • A x))
      (lam * ∫ z : Omega × EuclideanSpace ℝ iota,
        ‖posteriorMean mu (fun x ↦ lam • A x) A (lam • A z.1+z.2)‖^2
        ∂mu.prod (stdGaussian (EuclideanSpace ℝ iota))) lam := by
  simp_rw [mixtureFreeEnergy_scale_eq_integral mu A hA]
  simpa only [integral_plantedLogDerivative mu A hA hK hAB lam] using
    hasDerivAt_integral_plantedLogLikelihood mu A hA hK hAB lam

/-- Exact one-half coefficient for the squared-strength parameter used by
Guerra interpolation and the scalar RS potential. -/
theorem hasDerivAt_mixtureFreeEnergy_sqrt [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) {gamma : ℝ} (hgamma : 0 < gamma) :
    HasDerivAt (fun t ↦ mixtureFreeEnergy mu (fun x ↦ Real.sqrt t • A x))
      ((1/2:ℝ) * ∫ z : Omega × EuclideanSpace ℝ iota,
        ‖posteriorMean mu (fun x ↦ Real.sqrt gamma • A x) A (Real.sqrt gamma • A z.1+z.2)‖^2
        ∂mu.prod (stdGaussian (EuclideanSpace ℝ iota))) gamma := by
  have h := (hasDerivAt_mixtureFreeEnergy_scale mu A hA hK hAB (Real.sqrt gamma)).comp gamma
    (Real.hasDerivAt_sqrt hgamma.ne')
  convert h using 1
  · rfl
  · field_simp [(Real.sqrt_pos.mpr hgamma).ne']


end TensorPCA.GaussianBoundedIMMSEProofs
