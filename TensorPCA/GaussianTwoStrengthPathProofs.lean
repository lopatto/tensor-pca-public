-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianTwoStrengthCalculusProofs

/-! # The two-strength differential and interpolation paths -/
@[expose] public section

namespace TensorPCA.GaussianTwoStrengthPathProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSideChannelProofs GaussianConditionalChannelDerivativeProofs
open GaussianTwoChannelFreeEnergyProofs GaussianTwoStrengthCalculusProofs
open scoped RealInnerProductSpace

theorem combinedLikelihood_swap {Omega E D : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
    (mu : Measure Omega) (A : Omega → E) (B : Omega → D) (y : E) (v : D) :
    combinedLikelihood mu A B y v = combinedLikelihood mu B A v y := by
  apply integral_congr_ae
  exact .of_forall fun x ↦ mul_comm _ _

theorem twoChannelFreeEnergy_swap {Omega E D : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (A : Omega → E) (B : Omega → D)
    (hA : Measurable A) (hB : Measurable B) :
    twoChannelFreeEnergy mu A B = twoChannelFreeEnergy mu B A := by
  have hSwap : MeasurePreserving (fun z : (Omega × D) × E ↦ ((z.1.1,z.2),z.1.2))
      ((mu.prod (stdGaussian D)).prod (stdGaussian E))
      ((mu.prod (stdGaussian E)).prod (stdGaussian D)) := by
    convert ((measurePreserving_prodAssoc mu (stdGaussian E) (stdGaussian D)).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id mu).prod (Measure.measurePreserving_swap (μ := stdGaussian D) (ν := stdGaussian E))).comp
        (measurePreserving_prodAssoc mu (stdGaussian D) (stdGaussian E))) using 1
    rfl
  have hObs : Measurable (fun z : (Omega × E) × D ↦ (B z.1.1+z.2,A z.1.1+z.1.2)) :=
    ((hB.comp measurable_fst.fst).add measurable_snd).prodMk
      ((hA.comp measurable_fst.fst).add measurable_fst.snd)
  have hLog : Measurable (fun z : (Omega × E) × D ↦
      Real.log (combinedLikelihood mu B A (B z.1.1+z.2) (A z.1.1+z.1.2))) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      (measurable_combinedLikelihood mu B A hB hA).log.comp hObs
  have hi := integral_map (μ := (mu.prod (stdGaussian D)).prod (stdGaussian E))
    hSwap.measurable.aemeasurable hLog.aestronglyMeasurable
  rw [hSwap.map_eq] at hi
  calc
    _ = ∫ z : (Omega × D) × E,
        Real.log (combinedLikelihood mu B A (B z.1.1+z.1.2) (A z.1.1+z.2))
        ∂(mu.prod (stdGaussian D)).prod (stdGaussian E) := by
      apply integral_congr_ae
      exact .of_forall fun z ↦ congrArg Real.log (combinedLikelihood_swap mu A B _ _)
    _ = _ := hi.symm

variable {Omega iota kappa : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
  [Fintype iota] [Fintype kappa]

theorem hasDerivAt_twoChannelFreeEnergy_path (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB)
    (a b : ℝ → ℝ) (t da db : ℝ) (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun u ↦ twoChannelFreeEnergy mu (fun x ↦ a u • A x) (fun x ↦ b u • B x))
      (da * (a t * ∫ v, conditionalPosteriorSecondMoment mu A (fun x ↦ b t • B x) (a t) v
        ∂mixtureLaw mu (fun x ↦ b t • B x)) +
       db * (b t * ∫ y, conditionalPosteriorSecondMoment mu B (fun x ↦ a t • A x) (b t) y
        ∂mixtureLaw mu (fun x ↦ a t • A x))) t := by
  let f : ℝ × ℝ → ℝ := fun p ↦ twoChannelFreeEnergy mu (fun x ↦ p.1 • A x) (fun x ↦ p.2 • B x)
  let p := (a t,b t)
  have hf := (differentiableAt_twoChannelFreeEnergy mu A B hA hB hKA hKB hAB hBB p).hasFDerivAt
  have hAt : Measurable (fun x ↦ a t • A x) := (continuous_const_smul (a t)).measurable.comp hA
  have hBt : Measurable (fun x ↦ b t • B x) := (continuous_const_smul (b t)).measurable.comp hB
  have hAtB : ∀ᵐ x ∂mu, ‖a t • A x‖ ≤ |a t| * KA := by
    filter_upwards [hAB] with x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hBtB : ∀ᵐ x ∂mu, ‖b t • B x‖ ≤ |b t| * KB := by
    filter_upwards [hBB] with x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h1 := hf.comp_hasDerivAt (a t) ((hasDerivAt_id (a t)).prodMk (hasDerivAt_const (a t) (b t)))
  have h2 := hf.comp_hasDerivAt (b t) ((hasDerivAt_const (b t) (a t)).prodMk (hasDerivAt_id (b t)))
  have hk1 := hasDerivAt_twoChannelFreeEnergy_scale mu A (fun x ↦ b t • B x) hA hBt hKA hAB hBtB (a t)
  have hk2 : HasDerivAt (fun u ↦ twoChannelFreeEnergy mu (fun x ↦ a t • A x) (fun x ↦ u • B x))
      (b t * ∫ y, conditionalPosteriorSecondMoment mu B (fun x ↦ a t • A x) (b t) y
        ∂mixtureLaw mu (fun x ↦ a t • A x)) (b t) := by
    convert hasDerivAt_twoChannelFreeEnergy_scale mu B (fun x ↦ a t • A x) hB hAt hKB hBB hAtB (b t) using 1
    funext u
    exact twoChannelFreeEnergy_swap mu _ _ hAt ((continuous_const_smul u).measurable.comp hB)
  have he1 := h1.unique hk1
  have he2 := h2.unique hk2
  have h := hf.comp_hasDerivAt t (ha.prodMk hb)
  convert h using 1
  · rfl
  · rw [show (da,db) = da • ((1:ℝ),0) + db • ((0:ℝ),1) by ext <;> simp,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, he1, he2]

/-- The exact Guerra square-root path derivative for actual independent
Gaussian tensor and scalar channels, before identifying posterior moments
with tensor/scalar replica overlap polynomials. -/
theorem hasDerivAt_guerraPath (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun u ↦ twoChannelFreeEnergy mu (fun x ↦ Real.sqrt u • A x)
        (fun x ↦ Real.sqrt (1-u) • B x))
      ((1/2:ℝ) * ∫ v, conditionalPosteriorSecondMoment mu A (fun x ↦ Real.sqrt (1-t) • B x)
          (Real.sqrt t) v ∂mixtureLaw mu (fun x ↦ Real.sqrt (1-t) • B x) -
       (1/2:ℝ) * ∫ y, conditionalPosteriorSecondMoment mu B (fun x ↦ Real.sqrt t • A x)
          (Real.sqrt (1-t)) y ∂mixtureLaw mu (fun x ↦ Real.sqrt t • A x)) t := by
  have ha := Real.hasDerivAt_sqrt ht0.ne'
  have hb : HasDerivAt (fun u : ℝ ↦ Real.sqrt (1-u)) (-(1/(2*Real.sqrt (1-t)))) t := by
    simpa only [zero_sub, mul_neg, mul_one, Function.comp_def, Pi.sub_apply, Pi.one_apply, id_eq] using
      (Real.hasDerivAt_sqrt (sub_pos.mpr ht1).ne').comp t
        ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))
  have h := hasDerivAt_twoChannelFreeEnergy_path mu A B hA hB hKA hKB hAB hBB
    Real.sqrt (fun u ↦ Real.sqrt (1-u)) t (1/(2*Real.sqrt t)) (-(1/(2*Real.sqrt (1-t)))) ha hb
  convert h using 1
  field_simp [(Real.sqrt_pos.mpr ht0).ne', (Real.sqrt_pos.mpr (sub_pos.mpr ht1)).ne']
  ring


end TensorPCA.GaussianTwoStrengthPathProofs
