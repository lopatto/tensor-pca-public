-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import TensorPCA.Statements
public import TensorPCA.LimitTools
public import TensorPCA.EstimatorBounds

/-!
# Zero-signal overlap consequences

The exact spherical moments and finite randomized-estimator formulas are proved
in Geometry. This module transports them through the paper's coupling laws and uses summable fourth-moment tails; no independence across dimensions
is assumed.
-/
@[expose] public section

namespace TensorPCA.ZeroSignalProofs
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace BigOperators
universe u v

/-- Every randomized unit estimator has vanishing expected overlap power at
zero signal, for every fixed exponent at least two. -/
theorem expectedOverlapPower_zero_tendsto {k : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (A : ℕ → Type u) [∀ n, MeasurableSpace (A n)]
    (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
    (est : ∀ n, Model.Estimator (n+1) k (A n))
    (hest : ∀ n, Model.IsUnitEstimator (est n)) :
    Tendsto (fun n ↦ Model.expectedOverlapPower (n+1) k 0 (est n) (ν n) p)
      atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (fun n : ℕ ↦ 1 / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hd.const_div_atTop 1
  apply squeeze_zero _ _ hzero
  · intro n
    unfold Model.expectedOverlapPower
    exact integral_nonneg (fun z ↦ pow_nonneg (abs_nonneg _) p)
  · intro n
    exact Geometry.zeroSignal_estimator_power_bound (ν n) (Nat.succ_pos n)
      (est n) (hest n) p hp

/-- The zero-signal expected absolute overlap also vanishes, by the proved
finite Hölder bound and the vanishing kth moment. -/
theorem expectedOverlapPower_one_zero_tendsto {k : ℕ} (hk : 1 < k)
    (A : ℕ → Type u) [∀ n, MeasurableSpace (A n)]
    (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
    (est : ∀ n, Model.Estimator (n+1) k (A n))
    (hest : ∀ n, Model.IsUnitEstimator (est n)) :
    Tendsto (fun n ↦ Model.expectedOverlapPower (n+1) k 0 (est n) (ν n) 1)
      atTop (𝓝 0) := by
  have hpow := expectedOverlapPower_zero_tendsto (k := k) k (show 2 ≤ k from hk) A ν est hest
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hk)
  have hkInv : 0 < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  have hroot := ((Real.continuous_rpow_const (q := (k : ℝ)⁻¹) hkInv.le).continuousAt.tendsto).comp hpow
  rw [Real.zero_rpow (ne_of_gt hkInv)] at hroot
  apply squeeze_zero _ _ hroot
  · intro n
    exact EstimatorBounds.expectedOverlapPower_nonneg (n+1) k 0 (ν n) (est n) 1
  · intro n
    exact EstimatorBounds.expectedOverlapPower_one_le_rpow (Nat.succ_pos n) hk 0 (ν n) (est n) (hest n)

private theorem inverse_successor_product_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (((j : ℝ)+1)*((j : ℝ)+2))) =
      1-1/((n : ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have hcast : (n : ℝ)+1+1 = (n : ℝ)+2 := by ring
    rw [hcast]
    field_simp [show (n : ℝ)+1 ≠ 0 by positivity, show (n : ℝ)+2 ≠ 0 by positivity]
    ring

/-- Elementary summability for fourth-moment tails; no asymptotic p-series
comparison is needed. -/
theorem summable_inverse_successor_product :
    Summable (fun n : ℕ ↦ 1 / (((n : ℝ)+1)*((n : ℝ)+2))) := by
  apply summable_of_sum_range_le (fun n ↦ by positivity)
  intro n
  rw [inverse_successor_product_sum n]
  exact sub_le_self _ (by positivity)

/-- A fourth-moment Markov bound for nonnegative random variables. All
integrability and probability assumptions are explicit. -/
theorem measure_ge_le_of_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (hint : Integrable (fun ω ↦ f ω^4) μ) (eps : ℝ) (heps : 0 < eps) :
    μ {ω | eps ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω^4 ∂μ)/eps^4) := by
  have hevent : {ω | eps ≤ f ω} = {ω | eps^4 ≤ f ω^4} := by
    ext ω
    exact (pow_le_pow_iff_left₀ heps.le (hf ω) (by decide : 4 ≠ 0)).symm
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω ↦ pow_nonneg (hf ω) 4)) hint (eps^4)
  rw [← hevent] at hmark
  have hreal : (μ {ω | eps ≤ f ω}).toReal ≤ (∫ ω, f ω^4 ∂μ)/eps^4 := by
    apply (le_div_iff₀ (pow_pos heps 4)).mpr
    simpa only [measureReal_def, mul_comm] using hmark
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
    (div_nonneg (integral_nonneg (fun ω ↦ pow_nonneg (hf ω) 4)) (pow_nonneg heps.le 4))).mpr hreal

/-- Exact fourth-moment zero-signal tail bound for every independent
randomized unit estimator under the actual product experiment. -/
theorem zeroSignal_estimator_fourth_tail {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (hN : 0 < N)
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est)
    (eps : ℝ) (heps : 0 < eps) :
    ((Model.experimentLaw N k).prod ν) {z | eps ≤
      |inner ℝ (est (Model.observation 0 z.1) z.2) z.1.1|} ≤
      ENNReal.ofReal ((3/((N : ℝ)*((N : ℝ)+2)))/eps^4) := by
  have h := measure_ge_le_of_fourth_moment ((Model.experimentLaw N k).prod ν)
    (fun z ↦ |inner ℝ (est (Model.observation 0 z.1) z.2) z.1.1|)
    (fun _ ↦ abs_nonneg _) (Geometry.estimator_overlap_power_integrable ν hN est hest 0 4)
    eps heps
  change ((Model.experimentLaw N k).prod ν) _ ≤
    ENNReal.ofReal (Model.expectedOverlapPower N k 0 est ν 4/eps^4) at h
  rw [Geometry.zeroSignal_estimator_fourth_moment ν hN est hest] at h
  exact h

/-- Fourth-moment zero-signal overlap tails are summable for every actual
estimator coupling. The estimator need not be an MLE, and the coupling need
not be independent between dimensions. -/
theorem zeroSignal_overlap_summable_tails {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {E : Statements.PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    [∀ n, IsProbabilityMeasure (ν n)] (R : Statements.EstimatorCoupling E A ν)
    (eps : ℝ) (heps : 0 < eps) :
    (∑' n : ℕ, μ {ω | eps ≤ Statements.sampleOverlap R 0 n ω}) ≠ ∞ := by
  let C : ℝ := 3/eps^4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := summable_inverse_successor_product.mul_left C
  apply ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  have hF : Measurable (fun z : (Model.Vector (n+1) × Model.Tensor (n+1) k) × A n ↦
      |inner ℝ (R.estimator n (Model.observation 0 z.1) z.2) z.1.1|) :=
    continuous_abs.measurable.comp (continuous_inner.measurable.comp
      (((R.unit n).1.comp (((Model.measurable_observation (n+1) k 0).comp measurable_fst).prodMk
        measurable_snd)).prodMk (measurable_fst.comp measurable_fst)))
  have hset : MeasurableSet {z : (Model.Vector (n+1) × Model.Tensor (n+1) k) × A n |
      eps ≤ |inner ℝ (R.estimator n (Model.observation 0 z.1) z.2) z.1.1|} :=
    measurableSet_le measurable_const hF
  have hmap := Measure.map_apply (μ := μ) ((E.measurable n).prodMk (R.measurable n)) hset
  rw [R.independentLaw n] at hmap
  have hcompare : (3/(((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+2)))/eps^4 ≤
      C*(1/(((n : ℝ)+1)*((n : ℝ)+2))) := by
    have hden : 0 < ((n : ℝ)+1)*((n : ℝ)+2) := by positivity
    have hprod : ((n : ℝ)+1)*((n : ℝ)+2) ≤ ((n : ℝ)+1)*((n : ℝ)+3) := by
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have hinv := one_div_le_one_div_of_le hden hprod
    calc
      _ = C*(1/(((n : ℝ)+1)*((n : ℝ)+3))) := by dsimp [C]; push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hC
  calc
    _ = ((Model.experimentLaw (n+1) k).prod (ν n)) {z | eps ≤
        |inner ℝ (R.estimator n (Model.observation 0 z.1) z.2) z.1.1|} := hmap.symm
    _ ≤ ENNReal.ofReal ((3/(((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+2)))/eps^4) :=
      zeroSignal_estimator_fourth_tail (ν n) (Nat.succ_pos n) (R.estimator n) (R.unit n) eps heps
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcompare

/-- Absolute zero-signal overlap tends to zero almost surely for every
independently randomized unit estimator under every actual physical coupling. -/
theorem sampleOverlap_zero_ae {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {E : Statements.PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    [∀ n, IsProbabilityMeasure (ν n)] (R : Statements.EstimatorCoupling E A ν) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleOverlap R 0 n ω) atTop (𝓝 0) :=
  LimitTools.ae_tendsto_zero_of_summable_tails μ
    (fun n ω ↦ Statements.sampleOverlap R 0 n ω) (fun _ _ ↦ abs_nonneg _)
    (zeroSignal_overlap_summable_tails R)

end TensorPCA.ZeroSignalProofs
