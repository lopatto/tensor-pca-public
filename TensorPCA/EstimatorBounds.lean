-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.OddValidationProofs
public import TensorPCA.Statistical

/-! # Finite absolute-overlap bounds and Hölder's inequality -/
@[expose] public section

namespace TensorPCA.EstimatorBounds

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

theorem overlap_memLp {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) (p : ℝ≥0∞) :
    MemLp (fun z ↦ |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1|)
      p ((Model.experimentLaw N k).prod ν) := by
  have hv : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      est (Model.observation lam z.1) z.2) :=
    hest.1.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk measurable_snd)
  have hx : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦ z.1.1) :=
    measurable_fst.comp measurable_fst
  have hi : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      inner ℝ (est (Model.observation lam z.1) z.2) z.1.1) :=
    Continuous.measurable2 (continuous_inner (𝕜 := ℝ)) hv hx
  have hf : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1|) := continuous_abs.measurable.comp hi
  apply MemLp.of_bound hf.aestronglyMeasurable 1
  have hx_unit : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ‖z.1.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (OddValidationProofs.experiment_vector_norm_ae hN)
  filter_upwards [hx_unit] with z hz
  simpa only [Real.norm_eq_abs, abs_abs, hest.2 _ _, hz, one_mul] using
    abs_real_inner_le_norm (est (Model.observation lam z.1) z.2) z.1.1

/-- The first absolute-overlap moment is bounded by the kth-moment root. -/
theorem expectedOverlapPower_one_le_rpow {N k : ℕ} (hN : 0 < N) (hk : 1 < k) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k lam est ν 1 ≤
      (Model.expectedOverlapPower N k lam est ν k) ^ ((k : ℝ)⁻¹) := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast hk
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (Model.experimentLaw N k).prod ν) (p := (k : ℝ)) (q := Real.conjExponent (k : ℝ))
    (f := fun z ↦ |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1|)
    (g := fun _ ↦ (1 : ℝ)) (Real.HolderConjugate.conjExponent hkR)
    (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (overlap_memLp hN lam ν est hest _)
    (memLp_const (1 : ℝ))
  simpa only [Model.expectedOverlapPower, pow_one, mul_one, Real.rpow_natCast,
    Real.one_rpow, integral_const, probReal_univ, one_smul, one_div] using h

theorem expectedOverlapPower_nonneg (N k : ℕ) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A)
    (est : Model.Estimator N k A) (p : ℕ) :
    0 ≤ Model.expectedOverlapPower N k lam est ν p :=
  integral_nonneg fun _ ↦ pow_nonneg (abs_nonneg _) _

theorem expectedOverlapPower_one_le_validationRoot {N k : ℕ} (hN : 0 < N) (hk : 1 < k)
    (lam delta : ℝ) (hdelta : 0 < delta)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k lam est ν 1 ≤ Statistical.validationRootEnvelope N k lam delta := by
  apply (expectedOverlapPower_one_le_rpow hN hk lam ν est hest).trans
  exact Real.rpow_le_rpow (expectedOverlapPower_nonneg N k lam ν est k)
    (OddValidationProofs.expectedOverlapPower_le_validation hN lam delta hdelta ν est hest)
    (by positivity)

/-- All finite estimator inequalities in the checked reduction now follow from
the proved posterior, Gaussian validation and Hölder arguments. -/
theorem finiteEstimatorBounds (k : ℕ) (hk : 1 < k) (lam : ℝ)
    (A : ℕ → Type*) [∀ n, MeasurableSpace (A n)]
    (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
    (est : ∀ n, Model.Estimator (n + 1) k (A n))
    (hest : ∀ n, Model.IsUnitEstimator (est n)) :
    Statistical.FiniteEstimatorBounds k lam ν est := by
  intro delta hdelta _ n
  constructor
  · exact OddValidationProofs.expectedOverlapPower_le_validation (Nat.succ_pos n)
      lam delta hdelta (ν n) (est n) (hest n)
  · exact expectedOverlapPower_one_le_validationRoot (Nat.succ_pos n) hk
      lam delta hdelta (ν n) (est n) (hest n)


end TensorPCA.EstimatorBounds
