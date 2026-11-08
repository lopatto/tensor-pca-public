-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianTensorMomentProofs
public import TensorPCA.TensorTupleCountProofs
public import TensorPCA.TensorChannelInformationProofs

/-!
# Discarding repeated ordered tensor coordinates

The retained channel consists of all injective ordered tuples. Its Gaussian
noise law and the free-energy comparison are concrete consequences of coordinate restriction; the lost signal energy is O(1/N) at fixed order.
-/
@[expose] public section

namespace TensorPCA.OrderedTensorComparisonProofs

open MeasureTheory ProbabilityTheory Filter GaussianPriorTransferProofs GaussianTensorMomentProofs
  GaussianCoordinateProjectionProofs SphericalGaussianTransferProofs TensorChannelInformationProofs
  TensorTupleCountProofs
open scoped ENNReal RealInnerProductSpace Classical Topology

noncomputable def distinctTupleEmbedding (N k : ℕ) :
    {i : Fin k → Fin N // Function.Injective i} ↪ (Fin k → Fin N) := ⟨Subtype.val, Subtype.val_injective⟩

noncomputable def distinctPriorFreeEnergy (N k : ℕ) (gamma : ℝ) : ℝ :=
  mixtureFreeEnergy (stdGaussian (Model.Vector N))
    (coordinateProjection (distinctTupleEmbedding N k) ∘ gaussianSignal N k gamma) / N

theorem missing_coordinates_eq_repeated (N k : ℕ) :
    Finset.univ.filter (fun i ↦ i ∉ Set.range (distinctTupleEmbedding N k)) = repeatedTuples N k := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, repeatedTuples]
  constructor
  · intro h hi
    exact h ⟨⟨i, hi⟩, rfl⟩
  · intro h ⟨j, hj⟩
    apply h
    exact hj ▸ j.2

theorem scalar_moment_nonneg (k : ℕ) : 0 ≤ GaussianMomentProofs.radialMomentProduct 1 k := by
  rw [← integral_scalar_even_power k]
  apply integral_nonneg
  intro x
  change (0 : ℝ) ≤ x ^ (2*k)
  simpa only [← pow_mul] using pow_nonneg (sq_nonneg x) k

theorem integral_repeated_coordinate_energy_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    (∫ g : Model.Vector N, ∑ i ∈ repeatedTuples N k, gaussianFeature N k g i ^ 2
      ∂stdGaussian (Model.Vector N)) ≤
      (k : ℝ) ^ 3 * GaussianMomentProofs.radialMomentProduct 1 k / N := by
  have hmoment := integral_gaussianFeature_coordinate_sum_le hk (repeatedTuples N k)
  have hcount : ((repeatedTuples N k).card : ℝ) ≤ (k : ℝ) ^ 2 * (N : ℝ) ^ (k-1) := by
    exact_mod_cast repeatedTuples_card_le N k
  have hM := scalar_moment_nonneg k
  have hc : 0 ≤ (k : ℝ) * GaussianMomentProofs.radialMomentProduct 1 k / (N : ℝ) ^ k := by positivity
  apply hmoment.trans ((mul_le_mul_of_nonneg_right hcount hc).trans_eq _)
  have hNz : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hpow : (N : ℝ) ^ k = (N : ℝ) ^ (k-1) * N := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp [hNz]

theorem full_distinct_freeEnergy_bounds {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    0 ≤ gaussianPriorFreeEnergy N k gamma-distinctPriorFreeEnergy N k gamma ∧
    gaussianPriorFreeEnergy N k gamma-distinctPriorFreeEnergy N k gamma ≤
      (gamma / 2 * (k : ℝ) ^ 3 * GaussianMomentProofs.radialMomentProduct 1 k) / N := by
  have h := discarded_coordinate_freeEnergy_bounds (stdGaussian (Model.Vector N))
    (gaussianSignal N k gamma) (measurable_gaussianSignal N k gamma)
    (gaussianSignal_memLp_two hN gamma) (distinctTupleEmbedding N k)
  have hrange : Set.range (distinctTupleEmbedding N k) =
      {i : Fin k → Fin N | Function.Injective i} := Subtype.range_val_subtype
  simp only [hrange, Set.mem_ofPred_eq] at h
  change
      0 ≤ mixtureFreeEnergy (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma) -
        mixtureFreeEnergy (stdGaussian (Model.Vector N))
          (coordinateProjection (distinctTupleEmbedding N k) ∘ gaussianSignal N k gamma) ∧
      mixtureFreeEnergy (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma) -
        mixtureFreeEnergy (stdGaussian (Model.Vector N))
          (coordinateProjection (distinctTupleEmbedding N k) ∘ gaussianSignal N k gamma) ≤
        (1 / 2 : ℝ) * ∫ g : Model.Vector N, ∑ i ∈ repeatedTuples N k,
          gaussianSignal N k gamma g i ^ 2 ∂stdGaussian (Model.Vector N) at h
  have hs (g : Model.Vector N) (i : Fin k → Fin N) :
      gaussianSignal N k gamma g i ^ 2 = (gamma * (N : ℝ)) * gaussianFeature N k g i ^ 2 := by
    change ((Real.sqrt gamma * Real.sqrt N) * gaussianFeature N k g i) ^ 2 = _
    rw [mul_pow, mul_pow, Real.sq_sqrt hgamma, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp_rw [hs, ← Finset.mul_sum] at h
  rw [integral_const_mul] at h
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdiff : gaussianPriorFreeEnergy N k gamma-distinctPriorFreeEnergy N k gamma =
      (mixtureFreeEnergy (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma) -
        mixtureFreeEnergy (stdGaussian (Model.Vector N))
          (coordinateProjection (distinctTupleEmbedding N k) ∘ gaussianSignal N k gamma)) / N := by
    rw [gaussianPriorFreeEnergy, distinctPriorFreeEnergy, ← sub_div]
    rfl
  rw [hdiff]
  constructor
  · exact div_nonneg h.1 hNpos.le
  · have hdiv := div_le_div_of_nonneg_right h.2 hNpos.le
    have hc : ((1 / 2 : ℝ) * (gamma * N *
        (∫ g : Model.Vector N, ∑ i ∈ repeatedTuples N k, gaussianFeature N k g i ^ 2
          ∂stdGaussian (Model.Vector N)))) / N =
        gamma / 2 * (∫ g : Model.Vector N, ∑ i ∈ repeatedTuples N k, gaussianFeature N k g i ^ 2
          ∂stdGaussian (Model.Vector N)) := by field_simp [hNpos.ne']
    rw [hc] at hdiv
    apply hdiv.trans
    have henergy := mul_le_mul_of_nonneg_left (integral_repeated_coordinate_energy_le hN hk)
      (div_nonneg hgamma (by norm_num : (0 : ℝ) ≤ 2))
    convert henergy using 1
    ring

/-- Repeated ordered coordinates do not change the fixed-strength limiting
free energy of the actual Gaussian-prior tensor channel. -/
theorem full_sub_distinct_tendsto (k : ℕ) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    Tendsto (fun n : ℕ ↦ gaussianPriorFreeEnergy (n+1) k gamma-distinctPriorFreeEnergy (n+1) k gamma)
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ by exact_mod_cast Nat.le_succ n)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero (fun n ↦ (full_distinct_freeEnergy_bounds (Nat.succ_pos n) hk hgamma).1)
    (fun n ↦ (full_distinct_freeEnergy_bounds (Nat.succ_pos n) hk hgamma).2)
  exact hn.const_div_atTop _


end TensorPCA.OrderedTensorComparisonProofs
