-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianFiberChannelProofs
public import TensorPCA.OrderedTensorComparisonProofs
public import TensorPCA.TensorOrbitCountProofs

/-!
# Exact k-factorial tensor-channel aggregation

Injective ordered tuples are grouped by their unordered range. Every
fiber has k! elements, so normalized aggregation gains sqrt(k!) in signal while
retaining canonical Gaussian noise. The orthogonal directions have zero signal.
-/
@[expose] public section

namespace TensorPCA.TensorOrbitAggregationProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianFiberChannelProofs
  GaussianCoordinateProjectionProofs OrderedTensorComparisonProofs TensorOrbitCountProofs
  TensorChannelInformationProofs SphericalGaussianTransferProofs
open scoped ENNReal RealInnerProductSpace Classical Topology

noncomputable def orbitEmbedding (N k : ℕ) :
    EuclideanSpace ℝ (KSubset N k) →ₗᵢ[ℝ] EuclideanSpace ℝ (DistinctTuple N k) :=
  fiberEmbedding tupleRange (Nat.factorial_pos k)
    (fun S ↦ by simpa only [Fintype.card_eq_nat_card] using tupleRange_fiber_card S)

noncomputable def aggregateCoefficient (N k : ℕ) (gamma : ℝ) : ℝ :=
  Real.sqrt (Nat.factorial k) * (Real.sqrt gamma * Real.sqrt N) * ((Real.sqrt N)⁻¹) ^ k

noncomputable def unorderedSignal (N k : ℕ) (gamma : ℝ) (g : Model.Vector N) :
    EuclideanSpace ℝ (KSubset N k) :=
  WithLp.toLp 2 (fun S ↦ aggregateCoefficient N k gamma * ∏ n ∈ S.1, g n)

noncomputable def unorderedPriorFreeEnergy (N k : ℕ) (gamma : ℝ) : ℝ :=
  mixtureFreeEnergy (stdGaussian (Model.Vector N)) (unorderedSignal N k gamma) / N

theorem orbitEmbedding_signal (N k : ℕ) (gamma : ℝ) (g : Model.Vector N) :
    orbitEmbedding N k (unorderedSignal N k gamma g) =
      coordinateProjection (distinctTupleEmbedding N k) (gaussianSignal N k gamma g) := by
  ext i
  rw [orbitEmbedding, fiberEmbedding_apply, coordinateProjection_apply]
  change (Real.sqrt (Nat.factorial k))⁻¹ *
      (aggregateCoefficient N k gamma * ∏ n ∈ (tupleRange i).1, g n) =
      (Real.sqrt gamma * Real.sqrt N) * gaussianFeature N k g i.1
  rw [gaussianFeature, Geometry.feature_smul]
  change (Real.sqrt (Nat.factorial k))⁻¹ *
      (aggregateCoefficient N k gamma * ∏ n ∈ (tupleRange i).1, g n) =
      (Real.sqrt gamma * Real.sqrt N) * (((Real.sqrt N)⁻¹) ^ k * ∏ j : Fin k, g (i.1 j))
  rw [prod_tuple_eq_prod_range]
  unfold aggregateCoefficient
  have hfac : Real.sqrt (Nat.factorial k) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos k))).ne'
  field_simp [hfac]

theorem adjoint_distinct_signal (N k : ℕ) (gamma : ℝ) :
    (orbitEmbedding N k).toContinuousLinearMap.adjoint ∘
      (coordinateProjection (distinctTupleEmbedding N k) ∘ gaussianSignal N k gamma) =
        unorderedSignal N k gamma := by
  funext g
  rw [Function.comp_apply, Function.comp_apply, ← orbitEmbedding_signal N k gamma g]
  exact congrArg (fun L : EuclideanSpace ℝ (KSubset N k) →L[ℝ] EuclideanSpace ℝ (KSubset N k) ↦
    L (unorderedSignal N k gamma g)) (orbitEmbedding N k).adjoint_comp_self

theorem measurable_unorderedSignal (N k : ℕ) (gamma : ℝ) : Measurable (unorderedSignal N k gamma) := by
  rw [← adjoint_distinct_signal N k gamma]
  exact (orbitEmbedding N k).toContinuousLinearMap.adjoint.continuous.measurable.comp
    ((coordinateProjection (distinctTupleEmbedding N k)).continuous.measurable.comp
      (measurable_gaussianSignal N k gamma))

theorem unorderedSignal_memLp_two {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    MemLp (unorderedSignal N k gamma) 2 (stdGaussian (Model.Vector N)) := by
  rw [← adjoint_distinct_signal N k gamma]
  exact (orbitEmbedding N k).toContinuousLinearMap.adjoint.comp_memLp'
    ((coordinateProjection (distinctTupleEmbedding N k)).comp_memLp' (gaussianSignal_memLp_two hN gamma))

/-- Exact equality: all k! ordered observations of the same monomial aggregate
into one independent canonical Gaussian channel with sqrt(k!) larger signal. -/
theorem distinct_freeEnergy_eq_unordered {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    distinctPriorFreeEnergy N k gamma = unorderedPriorFreeEnergy N k gamma := by
  have heq : (orbitEmbedding N k) ∘ unorderedSignal N k gamma =
      coordinateProjection (distinctTupleEmbedding N k) ∘ gaussianSignal N k gamma := by
    funext g
    exact orbitEmbedding_signal N k gamma g
  unfold distinctPriorFreeEnergy unorderedPriorFreeEnergy
  rw [← heq, mixtureFreeEnergy_isometricImage (stdGaussian (Model.Vector N))
    (unorderedSignal N k gamma) (measurable_unorderedSignal N k gamma) (unorderedSignal_memLp_two hN gamma)]

theorem aggregateCoefficient_eq_sqrt {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    aggregateCoefficient N k gamma = Real.sqrt ((Nat.factorial k : ℝ) * gamma / (N : ℝ) ^ (k-1)) := by
  have hc : 0 ≤ aggregateCoefficient N k gamma := by unfold aggregateCoefficient; positivity
  have hrhs : 0 ≤ (Nat.factorial k : ℝ) * gamma / (N : ℝ) ^ (k-1) := by positivity
  apply (sq_eq_sq₀ hc (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hrhs]
  have hnorm : (((Real.sqrt N)⁻¹) ^ k) ^ 2 = ((N : ℝ) ^ k)⁻¹ := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N), inv_pow]
  have hpow : (N : ℝ) ^ k = (N : ℝ) ^ (k-1) * N := by rw [← pow_succ]; congr 1; omega
  calc
    _ = (Real.sqrt (Nat.factorial k)) ^ 2 * (Real.sqrt gamma) ^ 2 * (Real.sqrt N) ^ 2 *
        ((((Real.sqrt N)⁻¹) ^ k) ^ 2) := by unfold aggregateCoefficient; ring
    _ = _ := by
      rw [Real.sq_sqrt (Nat.cast_nonneg (Nat.factorial k)), Real.sq_sqrt hgamma,
        Real.sq_sqrt (Nat.cast_nonneg N), hnorm, hpow]
      field_simp [(Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne']

/-- The standardized coefficient in the external product-prior convention,
whose scalar noise variance is Delta=1/(k*gamma). -/
theorem aggregateCoefficient_eq_source {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    aggregateCoefficient N k gamma = Real.sqrt ((Nat.factorial (k-1) : ℝ) /
      ((N : ℝ) ^ (k-1) * (1 / ((k : ℝ) * gamma)))) := by
  rw [aggregateCoefficient_eq_sqrt hN hk hgamma.le]
  congr 1
  have hfact : (Nat.factorial k : ℝ) = (k : ℝ) * (Nat.factorial (k-1) : ℝ) := by
    have h := Nat.factorial_succ (k-1)
    rw [Nat.sub_add_cancel hk] at h
    exact_mod_cast h
  rw [hfact]
  field_simp [(Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne',
    (Nat.cast_pos.mpr hk : (0 : ℝ) < k).ne', hgamma.ne']


end TensorPCA.TensorOrbitAggregationProofs
