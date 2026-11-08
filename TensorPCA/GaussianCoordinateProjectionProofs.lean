-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianChannelProjectionProofs
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite Gaussian coordinate projections

Extension by zero is a linear isometric embedding. Its adjoint is precisely
coordinate restriction and maps canonical Gaussian noise to canonical Gaussian
noise. Thus the generic retained-channel premise is proved for subsets of the ordered tensor coordinates.
-/
@[expose] public section

namespace TensorPCA.GaussianCoordinateProjectionProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
  GaussianChannelProjectionProofs
open scoped ENNReal RealInnerProductSpace Classical

theorem stdGaussian_map_adjoint {E D : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D] (I : D →ₗᵢ[ℝ] E) :
    (stdGaussian E).map I.toContinuousLinearMap.adjoint = stdGaussian D := by
  apply Measure.ext_of_charFunDual
  funext L
  have hnorm : ‖L.comp I.toContinuousLinearMap.adjoint‖ = ‖L‖ := by
    let v := (InnerProductSpace.toDual ℝ D).symm L
    have hrep : L.comp I.toContinuousLinearMap.adjoint = innerSL ℝ (I v) := by
      ext x
      change L (I.toContinuousLinearMap.adjoint x) = inner ℝ (I v) x
      rw [← InnerProductSpace.toDual_symm_apply]
      exact I.toContinuousLinearMap.adjoint_inner_right v x
    rw [hrep, innerSL_apply_norm, I.norm_map]
    exact (InnerProductSpace.toDual ℝ D).symm.norm_map L
  rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian, hnorm]

noncomputable def coordinateEmbedding {alpha iota : Type*} [Fintype alpha] [Fintype iota]
    (i : alpha ↪ iota) : EuclideanSpace ℝ alpha →ₗᵢ[ℝ] EuclideanSpace ℝ iota :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ i

noncomputable def coordinateProjection {alpha iota : Type*} [Fintype alpha] [Fintype iota]
    (i : alpha ↪ iota) : EuclideanSpace ℝ iota →L[ℝ] EuclideanSpace ℝ alpha :=
  (coordinateEmbedding i).toContinuousLinearMap.adjoint

theorem coordinateProjection_apply {alpha iota : Type*} [Fintype alpha] [Fintype iota]
    (i : alpha ↪ iota) (z : EuclideanSpace ℝ iota) (a : alpha) : coordinateProjection i z a = z (i a) := by
  classical
  calc
    _ = inner ℝ (EuclideanSpace.basisFun alpha ℝ a) (coordinateProjection i z) :=
      (EuclideanSpace.basisFun_inner alpha ℝ (coordinateProjection i z) a).symm
    _ = inner ℝ (coordinateEmbedding i (EuclideanSpace.basisFun alpha ℝ a)) z :=
      (coordinateEmbedding i).toContinuousLinearMap.adjoint_inner_right _ _
    _ = _ := by
      simp only [coordinateEmbedding, EuclideanSpace.basisFun_apply,
        LinearIsometry.piLpExtendByZero_apply_single, EuclideanSpace.inner_single_left,
        conj_trivial, one_mul]

theorem coordinateProjection_noiseLaw {alpha iota : Type*} [Fintype alpha] [Fintype iota]
    (i : alpha ↪ iota) :
    (stdGaussian (EuclideanSpace ℝ iota)).map (coordinateProjection i) =
      stdGaussian (EuclideanSpace ℝ alpha) := stdGaussian_map_adjoint (coordinateEmbedding i)

theorem norm_sq_sub_projection {alpha iota : Type*} [Fintype alpha] [Fintype iota]
    (i : alpha ↪ iota) (z : EuclideanSpace ℝ iota) :
    ‖z‖ ^ 2-‖coordinateProjection i z‖ ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j ↦ j ∉ Set.range i), z j ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [coordinateProjection_apply]
  have hretained : (∑ j ∈ Finset.univ.filter (fun j ↦ j ∈ Set.range i), z j ^ 2) =
      ∑ a : alpha, z (i a) ^ 2 := by
    have hset : Finset.univ.filter (fun j ↦ j ∈ Set.range i) = Finset.univ.image i := by
      ext j
      simp
    rw [hset, Finset.sum_image]
    exact fun a _ b _ hab ↦ i.injective hab
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j ↦ j ∈ Set.range i) (fun j ↦ z j ^ 2)
  rw [hretained] at hsplit
  linarith

/-- Actual retained-coordinate comparison, with its Gaussian-noise transport
proved and the discarded energy written as the concrete coordinate sum. -/
theorem discarded_coordinate_freeEnergy_bounds {Omega alpha iota : Type*} [MeasurableSpace Omega]
    [Fintype alpha] [Fintype iota] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → EuclideanSpace ℝ iota) (hF : Measurable F) (hF2 : MemLp F 2 mu) (i : alpha ↪ iota) :
    0 ≤ mixtureFreeEnergy mu F-mixtureFreeEnergy mu (coordinateProjection i ∘ F) ∧
    mixtureFreeEnergy mu F-mixtureFreeEnergy mu (coordinateProjection i ∘ F) ≤
      (1 / 2 : ℝ) * ∫ x, ∑ j ∈ Finset.univ.filter (fun j ↦ j ∉ Set.range i), F x j ^ 2 ∂mu := by
  have h := discarded_channel_freeEnergy_bounds mu F hF hF2 (coordinateProjection i)
    (coordinateProjection_noiseLaw i)
  simpa only [norm_sq_sub_projection] using h


end TensorPCA.GaussianCoordinateProjectionProofs
