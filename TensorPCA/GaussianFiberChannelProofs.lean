-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianCoordinateProjectionProofs

/-!
# Gaussian aggregation over equal finite fibers

A normalized sum over a fiber of size m gains sqrt(m) in signal strength and
retains canonical Gaussian noise. The remaining orthogonal coordinates have
zero signal and therefore zero free-energy cost.
-/
@[expose] public section

namespace TensorPCA.GaussianFiberChannelProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
  GaussianChannelProjectionProofs GaussianCoordinateProjectionProofs
open scoped ENNReal RealInnerProductSpace Classical

theorem sum_comp_eq_card_mul {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → beta) (m : ℕ) (hcard : ∀ b, Fintype.card {a : alpha // f a = b} = m)
    (z : beta → ℝ) : (∑ a, z (f a)) = (m : ℝ) * ∑ b, z b := by
  rw [← Fintype.sum_fiberwise' f z]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [Finset.mul_sum]

noncomputable def fiberLinearMap {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → beta) (m : ℕ) : EuclideanSpace ℝ beta →ₗ[ℝ] EuclideanSpace ℝ alpha where
  toFun y := WithLp.toLp 2 (fun a ↦ (Real.sqrt m)⁻¹ * y (f a))
  map_add' y z := by
    ext a
    change (Real.sqrt m)⁻¹ * (y (f a)+z (f a)) = _
    exact mul_add _ _ _
  map_smul' r y := by
    ext a
    change (Real.sqrt m)⁻¹ * (r * y (f a)) = r * ((Real.sqrt m)⁻¹ * y (f a))
    ring

theorem fiberLinearMap_inner {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → beta) {m : ℕ} (hm : 0 < m)
    (hcard : ∀ b, Fintype.card {a : alpha // f a = b} = m)
    (y z : EuclideanSpace ℝ beta) :
    inner ℝ (fiberLinearMap f m y) (fiberLinearMap f m z) = inner ℝ y z := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  change (∑ a, ((Real.sqrt m)⁻¹ * y (f a)) * ((Real.sqrt m)⁻¹ * z (f a))) = ∑ b, y b * z b
  calc
    _ = ((Real.sqrt m)⁻¹) ^ 2 * ∑ a, y (f a) * z (f a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [sum_comp_eq_card_mul f m hcard (fun b ↦ y b*z b), inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg m), ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_pos.mpr hm : (0 : ℝ) < m).ne', one_mul]

noncomputable def fiberEmbedding {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → beta) {m : ℕ} (hm : 0 < m)
    (hcard : ∀ b, Fintype.card {a : alpha // f a = b} = m) :
    EuclideanSpace ℝ beta →ₗᵢ[ℝ] EuclideanSpace ℝ alpha :=
  (fiberLinearMap f m).isometryOfInner (fiberLinearMap_inner f hm hcard)

theorem fiberEmbedding_apply {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → beta) {m : ℕ} (hm : 0 < m)
    (hcard : ∀ b, Fintype.card {a : alpha // f a = b} = m)
    (y : EuclideanSpace ℝ beta) (a : alpha) :
    fiberEmbedding f hm hcard y a = (Real.sqrt m)⁻¹ * y (f a) := rfl

theorem fiberEmbedding_sqrt_smul {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → beta) {m : ℕ} (hm : 0 < m)
    (hcard : ∀ b, Fintype.card {a : alpha // f a = b} = m)
    (y : EuclideanSpace ℝ beta) :
    fiberEmbedding f hm hcard (Real.sqrt m • y) = WithLp.toLp 2 (fun a ↦ y (f a)) := by
  ext a
  rw [fiberEmbedding_apply]
  change (Real.sqrt m)⁻¹ * (Real.sqrt m * y (f a)) = y (f a)
  rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne', one_mul]

/-- Adding Gaussian coordinates orthogonal to the signal changes no free
energy. The proof uses the actual Gaussian noise transport and both checked
information-theoretic data-processing inequalities. -/
theorem mixtureFreeEnergy_isometricImage {Omega E D : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (U : Omega → D) (hU : Measurable U) (hU2 : MemLp U 2 mu) (I : D →ₗᵢ[ℝ] E) :
    mixtureFreeEnergy mu (I ∘ U) = mixtureFreeEnergy mu U := by
  have hIU : Measurable (I ∘ U) := I.continuous.measurable.comp hU
  have hIU2 : MemLp (I ∘ U) 2 mu := I.toContinuousLinearMap.comp_memLp' hU2
  have hproj (x) : I.toContinuousLinearMap.adjoint (I (U x)) = U x := by
    have h := congrArg (fun L : D →L[ℝ] D ↦ L (U x)) I.adjoint_comp_self
    exact h
  have heq : I.toContinuousLinearMap.adjoint ∘ (I ∘ U) = U := funext hproj
  have h := discarded_channel_freeEnergy_bounds mu (I ∘ U) hIU hIU2 I.toContinuousLinearMap.adjoint
    (stdGaussian_map_adjoint I)
  rw [heq] at h
  simp only [Function.comp_apply, hproj, I.norm_map, sub_self, integral_zero, mul_zero] at h
  exact le_antisymm (sub_nonpos.mp h.2) (sub_nonneg.mp h.1)


end TensorPCA.GaussianFiberChannelProofs
