-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityKernelStabilityProofs
public import TensorPCA.FinitePriorCavityPathProofs
public import TensorPCA.GaussianTensorMomentProofs
public import TensorPCA.GaussianFiberChannelProofs

/-! Finite Bayesian free-energy stability in the base cross-kernel L2 metric. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityFreeEnergyComparisonProofs
open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorCavityKernelDerivativeProofs FinitePriorCavityKernelStabilityProofs FinitePriorCavityPathProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega iota kappa : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype iota] [Fintype kappa] [DecidableEq iota] [DecidableEq kappa]

/-- Actual Bayesian free energies are close when their cross kernels are close
in L2 under the actual base prior. All posterior and Gaussian estimates are
proved; the bound is uniform in the two signal dimensions. -/
theorem abs_freeEnergy_sub_le_kernel_l2 (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, ‖B x‖ ≤ CB) :
    |mixtureFreeEnergy q A-mixtureFreeEnergy q B| ≤
      (1/2 : ℝ)*Real.exp (22*(CA+CB)^2)*Real.sqrt (∫ p, (kernelDifference A B p)^2 ∂q.prod q) := by
  let df : ℝ → ℝ := fun t ↦ (1/2 : ℝ)*∫ y, ∫ p, kernelDifference A B p
    ∂(posteriorKernel q (interpolatedSignal A B t) y).prod (posteriorKernel q (interpolatedSignal A B t) y)
    ∂mixtureLaw q (interpolatedSignal A B t)
  apply abs_freeEnergy_sub_le_of_guerraPath_derivative q A B hA hB hCA hCB
    (Filter.Eventually.of_forall hbA) (Filter.Eventually.of_forall hbB) (df := df)
  · intro t ht
    exact guerraPath_hasDerivAt_kernel q A B hA hB hCA hCB hbA hbB ht.1 ht.2
  · intro t ht
    change |(1/2 : ℝ)*(∫ y, ∫ p, kernelDifference A B p
      ∂(posteriorKernel q (interpolatedSignal A B t) y).prod (posteriorKernel q (interpolatedSignal A B t) y)
      ∂mixtureLaw q (interpolatedSignal A B t))| ≤ _
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    exact (mul_le_mul_of_nonneg_left (guerraPath_kernel_bound q A B hA hB hCA hCB hbA hbB ⟨ht.1.le,ht.2.le⟩)
      (by norm_num : (0 : ℝ) ≤ 1/2)).trans_eq (by ring)

/-- The scalar comparison target retains the literal real channel used by
the manuscript's RS potential. The canonical one-coordinate isometry transports
both its free energy and its cross kernel exactly. -/
theorem abs_freeEnergy_sub_le_kernel_l2_real (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → ℝ)
    (hA : Measurable A) (hB : Measurable B) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, |B x| ≤ CB) :
    |mixtureFreeEnergy q A-mixtureFreeEnergy q B| ≤
      (1/2 : ℝ)*Real.exp (22*(CA+CB)^2)*Real.sqrt
        (∫ p : Omega × Omega, (inner ℝ (A p.1) (A p.2)-B p.1*B p.2)^2 ∂q.prod q) := by
  let I := GaussianTensorMomentProofs.coordinateLine (0 : Fin 1)
  have hG : Measurable (I ∘ B) := I.continuous.measurable.comp hB
  have hGN (x : Omega) : ‖(I ∘ B) x‖ ≤ CB := by
    change ‖I (B x)‖ ≤ CB
    rw [I.norm_map,Real.norm_eq_abs]
    exact hbB x
  have hB2 : MemLp B 2 q := MemLp.of_bound hB.aestronglyMeasurable CB (Filter.Eventually.of_forall hbB)
  have H := abs_freeEnergy_sub_le_kernel_l2 q A (I ∘ B) hA hG hCA hCB hbA hGN
  rw [GaussianFiberChannelProofs.mixtureFreeEnergy_isometricImage q B hB hB2 I] at H
  have hKernel : kernelDifference A (I ∘ B) = fun p : Omega × Omega ↦ inner ℝ (A p.1) (A p.2)-B p.1*B p.2 := by
    funext p
    change inner ℝ (A p.1) (A p.2)-inner ℝ (I (B p.1)) (I (B p.2)) = _
    rw [I.inner_map_map]
    simp only [Real.inner_apply]
  rw [hKernel] at H
  exact H

end
end TensorPCA.FinitePriorCavityFreeEnergyComparisonProofs
