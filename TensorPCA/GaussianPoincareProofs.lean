-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.KLSProofs.Poincare.Gaussian.Multivariate

/-! Sharp Gaussian Poincaré for the canonical Gaussian law. The selected
KLS proof uses globally smooth L² tests with integrable canonical gradient
energy; no compact support or separate Poincaré hypothesis is supplied. -/
@[expose] public section
namespace TensorPCA.GaussianPoincareProofs
open MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The sharp constant-one inequality on the genuine standard Gaussian,
including zero-dimensional Euclidean spaces. -/
theorem variance_stdGaussian_le_gradient (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hL2 : MemLp f 2 (stdGaussian E))
    (henergy : Integrable (fun x ↦ ‖gradient f x‖^2) (stdGaussian E)) :
    variance f (stdGaussian E) ≤ ∫ x, ‖gradient f x‖^2 ∂stdGaussian E := by
  have H := (KLSProofs.Poincare.SmoothTest.holds_stdGaussian (V := E)).variance_le
    ⟨hf, hL2, henergy⟩
  simpa only [one_mul, KLSProofs.Poincare.SmoothTest.energy] using H

/-- Equivalent operator-norm form, useful for the finite tensor free-energy
Fréchet derivative. The actual Hilbert gradient convention is unchanged. -/
theorem variance_stdGaussian_le_fderiv (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hL2 : MemLp f 2 (stdGaussian E))
    (henergy : Integrable (fun x ↦ ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    variance f (stdGaussian E) ≤ ∫ x, ‖fderiv ℝ f x‖^2 ∂stdGaussian E := by
  have hnorm (x : E) := KLSProofs.Poincare.SmoothTest.norm_fderiv_eq_norm_gradient f x
  have hgrad : Integrable (fun x ↦ ‖gradient f x‖^2) (stdGaussian E) := by
    simpa only [hnorm] using henergy
  have H := variance_stdGaussian_le_gradient f hf hL2 hgrad
  simpa only [hnorm] using H


end
end TensorPCA.GaussianPoincareProofs
