/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TensorPCA.GaussianConcentration
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Canonical Gaussian concentration

The finite product Gaussian of the concentration port equals Mathlib's
`stdGaussian`. This identity transports its concentration inequality.
The imported port retains its original MIT copyright and license notice.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace TensorPCA.GaussianConcentrationBridge

/-- The reused product-Gaussian model is exactly the canonical Euclidean Gaussian. -/
theorem standardGaussianMeasure_bridge (ι : Type*) [Fintype ι] :
    SYK.standardGaussianMeasureOnEuclidean ι = stdGaussian (EuclideanSpace ℝ ι) := by
  exact map_pi_eq_stdGaussian

/-- Concentration for the canonical finite-dimensional standard Gaussian. -/
theorem stdGaussian_lipschitz_tail {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t) (hLip : LipschitzWith L.toNNReal F) :
    stdGaussian (EuclideanSpace ℝ ι)
        {x | |F x - ∫ y, F y ∂stdGaussian (EuclideanSpace ℝ ι)| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  simpa only [standardGaussianMeasure_bridge] using
    SYK.euclidean_lipschitz_gaussian_concentration F L t hL ht hLip


end TensorPCA.GaussianConcentrationBridge
