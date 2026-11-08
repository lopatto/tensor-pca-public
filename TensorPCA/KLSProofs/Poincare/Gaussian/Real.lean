-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Poincare.Gaussian.Hardy
public import TensorPCA.KLSProofs.Poincare.SmoothTest.Linear

/-!
# Sharp one-dimensional Gaussian Poincaré constant

Source: the [Gaussian covariance family in the historical manuscript](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37)
states `C_P(N(0, Σ)) = λ_max(Σ)` for positive-definite covariance. This module proves its
one-dimensional Poincaré component for the repository's existing globally smooth L²
finite-energy `Admissible` domain.

The parameter `v : NNReal` is the variance, not its square root. Arbitrary means and the
zero-variance Dirac law are explicit local extensions. The positive-variance upper bound is
imported from `Gaussian.Hardy`; the identity test supplies sharpness through
`Poincare.SmoothTest.Linear`. The result does not assert a Sobolev-domain or spectral-gap
identification, nor does it formalize the source's Bakry--Émery/LSI proof route.

## Main results

* `holds_gaussianReal`: every `gaussianReal m v`, including `v = 0`, has valid constant `v`.
* `constant_gaussianReal`: its extended optimal constant is exactly `(v : ENNReal)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TensorPCA.KLSProofs.Poincare.SmoothTest

/-- Source: local zero-variance extension beyond the manuscript's positive-definite Gaussian
family. Mathlib's `gaussianReal_zero_var` and `variance_dirac` give the inequality with constant
zero for the Dirac law on ℝ; no density representation or subsingleton-space assumption is used. -/
theorem holds_gaussianReal_zero (m : ℝ) : Holds (gaussianReal m 0) 0 := by
  refine ⟨inferInstance, le_rfl, ?_⟩
  intro f _hf
  rw [zero_mul, gaussianReal_zero_var, variance_dirac]

/-- Source: the one-dimensional Poincaré component of the
[Gaussian covariance family](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37).
The existing smooth L² finite-energy domain, arbitrary mean, and zero-variance branch are
explicit local choices/extensions. Combine the positive-variance anchored estimate with
variance minimization and `holds_gaussianReal_zero`; the constant is the variance `v`. -/
theorem holds_gaussianReal (m : ℝ) (v : NNReal) : Holds (gaussianReal m v) (v : ℝ) := by
  by_cases hv : v = 0
  · simpa [hv] using holds_gaussianReal_zero m
  refine ⟨inferInstance, v.coe_nonneg, ?_⟩
  intro f hf
  calc
    variance f (gaussianReal m v) ≤ ∫ x, (f x - f m) ^ 2 ∂gaussianReal m v :=
      hf.variance_le_integral_sq_sub (f m)
    _ ≤ (v : ℝ) * energy (gaussianReal m v) f := hf.integral_sq_sub_gaussian_le hv

/-- Source: the linear-test lower-bound argument in the
[Gaussian covariance family](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L24-L28).
Use `variance_linear_le` at `1 : ℝ`, Mathlib's `memLp_id_gaussianReal`, and
`variance_id_gaussianReal`. The test is the identity, whose energy is one, including for `v = 0`.
Arbitrary means and zero variance are local extensions; no covariance eigenvalue theorem is needed.
-/
theorem Holds.gaussianReal_variance_le {m : ℝ} {v : NNReal} {C : ℝ}
    (h : Holds (gaussianReal m v) C) : (v : ℝ) ≤ C := by
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal m v) := memLp_id_gaussianReal' 2 (by norm_num)
  have hlin := variance_linear_le h hmem (1 : ℝ)
  have hid : linear (1 : ℝ) = id := by
    funext x
    simp [linear]
  rw [hid] at hlin
  simpa [variance_id_gaussianReal] using hlin

/-- Source: the one-dimensional sharp Poincaré constant in the
[Gaussian covariance family](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37),
with the existing local `Admissible` domain and local `ENNReal` infimum encoding of the constant in
[Definition 2.1](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25).
Combine `holds_gaussianReal`, `Holds.gaussianReal_variance_le`, `constant_le`, and `le_constant`.
All means and nonnegative variances are included; no infimum-attainment witness is assumed. -/
theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (gaussianReal m v) = (v : ENNReal) := by
  refine le_antisymm (constant_le (holds_gaussianReal m v)) (le_constant fun C hC ↦ ?_)
  have hvc : (v : ℝ) ≤ (C : ℝ) := hC.gaussianReal_variance_le
  exact_mod_cast hvc

end TensorPCA.KLSProofs.Poincare.SmoothTest
