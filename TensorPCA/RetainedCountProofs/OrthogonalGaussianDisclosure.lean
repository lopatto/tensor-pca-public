-- SPDX-License-Identifier: MIT
/-
MIT License

Copyright (c) 2026 P. M. Aronow and Patrick Lopatto

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Immutable original: pmaronow/aging-temp e28568e30a6ea1e20fce2b8e0a3a72da15759209,
formalization/SphericalAging/OrthogonalGaussianDisclosure.lean. Byte-identical selected source is
retained in pmaronow/slowequilibration-palomar at
a28aaa336343c4caf43791ababd8ed0ee5c7b58e, vendor/all-lean/SphericalAging/OrthogonalGaussianDisclosure.lean.
The local port changes only the namespace prefix and dependency import paths.
Only ordered_tensor_hasLaw is retained; the unused conditional-expectation
and projection tail is omitted, along with its unused canonical import.
Retained definitions and proof bodies are unchanged; local porting changes are Apache-2.0.
-/
module

public import TensorPCA.RetainedCountProofs.AdaptiveGradientDisclosure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

public section

/-! Standard Gaussian disorder splits into independent Gaussian
projections on any fixed tensor subspace and its orthogonal complement.
This is the fixed-subspace Gaussian regeneration used at the start of
source 10.6. Adaptive random-subspace conditioning remains separate. -/
noncomputable section
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
namespace TensorPCA.RetainedCountProofs.OrthogonalGaussianDisclosure
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open scoped InnerProductSpace BigOperators Topology

 theorem ordered_tensor_hasLaw (N p : ℕ) :
    HasLaw (WithLp.toLp 2 : Disorder N p→TensorSpace N p)
      (stdGaussian (TensorSpace N p)) (disorderLaw N p) := by
  refine ⟨(PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.aemeasurable,?_⟩
  exact map_pi_eq_stdGaussian


end TensorPCA.RetainedCountProofs.OrthogonalGaussianDisclosure

