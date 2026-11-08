-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed retained-count port from immutable source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GaussianQuadratic.lean
The exact Gaussian quadratic proofs are already checked in GaussianMomentProofs.
This is a thin export layer preserving all five original APIs, with no copied
definitions or proof bodies.
See the repository LICENSE. -/
module

public import TensorPCA.GaussianMomentProofs

@[expose] public section
namespace TensorPCA.RetainedCountProofs.GaussianQuadratic
export TensorPCA.GaussianMomentProofs
  (integrable_quadratic_lebesgue integral_quadratic_lebesgue weighted_density_eq
    integrable_exp_quadratic integral_exp_quadratic)

end TensorPCA.RetainedCountProofs.GaussianQuadratic
