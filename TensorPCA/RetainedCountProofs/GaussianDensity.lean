-- SPDX-License-Identifier: Apache-2.0
module

public import TensorPCA.GaussianDensityProofs

/-! Namespace-compatible reuse of the already checked exact Gaussian-density
port from pmaronow/slowequilibration-palomar at
 a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
SlowEquilibration/GaussianDensity.lean (Apache-2.0).
No density definition or proof body is duplicated. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GaussianDensity

export TensorPCA.GaussianDensityProofs
  (normalizer density densityLaw normalizer_pos density_pos density_continuous
    density_integrable density_integral densityLaw_probability density_complete_square
    densityLaw_laplace densityLaw_exp_integrable densityLaw_exp_integral
    integral_exp_inner_stdGaussian densityLaw_eq_stdGaussian stdGaussian_eq_withDensity)


end TensorPCA.RetainedCountProofs.GaussianDensity
