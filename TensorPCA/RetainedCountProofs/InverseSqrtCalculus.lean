-- SPDX-License-Identifier: Apache-2.0
module

public import TensorPCA.JTAnalyticProofs

/-! Reuse the already checked exact inverse-square-root calculus port.
Its immutable original is pmaronow/slowequilibration-palomar at
 a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
SlowEquilibration/InverseSqrtCalculus.lean (Apache-2.0).
The aliases preserve the source namespace expected by the retained-count
foundation, with no second copy of the definitions or proof bodies. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.InverseSqrtCalculus

export TensorPCA.JTAnalyticProofs
  (inverseSqrt hasDerivAt_inverseSqrt deriv_inverseSqrt deriv2_inverseSqrt
    deriv2_inverseSqrt_pos strictConvexOn_inverseSqrt)


end TensorPCA.RetainedCountProofs.InverseSqrtCalculus
