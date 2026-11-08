-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite actual-GOE source port from pmaronow/slowequilibration-palomar
   a28aaa336343c4caf43791ababd8ed0ee5c7b58e. Only the literal definitions and
   finite law/mean APIs named below are retained; no spectral/moment asymptotic
   bound is imported or assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GOERawMoments
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEPhysicalPotential
noncomputable section
open MeasureTheory GOERawMoments
/-- Literal ordinary expected absolute determinant under the actual matrix law. -/
def physicalMean (n N : ℕ) (b k : ℝ) : ℝ :=
  ∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) N b

end
end TensorPCA.RetainedCountProofs.GOEPhysicalPotential
