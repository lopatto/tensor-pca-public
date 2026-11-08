-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite actual-GOE source port from pmaronow/slowequilibration-palomar
   a28aaa336343c4caf43791ababd8ed0ee5c7b58e. Only the literal definitions and
   finite law/mean APIs named below are retained; no spectral/moment asymptotic
   bound is imported or assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SphericalGaussianJet
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOERawMoments
noncomputable section
open MeasureTheory
def matrixAbsoluteDet (n : ℕ) (k : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  |(k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W).det|

lemma matrixAbsoluteDet_measurable (n : ℕ) (k : ℝ) : Measurable (matrixAbsoluteDet n k) := by
  unfold matrixAbsoluteDet
  fun_prop

end
end TensorPCA.RetainedCountProofs.GOERawMoments
