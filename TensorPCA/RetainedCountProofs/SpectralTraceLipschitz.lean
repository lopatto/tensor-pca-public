-- SPDX-License-Identifier: Apache-2.0
/- Attributed exact scalar clipping source proof from
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/SpectralTraceLipschitz.lean. Only the exact clipped-log
   definition and scalar Lipschitz theorem are ported; matrix trace APIs remain
   a separate genuine obligation. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SemicirclePotentialIntegralProofs
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SpectralTraceLipschitz
noncomputable section
open scoped NNReal
open SemicirclePotential.OutsideFormula
def clippedLog (k rho x : ℝ) : ℝ := Real.log (max |k - x| rho)

/-- The exact scalar clipped logarithm used in `prop:kr-determinant`. -/
theorem clippedLog_lipschitz (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith ⟨1 / rho, by positivity⟩ (clippedLog k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |clippedLog k rho x - clippedLog k rho y| ≤ (1 / rho) * |x - y|
  have hmax : |max |k - x| rho - max |k - y| rho| ≤ |x - y| := by
    have hl : LipschitzWith 1 (fun x : ℝ => k - x) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show k - a - (k - b) = -(a - b) by ring, abs_neg]
    have habs : LipschitzWith 1 (fun x : ℝ => |k - x|) := by
      simpa only [Function.comp_def, Real.norm_eq_abs, one_mul] using
        (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hl
    have h := (habs.max_const rho).dist_le_mul x y
    simpa only [Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul] using h
  have hlog := log_difference_le hrho (le_max_right |k - x| rho) (le_max_right |k - y| rho)
  exact hlog.trans (by simpa only [div_eq_mul_inv, mul_comm, one_mul, mul_one] using
    div_le_div_of_nonneg_right hmax hrho.le)

end
end TensorPCA.RetainedCountProofs.SpectralTraceLipschitz
