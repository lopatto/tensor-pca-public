-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Exact ordinary determinant-mean scaling. The finite determinant identity
is adapted from GOEScaling.lean at immutable pmaronow/slowequilibration-palomar
 a28aaa336343c4caf43791ababd8ed0ee5c7b58e. The existing actual upper-entry GOE
law and genuine all-shift determinant integrability are reused; no spectral
limit or scaling assumption is supplied. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GOEScaling
public import TensorPCA.RetainedCountProofs.GOEPhysicalPotential
public import TensorPCA.RetainedCountProofs.UnrestrictedConditionedDeterminants
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEPhysicalMeanScalingProofs
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalGaussianJet GOEScaling GOERawMoments GOEPhysicalPotential
open UnrestrictedConditionedDeterminants
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine integrability of the actual raw shifted absolute determinant,
including every real shift and all finite Gaussian variance parameters. -/
theorem matrixAbsoluteDet_integrable (n N : ℕ) (b k : ℝ) :
    Integrable (matrixAbsoluteDet n k) (goeLaw (n+1) N b) := by
  apply ((fixed_shifted_determinant_integrable (n+1) N b k).abs).congr
  exact .of_forall fun W ↦ by
    unfold matrixAbsoluteDet
    rw [show k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-W = -(W-k • 1) by abel,
      Matrix.det_neg, abs_mul, abs_pow]
    simp

/-- An exact pointwise finite determinant identity, with positive scaling. -/
theorem matrixAbsoluteDet_scale {n : ℕ} {a : ℝ} (ha : 0 < a) (k : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    matrixAbsoluteDet n k (a • W) = a^(n+1)*matrixAbsoluteDet n (k/a) W := by
  have he : k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-a • W =
      a • ((k/a) • 1-W) := by
    rw [smul_sub,smul_smul,mul_div_cancel₀ k ha.ne']
  unfold matrixAbsoluteDet
  rw [he,Matrix.det_smul,Fintype.card_fin,abs_mul,abs_of_pos (pow_pos ha _)]

/-- The ordinary absolute determinant mean scales under the literal GOE law.
The standard matrix has dimension n+1 and entry variance 1/(n+1); the physical
matrix has off-diagonal variance b/N and diagonal variance 2b/N. -/
theorem physicalMean_scale (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    physicalMean n N b k =
      (scaleFactor n N b)^(n+1)*physicalMean n (n+1) 1 (k/scaleFactor n N b) := by
  have ha := scaleFactor_pos n hN hb
  unfold physicalMean
  rw [← goeLaw_scale n hN hb.le]
  rw [integral_map (show Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ ↦
      scaleFactor n N b • W) by fun_prop).aemeasurable
    (matrixAbsoluteDet_measurable n k).aestronglyMeasurable]
  simp_rw [matrixAbsoluteDet_scale ha]
  exact integral_const_mul _ _

end
end TensorPCA.RetainedCountProofs.GOEPhysicalMeanScalingProofs
