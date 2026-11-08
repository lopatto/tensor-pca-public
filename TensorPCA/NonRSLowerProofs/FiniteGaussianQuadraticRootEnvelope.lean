-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalStages
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootLoss

/-! The normalized quadratic root, its mean and its loss on a rare root event. These
identities specialize the L2 estimate to the spine definitions.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootEnvelope
open MeasureTheory ProbabilityTheory
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticStep FiniteGaussianQuadraticLogSteps
open FiniteGaussianQuadraticRootLoss OneStepGaussianShellMoments
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem profileConstant_dimension_scale {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) (B : ℝ) (i : ℕ) :
    profileConstant M x Delta B i=(M : ℝ)*profileConstant 1 x Delta B i := by
  unfold profileConstant tail
  rw [mul_add,Finset.mul_sum]
  congr 1
  · norm_num
    ring
  · apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> norm_num <;> ring

theorem normalized_root_eq {d M : ℕ} (hM : 0< M) (x Delta : Fin d→ℝ) (B : ℝ)
    {y0 : ℝ} (hy : 0≤ y0) (K : ℝ) (g : Model.Vector M) :
    envelope M x Delta B 0 (Real.sqrt y0 •g)/(M : ℝ)+K=
      (profileConstant 1 x Delta B 0+K)+
        (y0/(2*precision x Delta B 0))*‖g‖^2/(M : ℝ) := by
  rw [envelope,quadratic,profileConstant_dimension_scale,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    Real.sq_sqrt hy]
  have hMr : (M : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hM
  field_simp
  <;> ring

theorem normalized_root_memLp_two {d M : ℕ} (hM : 0< M) (x Delta : Fin d→ℝ) (B : ℝ)
    {y0 : ℝ} (hy : 0≤ y0) (K : ℝ) :
    MemLp (fun g : Model.Vector M => envelope M x Delta B 0 (Real.sqrt y0 •g)/(M : ℝ)+K)
      2 (stdGaussian (Model.Vector M)) := by
  simpa only [normalized_root_eq hM x Delta B hy K] using
    quadraticRoot_memLp_two M (profileConstant 1 x Delta B 0+K) (y0/(2*precision x Delta B 0))

theorem normalized_root_integral {d M : ℕ} (hM : 0< M) (x Delta : Fin d→ℝ) (B : ℝ)
    {y0 : ℝ} (hy : 0≤ y0) (K : ℝ) :
    (∫g : Model.Vector M,envelope M x Delta B 0 (Real.sqrt y0 •g)/(M : ℝ)+K
      ∂stdGaussian (Model.Vector M))=
      profileConstant 1 x Delta B 0+y0/(2*precision x Delta B 0)+K := by
  simp_rw [normalized_root_eq hM x Delta B hy K]
  have hi : Integrable (fun g : Model.Vector M => ‖g‖^2) (stdGaussian (Model.Vector M)) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  have hNorm : (∫g : Model.Vector M,‖g‖^2∂stdGaussian (Model.Vector M))=(M : ℝ) := by
    simpa [GaussianMomentProofs.radialMomentProduct,Model.Vector] using
      GaussianMomentProofs.gaussian_radius_even_moment (E := Model.Vector M) 1
  rw [integral_add (integrable_const _) ((hi.const_mul _).div_const _),integral_const,
    probReal_univ,one_smul,integral_div,integral_const_mul,hNorm]
  have hMr : (M : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hM
  field_simp
  <;> ring

theorem normalized_root_second_moment_le {d M : ℕ} (hM : 0< M) (x Delta : Fin d→ℝ) (B : ℝ)
    {y0 : ℝ} (hy : 0≤ y0) (K : ℝ) :
    (∫g : Model.Vector M,(envelope M x Delta B 0 (Real.sqrt y0 •g)/(M : ℝ)+K)^2
      ∂stdGaussian (Model.Vector M))≤
      2*(profileConstant 1 x Delta B 0+K)^2+6*(y0/(2*precision x Delta B 0))^2 := by
  simpa only [normalized_root_eq hM x Delta B hy K] using
    quadraticRoot_second_moment_le hM (profileConstant 1 x Delta B 0+K) (y0/(2*precision x Delta B 0))

theorem normalized_root_bad_integral_abs_le {d M : ℕ} (hM : 0< M)
    (x Delta : Fin d→ℝ) (B : ℝ) {y0 : ℝ} (hy : 0≤ y0) (K : ℝ)
    {bad : Set (Model.Vector M)} (hbad : MeasurableSet bad) {eta : ℝ}
    (hmass : (stdGaussian (Model.Vector M)).real bad≤eta) :
    |∫g in bad,envelope M x Delta B 0 (Real.sqrt y0 •g)/(M : ℝ)+K
      ∂stdGaussian (Model.Vector M)|≤
      Real.sqrt (2*(profileConstant 1 x Delta B 0+K)^2+6*(y0/(2*precision x Delta B 0))^2)*Real.sqrt eta := by
  simpa only [normalized_root_eq hM x Delta B hy K] using
    quadraticRoot_bad_integral_abs_le hM (profileConstant 1 x Delta B 0+K)
      (y0/(2*precision x Delta B 0)) hbad hmass

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootEnvelope
