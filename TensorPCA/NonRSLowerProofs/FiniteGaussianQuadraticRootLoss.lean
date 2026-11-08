-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianShellMoments

/-! The normalized quadratic root has a dimension-uniform second moment, and its loss on
a rare measurable root event is controlled by Cauchy-Schwarz. All constants and
coefficients may be real.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootLoss
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianShellMoments
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalizedRadius_memLp_two (M : ℕ) :
    MemLp (fun g : Model.Vector M ↦ ‖g‖^2/(M : ℝ)) 2 (stdGaussian (Model.Vector M)) := by
  have H : MemLp (fun g : Model.Vector M ↦ ‖g‖^2) 2 (stdGaussian (Model.Vector M)) := by
    simpa only [zero_add,one_smul] using norm_shift_sq_memLp_two (0 : Model.Vector M) 1
  simpa only [div_eq_mul_inv,mul_comm] using H.const_mul (M : ℝ)⁻¹

theorem quadraticRoot_memLp_two (M : ℕ) (c a : ℝ) :
    MemLp (fun g : Model.Vector M ↦ c+a*‖g‖^2/(M : ℝ)) 2 (stdGaussian (Model.Vector M)) := by
  have H := (memLp_const c).add ((normalizedRadius_memLp_two M).const_mul a)
  exact MemLp.ae_eq (.of_forall (fun g ↦ by simp only [Pi.add_apply]; ring)) H

private theorem normalizedRadius_second_moment_le_three {M : ℕ} (hM : 0<M) :
    (∫g : Model.Vector M,(‖g‖^2/(M : ℝ))^2∂stdGaussian (Model.Vector M))≤3 := by
  have hfourth := GaussianMomentProofs.gaussian_radius_even_moment (E := Model.Vector M) 2
  norm_num [GaussianMomentProofs.radialMomentProduct,Model.Vector,Finset.prod_range_succ] at hfourth
  have heq : (∫g : Model.Vector M,(‖g‖^2/(M : ℝ))^2∂stdGaussian (Model.Vector M))=
      ((M : ℝ)*((M : ℝ)+2))/(M : ℝ)^2 := by
    simp_rw [div_pow,← pow_mul]
    rw [integral_div]
    norm_num at hfourth ⊢
    rw [hfourth]
  rw [heq]
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hMone : (1 : ℝ)≤M := by exact_mod_cast hM
  apply (div_le_iff₀ (sq_pos_of_pos hMr)).mpr
  nlinarith

theorem quadraticRoot_second_moment_le {M : ℕ} (hM : 0<M) (c a : ℝ) :
    (∫g : Model.Vector M,(c+a*‖g‖^2/(M : ℝ))^2∂stdGaussian (Model.Vector M))≤2*c^2+6*a^2 := by
  have hU := quadraticRoot_memLp_two M c a
  have hR := normalizedRadius_memLp_two M
  have hMajor : Integrable (fun g : Model.Vector M ↦
      2*c^2+2*a^2*(‖g‖^2/(M : ℝ))^2) (stdGaussian (Model.Vector M)) :=
    (integrable_const _).add (hR.integrable_sq.const_mul _)
  have H := integral_mono hU.integrable_sq hMajor (fun g ↦ by
    have heq : a*‖g‖^2/(M : ℝ)=a*(‖g‖^2/(M : ℝ)) := by ring
    rw [heq]
    nlinarith [sq_nonneg (c-a*(‖g‖^2/(M : ℝ)))])
  rw [integral_add (integrable_const _) (hR.integrable_sq.const_mul _),integral_const,
    probReal_univ,one_smul,integral_const_mul] at H
  have hSecond := mul_le_mul_of_nonneg_left (normalizedRadius_second_moment_le_three hM)
    (show 0≤2*a^2 by positivity)
  linarith

private theorem abs_setIntegral_le_sqrt_second {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {U : Omega→ℝ} (hU : MemLp U 2 mu)
    {bad : Set Omega} (hbad : MeasurableSet bad) :
    |∫g in bad,U g∂mu|≤Real.sqrt (∫g,(U g)^2∂mu)*Real.sqrt (mu.real bad) := by
  let I : Omega→ℝ := bad.indicator (fun _ ↦ 1)
  have hI : MemLp I 2 mu := (memLp_const (1 : ℝ)).indicator hbad.nullMeasurableSet
  have hLeft : (∫g,|U g| * |I g|∂mu)=∫g in bad,|U g|∂mu := by
    rw [← integral_indicator hbad]
    apply integral_congr_ae
    exact .of_forall (fun g ↦ by by_cases hg : g∈bad <;> simp [I,hg])
  have hRight : (∫g,(I g)^2∂mu)=mu.real bad := by
    have heq : (fun g ↦ (I g)^2)=bad.indicator (fun _ ↦ (1 : ℝ)) := by
      funext g
      by_cases hg : g∈bad <;> simp [I,hg]
    rw [heq,integral_indicator_const (1 : ℝ) hbad]
    simp
  have H := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hU) (by simpa using hI)
  simp only [Real.norm_eq_abs,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] at H
  rw [hLeft,hRight] at H
  have hAbs : |∫g in bad,U g∂mu|≤∫g in bad,|U g|∂mu := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := mu.restrict bad) U
  exact hAbs.trans H

theorem quadraticRoot_bad_integral_abs_le {M : ℕ} (hM : 0<M) (c a : ℝ)
    {bad : Set (Model.Vector M)} (hbad : MeasurableSet bad) {eta : ℝ}
    (hmass : (stdGaussian (Model.Vector M)).real bad≤eta) :
    |∫g in bad,c+a*‖g‖^2/(M : ℝ)∂stdGaussian (Model.Vector M)|≤
      Real.sqrt (2*c^2+6*a^2)*Real.sqrt eta := by
  refine (abs_setIntegral_le_sqrt_second (stdGaussian (Model.Vector M))
    (quadraticRoot_memLp_two M c a) hbad).trans ?_
  gcongr
  exact quadraticRoot_second_moment_le hM c a

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootLoss
