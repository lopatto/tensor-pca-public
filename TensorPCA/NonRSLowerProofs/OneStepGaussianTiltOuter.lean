-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltEndpoint

/-! Positivity and integrability of the literal spherical one-step endpoint
under an outer Gaussian field. These permit retaining a likely field-norm
box without imposing an unproved integrability or negative-tail premise. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltOuter
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTiltEndpoint
open scoped RealInnerProductSpace Topology
noncomputable section

theorem one_le_sphericalLaplace {N : ℕ} (hN : 0 < N) (w : Model.Vector N) :
    1 ≤ sphericalLaplace N w := by
  let F : Model.Vector N → ℝ := fun u => inner ℝ w (Real.sqrt (N : ℝ) • u)
  have hI := Geometry.spherePrior_continuous_integrable hN F (by fun_prop)
  have hE := Geometry.spherePrior_continuous_integrable hN (fun u => Real.exp (F u))
    (by fun_prop)
  have hsym := Geometry.spherePrior_integral_comp_isometry
    (LinearIsometryEquiv.neg ℝ : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) F (by fun_prop)
  have hz : (∫ u, F u ∂Model.spherePrior N) = 0 := by
    have hn : -(∫ u, F u ∂Model.spherePrior N) = ∫ u, F u ∂Model.spherePrior N := by
      simpa only [F,LinearIsometryEquiv.coe_neg,smul_neg,inner_neg_right,integral_neg]
        using hsym
    linarith
  have H := integral_mono (hI.add (integrable_const (1 : ℝ))) hE
    (fun u => Real.add_one_le_exp (F u))
  change (∫ u, F u+1 ∂Model.spherePrior N) ≤ _ at H
  rw [integral_add hI (integrable_const (1 : ℝ))] at H
  simpa only [hz,zero_add,
    integral_const,probReal_univ,one_smul,F,sphericalLaplace] using H

theorem one_le_fractionalSphereMoment {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : 0 ≤ m)
    (v : ℝ) (y : Model.Vector N) : 1 ≤ fractionalSphereMoment N m v y := by
  have H := integral_mono (integrable_const (1 : ℝ))
    (fractionalSphereMoment_integrable hN hm v y)
    (fun g => Real.one_le_rpow (one_le_sphericalLaplace hN _) hm)
  simpa only [integral_const,probReal_univ,one_smul,fractionalSphereMoment] using H

theorem log_fractionalSphereMoment_nonneg {N : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : 0 ≤ m) (v : ℝ) (y : Model.Vector N) :
    0 ≤ Real.log (fractionalSphereMoment N m v y) :=
  Real.log_nonneg (one_le_fractionalSphereMoment hN hm v y)

theorem fractionalSphereMoment_measurable (N : ℕ) (m v : ℝ) :
    Measurable (fractionalSphereMoment N m v) := by
  have H : Measurable (fun p : Model.Vector N×Model.Vector N =>
      (sphericalLaplace N (p.1+Real.sqrt v • p.2))^m) :=
    ((sphericalLaplace_measurable N).comp (by fun_prop)).pow_const m
  exact H.stronglyMeasurable.integral_prod_right'.measurable

theorem sphericalLaplace_add_le {N : ℕ} (hN : 0 < N) (y w : Model.Vector N) :
    sphericalLaplace N (y+w) ≤
      Real.exp (Real.sqrt (N : ℝ)*‖y‖)*sphericalLaplace N w := by
  have hI := Geometry.spherePrior_continuous_integrable hN
    (fun u => Real.exp (inner ℝ (y+w) (Real.sqrt (N : ℝ) • u))) (by fun_prop)
  have hJ := (Geometry.spherePrior_continuous_integrable hN
    (fun u => Real.exp (inner ℝ w (Real.sqrt (N : ℝ) • u))) (by fun_prop)).const_mul
      (Real.exp (Real.sqrt (N : ℝ)*‖y‖))
  have H := integral_mono_ae hI hJ (by
    filter_upwards [Geometry.spherePrior_norm_ae hN] with u hu
    have hi := (le_abs_self (inner ℝ y (Real.sqrt (N : ℝ) • u))).trans
      (abs_real_inner_le_norm _ _)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one] at hi
    rw [inner_add_left,Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hi))
  simpa only [integral_const_mul,sphericalLaplace] using H

theorem fractionalSphereMoment_shift_le {N : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : 0 ≤ m) (v : ℝ) (y : Model.Vector N) :
    fractionalSphereMoment N m v y ≤
      Real.exp (m*Real.sqrt (N : ℝ)*‖y‖)*fractionalSphereMoment N m v 0 := by
  have hI := fractionalSphereMoment_integrable hN hm v y
  have hJ := (fractionalSphereMoment_integrable hN hm v (0 : Model.Vector N)).const_mul
    (Real.exp (m*Real.sqrt (N : ℝ)*‖y‖))
  have H := integral_mono hI hJ (fun g => by
    have H := Real.rpow_le_rpow (sphericalLaplace_pos hN _).le
      (sphericalLaplace_add_le hN y (Real.sqrt v • g)) hm
    rw [Real.mul_rpow (Real.exp_pos _).le (sphericalLaplace_pos hN _).le,
      ← Real.exp_mul] at H
    simpa only [zero_add,mul_assoc,mul_left_comm,mul_comm] using H)
  simpa only [integral_const_mul,fractionalSphereMoment] using H

theorem log_fractionalSphereMoment_le {N : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : 0 ≤ m) (v : ℝ) (y : Model.Vector N) :
    Real.log (fractionalSphereMoment N m v y) ≤
      m*Real.sqrt (N : ℝ)*‖y‖+Real.log (fractionalSphereMoment N m v 0) := by
  have H := Real.log_le_log (fractionalSphereMoment_pos hN hm v y)
    (fractionalSphereMoment_shift_le hN hm v y)
  rwa [Real.log_mul (Real.exp_pos _).ne' (fractionalSphereMoment_pos hN hm v 0).ne',
    Real.log_exp] at H

theorem outer_log_fractionalSphereMoment_integrable {N : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : 0 ≤ m) (v : ℝ) (u : Model.Vector N) (s : ℝ) :
    Integrable (fun g => Real.log (fractionalSphereMoment N m v (u+s • g)))
      (stdGaussian (Model.Vector N)) := by
  have hI : Integrable (fun g : Model.Vector N => ‖g‖) (stdGaussian (Model.Vector N)) :=
    (IsGaussian.integrable_id (μ := stdGaussian (Model.Vector N))).norm
  have hMaj := (((integrable_const ‖u‖).add (hI.const_mul |s|)).const_mul
    (m*Real.sqrt (N : ℝ))).add
      (integrable_const (Real.log (fractionalSphereMoment N m v 0)))
  have hMeas : Measurable (fun g : Model.Vector N =>
      Real.log (fractionalSphereMoment N m v (u+s • g))) :=
    Real.measurable_log.comp ((fractionalSphereMoment_measurable N m v).comp (by fun_prop))
  apply hMaj.mono' hMeas.aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs,abs_of_nonneg (log_fractionalSphereMoment_nonneg hN hm v _)]
  apply (log_fractionalSphereMoment_le hN hm v _).trans
  change m*Real.sqrt (N : ℝ)*‖u+s • g‖+Real.log (fractionalSphereMoment N m v 0) ≤
    m*Real.sqrt (N : ℝ)*(‖u‖+|s| * ‖g‖)+Real.log (fractionalSphereMoment N m v 0)
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm (Real.sqrt_nonneg _))
  simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le u (s • g)

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltOuter
