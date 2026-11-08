-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorIntegrability
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedMass

/-! The normalized Gaussian-annulus lower for any unit-spin probability, including the
perturbed bulk Gibbs law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityUnitPriorShellLower
open MeasureTheory ProbabilityTheory Set
open FiniteCavityNumeratorMoments FiniteCavityIdealField FiniteCavityShellGibbsPartition
open FiniteCavityShellLinearPartition FiniteCavityRetainedMass
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem unit_prior_cavity_joint_integrable {N M : ℕ} (k : ℕ) {mu L : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hL : 0≤L)
    (q : Measure (Model.Vector N)) [IsProbabilityMeasure q] (hq : ∀ᵐ x∂q,‖x‖=1)
    (zeta : Measure (Model.Vector M)) [IsFiniteMeasure zeta] (hEta : ∀ᵐ eta∂zeta,‖eta‖^2≤L)
    (g : CavityDisorder N M k) :
    Integrable (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (cavityFeature k mu beta p.2 p.1) g))
      (q.prod zeta) := by
  have hs : Continuous (fun p : Model.Vector N×Model.Vector M => inner ℝ (cavityFeature k mu beta p.2 p.1) g) :=
    ((cavityFeature_joint_continuous N M k mu beta).comp (continuous_fst.prodMk continuous_snd)).inner continuous_const
  apply Integrable.of_bound hs.rexp.aestronglyMeasurable
    (Real.exp (Real.sqrt L*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)*‖g‖))
  apply (Measure.ae_prod_iff_ae_ae (isClosed_le hs.rexp.norm continuous_const).measurableSet).2
  filter_upwards [hq] with x hx
  filter_upwards [hEta] with eta heta
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact ((le_abs_self _).trans (abs_real_inner_le_norm _ _)).trans
    (mul_le_mul_of_nonneg_right (cavityFeature_norm_le k hmu beta hL eta heta hx) (norm_nonneg g))

private theorem annulus_integral_eq_mass_mul_cond {M : ℕ} (hM : 0<M) {delta : ℝ}
    (hdelta : 0<delta) (f : Model.Vector M→ℝ) :
    (∫eta in gaussianAnnulus M delta,f eta∂stdGaussian (Model.Vector M))=
      annulusMass M delta*(∫eta,f eta∂ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)) := by
  have hp := annulusMass_pos hM hdelta
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _=annulusMass M delta*((annulusMass M delta)⁻¹*_)
  rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul]

theorem conditional_annulus_partition_lower {N M : ℕ} (hM : 0<M) (k : ℕ) {mu delta : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hdelta : 0<delta)
    (q : Measure (Model.Vector N)) [IsProbabilityMeasure q] (hq : ∀ᵐ x∂q,‖x‖=1)
    (g : CavityDisorder N M k) :
    (∫x,numeratorMark k mu beta g x∂q)≤
      ∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) g)∂q)
        ∂ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta) := by
  have hMark := (numeratorMark_memLp_spin hM k hmu beta q hq g).integrable (by norm_num : (1 : ENNReal)≤2)
  have hEta : ∀ᵐ eta∂(stdGaussian (Model.Vector M)).restrict (gaussianAnnulus M delta),
      ‖eta‖^2≤(M : ℝ)*(1+delta) :=
    (ae_restrict_mem (gaussianAnnulus_measurableSet M delta)).mono (fun eta heta => heta.2)
  have hAnn := unit_prior_cavity_joint_integrable k hmu beta (by positivity : 0≤(M : ℝ)*(1+delta)) q hq
    ((stdGaussian (Model.Vector M)).restrict (gaussianAnnulus M delta)) hEta g
  have hpoint (x : Model.Vector N) := gaussian_annulus_linear_partition_lower hM delta hdelta.le (blockField k mu beta g x)
  simp_rw [← cavityFeature_score_eq k mu beta g] at hpoint
  have H := integral_mono_ae (hMark.const_mul (annulusMass M delta)) hAnn.integral_prod_left
    (.of_forall hpoint)
  rw [integral_const_mul] at H
  have hSwap := integral_integral_swap (f := fun x eta => Real.exp (inner ℝ (cavityFeature k mu beta eta x) g)) hAnn
  rw [hSwap] at H
  rw [annulus_integral_eq_mass_mul_cond hM hdelta] at H
  have hp := annulusMass_pos hM hdelta
  nlinarith only [H,hp]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityUnitPriorShellLower
