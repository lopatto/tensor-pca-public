-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityIdealField
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellLinearPartition
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility
public import TensorPCA.GaussianSpinInterpolationProofs

/-! The ideal-z annulus partition, averaged under the true finite bulk Gibbs law. Both
coefficient fields are fixed here; Gaussian disorder averaging is a separate
obligation. The annulus mass occurs exactly once.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityIdealField FiniteCavityShellLinearPartition FiniteCavityGaussianCompatibility
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def blockField {N M : ℕ} (k : ℕ) (mu beta : ℝ)
    (g : EuclideanSpace ℝ (IdealCoordinate N M k)) (x : Model.Vector N) : Model.Vector M :=
  WithLp.toLp 2 (fun i => ∑I : Fin (k-1)→Fin (N+1),zFeature k mu beta x I*g (i,I))

theorem cavityFeature_score_eq {N M : ℕ} (k : ℕ) (mu beta : ℝ)
    (g : EuclideanSpace ℝ (IdealCoordinate N M k)) (x : Model.Vector N) (eta : Model.Vector M) :
    inner ℝ (cavityFeature k mu beta eta x) g=inner ℝ (blockField k mu beta g x) eta := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,cavityFeature,blockField,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem blockField_norm_le {N M : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (g : EuclideanSpace ℝ (IdealCoordinate N M k))
    {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    ‖blockField k mu beta g x‖≤|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)*‖g‖ := by
  let h := blockField k mu beta g x
  have hnorm : ‖h‖^2≤‖h‖*(|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)*‖g‖) := by
    calc
      _ = inner ℝ h h := (real_inner_self_eq_norm_sq h).symm
      _ = inner ℝ (cavityFeature k mu beta h x) g := (cavityFeature_score_eq k mu beta g x h).symm
      _ ≤ ‖cavityFeature k mu beta h x‖*‖g‖ := (le_abs_self _).trans (abs_real_inner_le_norm _ _)
      _ = _ := by rw [cavityFeature_norm k hmu beta h hx]; ring
  by_cases hh : ‖h‖=0
  · change ‖h‖≤_
    rw [hh]
    positivity
  · have hhpos := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hh)
    change ‖h‖≤_
    nlinarith only [hnorm,hhpos]

def bulkLinear (N M k : ℕ) (mu beta : ℝ) (x : Model.Vector N) : GroundState.Disorder N k→L[ℝ] ℝ :=
  innerSL ℝ (bulkFeature M (fun p : Fin k => p.val+1)
    (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x)

def bulkGibbs (N M k : ℕ) (mu beta : ℝ) (g : GroundState.Disorder N k) : Measure (Model.Vector N) :=
  gibbsMeasure (Model.spherePrior N) (bulkLinear N M k mu beta) g

theorem bulkLinear_continuous (N M k : ℕ) (mu beta : ℝ) : Continuous (bulkLinear N M k mu beta) := by
  unfold bulkLinear bulkFeature
  exact (innerSL ℝ).continuous.comp (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)

theorem bulkGibbs_probability {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) : IsProbabilityMeasure (bulkGibbs N M k mu beta g) := by
  obtain ⟨K,hK⟩ := (Geometry.unitSphere_isCompact N).bddAbove_image
    (bulkLinear_continuous N M k mu beta).norm.continuousOn
  have hb : ∀ᵐ x∂Model.spherePrior N,‖bulkLinear N M k mu beta x‖≤K :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx => hK ⟨x,hx,rfl⟩)
  exact gibbsMeasure_probability _ _ (bulkLinear_continuous N M k mu beta).measurable hb g

theorem bulkGibbs_norm_ae {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) : ∀ᵐ x∂bulkGibbs N M k mu beta g,‖x‖=1 :=
  (gibbsMeasure_absolutelyContinuous (Model.spherePrior N) (bulkLinear N M k mu beta) g).ae_le
    (Geometry.spherePrior_norm_ae hN)

private theorem fixed_joint_integrable {N M : ℕ} (k : ℕ) {mu L : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hL : 0≤L)
    (q : Measure (Model.Vector N)) [IsProbabilityMeasure q] (hq : ∀ᵐ x∂q,‖x‖=1)
    (nu : Measure (Model.Vector M)) [IsFiniteMeasure nu]
    (T : Model.Vector M→Model.Vector M) (hT : Continuous T) (hEta : ∀ᵐ eta∂nu,‖T eta‖^2≤L)
    (g : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    Integrable (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (cavityFeature k mu beta (T p.2) p.1) g))
      (q.prod nu) := by
  have hscore : Continuous (fun p : Model.Vector N×Model.Vector M =>
      inner ℝ (cavityFeature k mu beta (T p.2) p.1) g) :=
    ((cavityFeature_joint_continuous N M k mu beta).comp
      (continuous_fst.prodMk (hT.comp continuous_snd))).inner continuous_const
  have hc := hscore.rexp
  apply Integrable.of_bound hc.aestronglyMeasurable
    (Real.exp (Real.sqrt L*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)*‖g‖))
  apply (Measure.ae_prod_iff_ae_ae (isClosed_le hc.norm continuous_const).measurableSet).2
  filter_upwards [hq] with x hx
  filter_upwards [hEta] with eta heta
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  exact ((le_abs_self _).trans (abs_real_inner_le_norm _ _)).trans
    (mul_le_mul_of_nonneg_right (cavityFeature_norm_le k hmu beta hL (T eta) heta hx) (norm_nonneg g))

theorem fixed_shell_joint_integrable {N M : ℕ} (hN : 0<N) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta delta : ℝ) (hdelta : 0≤delta)
    (gB : GroundState.Disorder N k) (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    Integrable (fun p : Model.Vector N×Model.Vector M =>
      Real.exp (inner ℝ (cavityFeature k mu beta p.2 p.1) gZ))
      ((bulkGibbs N M k mu beta gB).prod ((stdGaussian (Model.Vector M)).restrict (gaussianAnnulus M delta))) := by
  letI := bulkGibbs_probability hN M k mu beta gB
  apply fixed_joint_integrable k hmu beta (by positivity : 0≤(M : ℝ)*(1+delta))
    (bulkGibbs N M k mu beta gB) (bulkGibbs_norm_ae hN M k mu beta gB)
    ((stdGaussian (Model.Vector M)).restrict (gaussianAnnulus M delta)) id continuous_id _ gZ
  exact (ae_restrict_mem (gaussianAnnulus_measurableSet M delta)).mono (fun eta heta => heta.2)

theorem annulus_partition_bulkGibbs_lower {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta delta : ℝ) (hdelta : 0≤delta)
    (gB : GroundState.Disorder N k) (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    (stdGaussian (Model.Vector M)).real (gaussianAnnulus M delta)*
        (∫x,(∫u,Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) gZ)
          ∂Model.spherePrior M)∂bulkGibbs N M k mu beta gB)≤
      ∫eta in gaussianAnnulus M delta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
        ∂bulkGibbs N M k mu beta gB)∂stdGaussian (Model.Vector M) := by
  let q := bulkGibbs N M k mu beta gB
  letI := bulkGibbs_probability hN M k mu beta gB
  have hL : 0≤(M : ℝ)*(1+delta) := by positivity
  have hSphereEta : ∀ᵐ u∂Model.spherePrior M,‖Real.sqrt (M : ℝ) • u‖^2≤(M : ℝ)*(1+delta) := by
    filter_upwards [Geometry.spherePrior_norm_ae hM] with u hu
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one,
      Real.sq_sqrt (Nat.cast_nonneg M)]
    nlinarith only [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ)≤M) hdelta]
  have hSphere := fixed_joint_integrable k hmu beta hL q (bulkGibbs_norm_ae hN M k mu beta gB)
    (Model.spherePrior M) (fun u => Real.sqrt (M : ℝ) • u)
    ((continuous_const : Continuous (fun _ : Model.Vector M => Real.sqrt (M : ℝ))).smul continuous_id) hSphereEta gZ
  have hAnnulus := fixed_shell_joint_integrable hN k hmu beta delta hdelta gB gZ
  have hpoint (x : Model.Vector N) := gaussian_annulus_linear_partition_lower hM delta hdelta (blockField k mu beta gZ x)
  simp_rw [← cavityFeature_score_eq k mu beta gZ] at hpoint
  have H := integral_mono_ae (hSphere.integral_prod_left.const_mul
    ((stdGaussian (Model.Vector M)).real (gaussianAnnulus M delta))) hAnnulus.integral_prod_left
    (.of_forall hpoint)
  rw [integral_const_mul] at H
  exact H.trans_eq (integral_integral_swap
    (f := fun (x : Model.Vector N) (eta : Model.Vector M) =>
      Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)) hAnnulus)


end
end TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition
