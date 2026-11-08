-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltOuter
public import TensorPCA.GaussianGibbsChangeOfMeasureProofs

/-! The concrete spherical cavity numerator mark, its positivity and exact Gaussian
second-moment bound. Cavity-sphere Cauchy and the Gaussian MGF supply the dimension-
free constant; no ambient Gaussian norm moment is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
open MeasureTheory ProbabilityTheory Set
open FiniteCavityIdealField FiniteCavityShellGibbsPartition
open OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open GaussianGibbsChangeOfMeasureProofs GaussianDensityProofs
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev CavityDisorder (N M k : ℕ) := EuclideanSpace ℝ (IdealCoordinate N M k)

def numeratorMark {N M : ℕ} (k : ℕ) (mu beta : ℝ) (g : CavityDisorder N M k) (x : Model.Vector N) : ℝ :=
  ∫ u : Model.Vector M,Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g) ∂Model.spherePrior M

theorem numeratorMark_eq_sphericalLaplace {N M : ℕ} (k : ℕ) (mu beta : ℝ)
    (g : CavityDisorder N M k) (x : Model.Vector N) :
    numeratorMark k mu beta g x=sphericalLaplace M (blockField k mu beta g x) := by
  unfold numeratorMark sphericalLaplace
  simp_rw [cavityFeature_score_eq]

theorem numeratorMark_one_le {N M : ℕ} (hM : 0<M) (k : ℕ) (mu beta : ℝ)
    (g : CavityDisorder N M k) (x : Model.Vector N) : 1≤numeratorMark k mu beta g x := by
  rw [numeratorMark_eq_sphericalLaplace]
  exact one_le_sphericalLaplace hM _

theorem numeratorMark_joint_measurable (N M k : ℕ) (mu beta : ℝ) :
    Measurable (fun p : CavityDisorder N M k×Model.Vector N ↦ numeratorMark k mu beta p.1 p.2) := by
  have hInput : Continuous (fun p : (CavityDisorder N M k×Model.Vector N)×Model.Vector M ↦
      (p.1.2,Real.sqrt (M : ℝ) • p.2)) := continuous_fst.snd.prodMk (continuous_snd.const_smul (Real.sqrt (M : ℝ)))
  have hFeature := (cavityFeature_joint_continuous N M k mu beta).comp hInput
  have hScore : Continuous (fun p : (CavityDisorder N M k×Model.Vector N)×Model.Vector M ↦
      inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • p.2) p.1.2) p.1.1) :=
    hFeature.inner continuous_fst.fst
  have hExp := Real.continuous_exp.comp hScore
  have H := hExp.stronglyMeasurable.integral_prod_right' (ν := Model.spherePrior M)
  simpa only [numeratorMark,Function.comp_def] using H.measurable

private theorem scaledScore_joint_continuous {N M : ℕ} (k : ℕ) (mu beta r : ℝ) (x : Model.Vector N) :
    Continuous (fun p : Model.Vector M×CavityDisorder N M k ↦
      Real.exp (r*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • p.1) x) p.2)) := by
  have hInput : Continuous (fun p : Model.Vector M×CavityDisorder N M k ↦
      (x,Real.sqrt (M : ℝ) • p.1)) := continuous_const.prodMk (continuous_fst.const_smul (Real.sqrt (M : ℝ)))
  have hScore : Continuous (fun p : Model.Vector M×CavityDisorder N M k ↦
      inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • p.1) x) p.2) :=
    ((cavityFeature_joint_continuous N M k mu beta).comp hInput).inner continuous_snd
  have H := Real.continuous_exp.comp ((continuous_const : Continuous (fun _ : Model.Vector M×CavityDisorder N M k ↦ r)).mul hScore)
  simpa only [Function.comp_def,Pi.mul_apply] using H

theorem numeratorMark_sq_le_doubled_score {N M : ℕ} (hM : 0<M) (k : ℕ) (mu beta : ℝ)
    (g : CavityDisorder N M k) (x : Model.Vector N) :
    (numeratorMark k mu beta g x)^2≤
      ∫ u : Model.Vector M,Real.exp (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g) ∂Model.spherePrior M := by
  let Y := fun u : Model.Vector M ↦ Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g)
  have hCont : Continuous Y := by
    have H := (scaledScore_joint_continuous (M := M) k mu beta 1 x).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : Model.Vector M ↦ g)))
    simpa only [Function.comp_def,one_mul,id_eq,Y] using H
  have hSqI : Integrable (fun u ↦ Y u^2) (Model.spherePrior M) :=
    Geometry.spherePrior_continuous_integrable hM _ (hCont.pow 2)
  have hLp : MemLp Y 2 (Model.spherePrior M) :=
    (memLp_two_iff_integrable_sq hCont.measurable.aestronglyMeasurable).mpr hSqI
  have H := variance_nonneg Y (Model.spherePrior M)
  rw [variance_eq_sub hLp] at H
  change 0≤(∫ u,Y u^2 ∂Model.spherePrior M)-(numeratorMark k mu beta g x)^2 at H
  have hPow (u : Model.Vector M) : Y u^2=
      Real.exp (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g) := by
    dsimp only [Y]
    rw [two_mul,Real.exp_add,pow_two]
  simp_rw [hPow] at H
  linarith

theorem doubled_score_gaussian_integrable {N M : ℕ} (k : ℕ) (mu beta : ℝ)
    (x : Model.Vector N) (u : Model.Vector M) :
    Integrable (fun g : CavityDisorder N M k ↦ Real.exp
      (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g))
      (stdGaussian (CavityDisorder N M k)) := by
  have H := integrable_exp_inner_add ((2 : ℝ) • cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) 0
  simpa only [real_inner_smul_left,add_zero] using H

theorem doubled_score_gaussian_integral {N M : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {x : Model.Vector N} (hx : x∈Model.unitSphere N)
    {u : Model.Vector M} (hu : u∈Model.unitSphere M) :
    (∫ g : CavityDisorder N M k,Real.exp (2*inner ℝ
      (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g) ∂stdGaussian (CavityDisorder N M k))=
      Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1) := by
  have hNorm := cavityFeature_norm_sq (M := M) k hmu beta (Real.sqrt (M : ℝ) • u) hx
  change ‖u‖=1 at hu
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one,
    Real.sq_sqrt (Nat.cast_nonneg M)] at hNorm
  have H := integral_exp_inner_stdGaussian (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) (2 : ℝ)
  rw [hNorm] at H
  convert H using 1
  congr 1
  ring

theorem doubled_score_joint_integrable {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    Integrable (fun p : Model.Vector M×CavityDisorder N M k ↦
      Real.exp (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • p.1) x) p.2))
      ((Model.spherePrior M).prod (stdGaussian (CavityDisorder N M k))) := by
  have hm := (scaledScore_joint_continuous (M := M) k mu beta 2 x).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (doubled_score_gaussian_integrable k mu beta x),?_⟩
  have hparam : AEStronglyMeasurable (fun u : Model.Vector M ↦
      ∫g : CavityDisorder N M k, ‖Real.exp (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g)‖ ∂stdGaussian (CavityDisorder N M k)) (Model.spherePrior M) :=
    (hm.norm.integral_prod_right' (ν := stdGaussian (CavityDisorder N M k))).aestronglyMeasurable
  apply (integrable_const (Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1))).mono' hparam
  filter_upwards [Geometry.spherePrior_norm_ae hM] with u hu
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using
    (doubled_score_gaussian_integral k hmu beta hx hu).le

theorem numeratorMark_sq_integrable {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    Integrable (fun g : CavityDisorder N M k ↦ (numeratorMark k mu beta g x)^2)
      (stdGaussian (CavityDisorder N M k)) := by
  have hDom := (doubled_score_joint_integrable hM k hmu beta hx).integral_prod_right
  have hm : Measurable (fun g : CavityDisorder N M k ↦ (numeratorMark k mu beta g x)^2) :=
    ((numeratorMark_joint_measurable N M k mu beta).comp (measurable_id.prodMk (measurable_const (a := x)))).pow_const 2
  apply hDom.mono' hm.aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact numeratorMark_sq_le_doubled_score hM k mu beta g x

theorem numeratorMark_gaussian_second_moment {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    (∫ g : CavityDisorder N M k,(numeratorMark k mu beta g x)^2 ∂stdGaussian (CavityDisorder N M k))≤
      Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1) := by
  have hi := doubled_score_joint_integrable hM k hmu beta hx
  have H := integral_mono (numeratorMark_sq_integrable hM k hmu beta hx) hi.integral_prod_right
    (fun g ↦ numeratorMark_sq_le_doubled_score hM k mu beta g x)
  have hMGF : (∫ g : CavityDisorder N M k,∫ u : Model.Vector M,Real.exp
      (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g)
      ∂Model.spherePrior M ∂stdGaussian (CavityDisorder N M k))=
      Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1) := by
    calc
      _=(∫ u : Model.Vector M,∫ g : CavityDisorder N M k,Real.exp
        (2*inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g)
        ∂stdGaussian (CavityDisorder N M k) ∂Model.spherePrior M) :=
          (integral_prod_symm _ hi).symm.trans (integral_prod _ hi)
      _=∫ _u : Model.Vector M,Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1) ∂Model.spherePrior M :=
        integral_congr_ae ((Geometry.spherePrior_norm_ae hM).mono (fun u hu ↦ doubled_score_gaussian_integral k hmu beta hx hu))
      _=_ := by rw [integral_const,probReal_univ,one_smul]
  exact H.trans_eq hMGF

end
end TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
