-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltOuter
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingMeasure

/-! Second moment and clipping tail of the spherical Laplace numerator under a Gaussian
field with total coordinate variance v. The moment is exp(2*M*v), independent of
hierarchy depth or masses.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorMoments
open MeasureTheory ProbabilityTheory Filter
open OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open FiniteCavityCompensatorGaussianMoments NumeratorMarkClippingMeasure
open scoped RealInnerProductSpace
noncomputable section
variable {M : ℕ}

theorem spherical_gaussian_second_moment (hM : 0<M) {v : ℝ} (hv : 0≤v) :
    Integrable (fun g : Model.Vector M => (sphericalLaplace M (Real.sqrt v •g))^2) (stdGaussian (Model.Vector M)) ∧
      (∫g : Model.Vector M,(sphericalLaplace M (Real.sqrt v •g))^2 ∂stdGaussian (Model.Vector M))≤Real.exp (2*(M : ℝ)*v) := by
  let F : Model.Vector M→Model.Vector M := fun u => Real.sqrt v •(Real.sqrt (M : ℝ) •u)
  let D := Real.sqrt v*Real.sqrt (M : ℝ)
  have hF : Measurable F := by fun_prop
  have hD : 0≤D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hFD : ∀ᵐu∂Model.spherePrior M,‖F u‖≤D := by
    filter_upwards [Geometry.spherePrior_norm_ae hM] with u hu
    simp only [F,D,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one,le_refl]
  have hPop (g : Model.Vector M) : sphericalLaplace M (Real.sqrt v •g)=
      ∫u,Real.exp (inner ℝ (F u) g) ∂Model.spherePrior M := by
    unfold sphericalLaplace
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by
      congr 1
      simp only [F,real_inner_smul_left,real_inner_smul_right]
      rw [real_inner_comm g u]
      ring)
  have hSq (g : Model.Vector M) : (sphericalLaplace M (Real.sqrt v •g))^2≤
      ∫u,(Real.exp (inner ℝ (F u) g))^2 ∂Model.spherePrior M := by
    have hLp := expMark_memLp (Model.spherePrior M) hF hFD g
    have H := variance_eq_sub hLp
    have HN := variance_nonneg (fun u => Real.exp (inner ℝ (F u) g)) (Model.spherePrior M)
    simp only [Pi.pow_apply] at H
    rw [H] at HN
    rw [hPop]
    exact sub_nonneg.mp HN
  have hJoint := expMark_joint_sq_integrable (Model.spherePrior M) hF hD hFD
  have hI := hJoint.integral_prod_left
  have hm : Measurable (fun g : Model.Vector M => (sphericalLaplace M (Real.sqrt v •g))^2) :=
    ((sphericalLaplace_measurable M).comp (continuous_const_smul (Real.sqrt v)).measurable).pow_const 2
  have hi : Integrable (fun g : Model.Vector M => (sphericalLaplace M (Real.sqrt v •g))^2) (stdGaussian (Model.Vector M)) := by
    apply hI.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun g => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hSq g)
  have H := integral_mono hi hI hSq
  rw [← integral_prod _ hJoint] at H
  have HD : D^2=(M : ℝ)*v := by
    dsimp [D]
    rw [mul_pow,Real.sq_sqrt hv,Real.sq_sqrt (Nat.cast_nonneg M)]
    ring
  have HB := expMark_joint_sq_integral_le (Model.spherePrior M) hF hD hFD
  rw [HD] at HB
  refine ⟨hi,H.trans ?_⟩
  convert HB using 1
  ring

theorem spherical_gaussian_clipping_tail (hM : 0<M) {v L : ℝ} (hv : 0≤v) (hL : 1≤L) :
    Integrable (fun g : Model.Vector M => sphericalLaplace M (Real.sqrt v •g)-min (sphericalLaplace M (Real.sqrt v •g)) L)
      (stdGaussian (Model.Vector M)) ∧
    0≤(∫g : Model.Vector M,sphericalLaplace M (Real.sqrt v •g)-min (sphericalLaplace M (Real.sqrt v •g)) L ∂stdGaussian (Model.Vector M)) ∧
      (∫g : Model.Vector M,sphericalLaplace M (Real.sqrt v •g)-min (sphericalLaplace M (Real.sqrt v •g)) L ∂stdGaussian (Model.Vector M))≤Real.exp (2*(M : ℝ)*v)/L := by
  have HI := spherical_gaussian_second_moment hM hv
  have hm : Measurable (fun g : Model.Vector M => sphericalLaplace M (Real.sqrt v •g)) :=
    (sphericalLaplace_measurable M).comp (continuous_const_smul (Real.sqrt v)).measurable
  have H := clip_tail_integrable_and_bound (stdGaussian (Model.Vector M)) hm
    (ae_of_all _ (fun g => one_le_sphericalLaplace hM _)) HI.1 hL
  exact ⟨H.1,H.2.1,H.2.2.trans (div_le_div_of_nonneg_right HI.2 (zero_lt_one.trans_le hL).le)⟩

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorMoments
