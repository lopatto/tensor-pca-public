-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- Uses the checked GaussianSpinComparison trace port of slowequilibration
-- a28aaa336343c4caf43791ababd8ed0ee5c7b58e (Apache-2.0).
module
public import TensorPCA.GaussianSpinComparisonProofs

/-! Absolute Gaussian log-partition comparison with nonconstant diagonals. The prior and
bounded features supply the Gaussian integrability.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GaussianAbsoluteCovarianceComparison
open MeasureTheory ProbabilityTheory Set Filter GaussianSpinInterpolation GaussianSpinComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I V : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace V]

theorem signedTrace_abs_le (nu : Measure V) [IsProbabilityMeasure nu]
    (L : V → EuclideanSpace ℝ I →L[ℝ] ℝ) (hL : Measurable L)
    {K ddiag dpair : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂nu, ‖L v‖≤K) (label : I → Bool)
    (hdiag : ∀ᵐ v ∂nu, |signedKernel L label v v|≤ddiag)
    (hpair : ∀ᵐ p ∂nu.prod nu, |signedKernel L label p.1 p.2|≤dpair)
    (theta : ℝ) (g : EuclideanSpace ℝ I) :
    |∑ i, covarianceSign label i*variance (coordinateObservable L i)
      (gibbsMeasure nu (rotatedLinear L label theta) g)|≤ddiag+dpair := by
  let G := gibbsMeasure nu (rotatedLinear L label theta) g
  letI : IsProbabilityMeasure G := gibbsMeasure_probability nu _
    (rotatedLinear_measurable L hL label theta) (rotatedLinear_bound nu L hK hb label theta) g
  have hac : G≪nu := gibbsMeasure_absolutelyContinuous nu _ g
  have hD : |∫ v, signedKernel L label v v ∂G|≤ddiag := by
    have H := norm_integral_le_of_norm_le_const (μ := G)
      (f := fun v ↦ signedKernel L label v v) (C := ddiag)
      ((hdiag.filter_mono hac.ae_le).mono (fun _ h ↦ by simpa only [Real.norm_eq_abs] using h))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hP : |∫ p : V×V, signedKernel L label p.1 p.2 ∂G.prod G|≤dpair := by
    have H := norm_integral_le_of_norm_le_const (μ := G.prod G)
      (f := fun p : V×V ↦ signedKernel L label p.1 p.2) (C := dpair)
      ((hpair.filter_mono (hac.prod hac).ae_le).mono (fun _ h ↦ by simpa only [Real.norm_eq_abs] using h))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  rw [signedVarianceTrace_eq_kernels nu L hL hK hb label theta g]
  exact (abs_sub _ _).trans (add_le_add hD hP)

theorem averagedRotatedLogPartition_abs_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    (L : V → EuclideanSpace ℝ I →L[ℝ] ℝ) (hL : Measurable L)
    {K ddiag dpair : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂nu, ‖L v‖≤K) (label : I → Bool)
    (hdiag : ∀ᵐ v ∂nu, |signedKernel L label v v|≤ddiag)
    (hpair : ∀ᵐ p ∂nu.prod nu, |signedKernel L label p.1 p.2|≤dpair) :
    |averagedRotatedLogPartition nu L label (Real.pi/2)-averagedRotatedLogPartition nu L label 0|≤
      (ddiag+dpair)/2 := by
  let F := averagedRotatedLogPartition nu L label
  let C := fun theta : ℝ ↦ (ddiag+dpair)/2*(Real.sin theta)^2
  have hF (theta : ℝ) := averagedRotatedLogPartition_hasDerivAt_signedTrace nu L hL hK hb label theta
  have hC (theta : ℝ) : HasDerivAt C ((ddiag+dpair)*Real.sin theta*Real.cos theta) theta := by
    convert ((Real.hasDerivAt_sin theta).pow 2).const_mul ((ddiag+dpair)/2) using 1
    ring
  have hmean (theta : ℝ) :
      |∫ g, (∑ i, covarianceSign label i*variance (coordinateObservable L i)
        (gibbsMeasure nu (rotatedLinear L label theta) g))
        ∂SYK.standardGaussianMeasureOnEuclidean I|≤ddiag+dpair := by
    have H := norm_integral_le_of_norm_le_const
      (μ := SYK.standardGaussianMeasureOnEuclidean I)
      (f := fun g ↦ ∑ i, covarianceSign label i*variance (coordinateObservable L i)
        (gibbsMeasure nu (rotatedLinear L label theta) g)) (C := ddiag+dpair)
      (Eventually.of_forall (fun g : EuclideanSpace ℝ I ↦ by
        have hh := signedTrace_abs_le nu L hL hK hb label hdiag hpair theta g
        simpa only [Real.norm_eq_abs] using hh))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hslope (theta : ℝ) (htheta : theta∈Icc 0 (Real.pi/2)) :
      |deriv F theta|≤(ddiag+dpair)*Real.sin theta*Real.cos theta := by
    have hs : 0≤Real.sin theta := Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 (by linarith [htheta.2,Real.pi_pos])
    have hc : 0≤Real.cos theta := Real.cos_nonneg_of_mem_Icc ⟨by linarith [htheta.1,Real.pi_pos],htheta.2⟩
    rw [(hF theta).deriv,abs_mul,abs_of_nonneg (mul_nonneg hs hc)]
    exact (mul_le_mul_of_nonneg_left (hmean theta) (mul_nonneg hs hc)).trans_eq (by ring)
  have hplus : MonotoneOn (fun theta ↦ C theta+F theta) (Icc 0 (Real.pi/2)) := by
    have hd (theta : ℝ) := (hC theta).add (hF theta)
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun theta ↦ (hd theta).continuousAt)).continuousOn
      (fun theta _ ↦ (hd theta).differentiableAt.differentiableWithinAt)
    intro theta ht
    have hh := (abs_le.mp (hslope theta (interior_subset ht))).1
    rw [(hd theta).deriv,← (hF theta).deriv]
    change 0≤(ddiag+dpair)*Real.sin theta*Real.cos theta+deriv F theta
    linarith
  have hminus : MonotoneOn (fun theta ↦ C theta-F theta) (Icc 0 (Real.pi/2)) := by
    have hd (theta : ℝ) := (hC theta).sub (hF theta)
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun theta ↦ (hd theta).continuousAt)).continuousOn
      (fun theta _ ↦ (hd theta).differentiableAt.differentiableWithinAt)
    intro theta ht
    have hh := (abs_le.mp (hslope theta (interior_subset ht))).2
    rw [(hd theta).deriv,← (hF theta).deriv]
    change 0≤(ddiag+dpair)*Real.sin theta*Real.cos theta-deriv F theta
    linarith
  have h0 : (0 : ℝ)∈Icc 0 (Real.pi/2) := ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have hpi : Real.pi/2∈Icc 0 (Real.pi/2) := ⟨by linarith [Real.pi_pos],le_rfl⟩
  have hp := hplus h0 hpi (by linarith [Real.pi_pos])
  have hm := hminus h0 hpi (by linarith [Real.pi_pos])
  simp only [C,Real.sin_zero,zero_pow (by norm_num : 2≠0),mul_zero,zero_add,zero_sub,
    Real.sin_pi_div_two,one_pow,mul_one] at hp hm
  apply abs_le.mpr
  constructor <;> change _≤_ <;> linarith

end
end TensorPCA.NonRSLowerProofs.GaussianAbsoluteCovarianceComparison
