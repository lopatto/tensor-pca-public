-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianAngularTraceProofs
public import TensorPCA.CoupledKernelExpectationProofs

/-! Integration of the finite angular covariance comparison. -/
@[expose] public section
namespace TensorPCA.GaussianAngularComparisonProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianSpinComparison
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs GaussianNestedSwapProofs
open GaussianNestedQuadraticProofs GaussianAngularPressureProofs GaussianAngularExpectationProofs GaussianAngularOuterProofs
open GaussianCoordinateResponseProofs GaussianAngularTraceProofs
open CoupledGaussianKernelProofs CoupledKernelExpectationProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem coordinate_trace_lower [DecidableEq ι] [DecidableEq κ]
    (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ≤ 1) (B C : ℝ)
    (hDiag : ∀ᵐ v ∂μ, B ≤ coordinateCovariance (L v) (L v)-coordinateCovariance (A v) (A v))
    (hCross : ∀ v u, coordinateCovariance (L v) (L u)-coordinateCovariance (A v) (A u) ≤ C) :
    B+(p-1)*C ≤
      ((∑ i, ∫ v, (coordinateObservable L i v)^2 ∂μ)-(∑ j, ∫ v, (coordinateObservable A j v)^2 ∂μ))+
      (p-1)*((∑ i, (∫ v, coordinateObservable L i v ∂μ)^2)-(∑ j, (∫ v, coordinateObservable A j v ∂μ)^2)) := by
  have hbA := hb.mono (fun _ hv ↦ hv.1)
  have hbL := hb.mono (fun _ hv ↦ hv.2)
  have hd := integral_mono_ae (integrable_const B)
    (covariance_difference_diagonal_integrable μ L A hL hA hKL hKA hbL hbA) hDiag
  have hc := integral_mono_ae (covariance_difference_product_integrable μ L A hL hA hbL hbA)
    (integrable_const C) (Filter.Eventually.of_forall (fun vu : V × V ↦ hCross vu.1 vu.2))
  simp only [integral_const,probReal_univ,one_smul] at hd hc
  have hc' := mul_le_mul_of_nonpos_left hc (sub_nonpos.mpr hp)
  change B+(p-1)*C ≤
    ((∑ i, ∫ v, (L v (EuclideanSpace.single i 1))^2 ∂μ)-(∑ j, ∫ v, (A v (EuclideanSpace.single j 1))^2 ∂μ))+
      (p-1)*((∑ i, (∫ v, L v (EuclideanSpace.single i 1) ∂μ)^2)-
        (∑ j, (∫ v, A v (EuclideanSpace.single j 1) ∂μ)^2))
  rw [sum_integral_coordinate_square_difference μ L A hL hA hKL hKA hbL hbA,
    sum_square_integral_coordinate_difference μ L A hL hA hbL hbA]
  exact add_le_add hd hc'

theorem angular_trace_lower [DecidableEq ι] [DecidableEq κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (B C : ℝ)
    (hDiag : ∀ᵐ v ∂ν, B ≤ coordinateCovariance (L v) (L v)-coordinateCovariance (A v) (A v))
    (hCross : ∀ v u, coordinateCovariance (L v) (L u)-coordinateCovariance (A v) (A u) ≤ C)
    (theta : ℝ) (w : EuclideanSpace ℝ κ) :
    B+(p-1)*C ≤ commonTrace ν A L p theta w-physicalTrace ν A L p theta w := by
  let μ := gibbsMeasure ν A (Real.cos theta • w)
  let τ := angularTilt ν A L p theta w
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  letI := angularTilt_probability ν A L hA hL hKL hb p theta w
  let DL : EuclideanSpace ℝ ι → ℝ := fun g ↦ ∑ i,
    expectation μ (fun v ↦ (coordinateObservable L i v)^2) L (Real.sin theta • g)
  let DA : EuclideanSpace ℝ ι → ℝ := fun g ↦ ∑ i,
    expectation μ (fun v ↦ (coordinateObservable A i v)^2) L (Real.sin theta • g)
  let SL : EuclideanSpace ℝ ι → ℝ := fun g ↦ ∑ i,
    (expectation μ (coordinateObservable L i) L (Real.sin theta • g))^2
  let SA : EuclideanSpace ℝ ι → ℝ := fun g ↦ ∑ i,
    (expectation μ (coordinateObservable A i) L (Real.sin theta • g))^2
  have hDLi (i : ι) : Integrable (fun g ↦ expectation μ (fun v ↦ (coordinateObservable L i v)^2)
      L (Real.sin theta • g)) τ := by
    have hb2 : ∀ᵐ v ∂ν, |(coordinateObservable L i v)^2| ≤ KL^2 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
      filter_upwards [(coordinateObservable_bound ν L (hb.mono (fun _ hv ↦ hv.2)) i).and hb] with v hv
      exact ⟨by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv.1 2,hv.2⟩
    exact angular_inner_integrable ν _ A L ((coordinateObservable_measurable L hL i).pow_const 2)
      hA hL (sq_nonneg KL) hKA hKL hb2 p theta w
  have hDAi (i : κ) : Integrable (fun g ↦ expectation μ (fun v ↦ (coordinateObservable A i v)^2)
      L (Real.sin theta • g)) τ := by
    have hb2 : ∀ᵐ v ∂ν, |(coordinateObservable A i v)^2| ≤ KA^2 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
      filter_upwards [(coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i).and hb] with v hv
      exact ⟨by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv.1 2,hv.2⟩
    exact angular_inner_integrable ν _ A L ((coordinateObservable_measurable A hA i).pow_const 2)
      hA hL (sq_nonneg KA) hKA hKL hb2 p theta w
  have hSLi (i : ι) : Integrable (fun g ↦ (expectation μ (coordinateObservable L i) L (Real.sin theta • g))^2) τ :=
    angular_inner_square_integrable ν _ A L (coordinateObservable_measurable L hL i) hA hL hKL hKA hKL
      ((coordinateObservable_bound ν L (hb.mono (fun _ hv ↦ hv.2)) i).and hb) p theta w
  have hSAi (i : κ) : Integrable (fun g ↦ (expectation μ (coordinateObservable A i) L (Real.sin theta • g))^2) τ :=
    angular_inner_square_integrable ν _ A L (coordinateObservable_measurable A hA i) hA hL hKA hKA hKL
      ((coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i).and hb) p theta w
  have hDL : Integrable DL τ := integrable_finsetSum _ (fun i _ ↦ hDLi i)
  have hDA : Integrable DA τ := integrable_finsetSum _ (fun i _ ↦ hDAi i)
  have hSL : Integrable SL τ := integrable_finsetSum _ (fun i _ ↦ hSLi i)
  have hSA : Integrable SA τ := integrable_finsetSum _ (fun i _ ↦ hSAi i)
  have hpoint (g : EuclideanSpace ℝ ι) : B+(p-1)*C ≤ DL g-DA g+(p-1)*(SL g-SA g) := by
    have hμν := gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)
    have hμb : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := hμν.ae_le hb
    have hμL := hμb.mono (fun _ hv ↦ hv.2)
    let ρ := gibbsMeasure μ L (Real.sin theta • g)
    letI := gibbsMeasure_probability μ L hL hμL (Real.sin theta • g)
    have hρν := (gibbsMeasure_absolutelyContinuous μ L (Real.sin theta • g)).trans hμν
    have H := coordinate_trace_lower ρ A L hA hL hKA hKL (hρν.ae_le hb) p hp.2 B C (hρν.ae_le hDiag) hCross
    simpa only [ρ,DL,DA,SL,SA,μ,
      integral_gibbsMeasure (gibbsMeasure ν A (Real.cos theta • w)) L hL hμL (Real.sin theta • g)] using H
  have hLower := integral_mono_ae (integrable_const (B+(p-1)*C))
    ((hDL.sub hDA).add ((hSL.sub hSA).const_mul (p-1))) (Filter.Eventually.of_forall hpoint)
  simp only [integral_const,probReal_univ,one_smul] at hLower
  have hID : (∫ g, DL g ∂τ) = ∑ i, angularMean ν (fun v ↦ (coordinateObservable L i v)^2) A L p theta w := by
    rw [show DL = fun g ↦ ∑ i, expectation μ (fun v ↦ (coordinateObservable L i v)^2) L (Real.sin theta • g) from rfl,
      integral_finsetSum _ (fun i _ ↦ hDLi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (angularMean_eq_physical_integral ν _ A L hA hL hKA hKL hb p theta w).symm
  have hIA : (∫ g, DA g ∂τ) = ∑ i, angularMean ν (fun v ↦ (coordinateObservable A i v)^2) A L p theta w := by
    rw [show DA = fun g ↦ ∑ i, expectation μ (fun v ↦ (coordinateObservable A i v)^2) L (Real.sin theta • g) from rfl,
      integral_finsetSum _ (fun i _ ↦ hDAi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (angularMean_eq_physical_integral ν _ A L hA hL hKA hKL hb p theta w).symm
  have hISL : (∫ g, SL g ∂τ) = ∑ i, angularSquareMean ν (coordinateObservable L i) A L p theta w := by
    rw [show SL = fun g ↦ ∑ i, (expectation μ (coordinateObservable L i) L (Real.sin theta • g))^2 from rfl,
      integral_finsetSum _ (fun i _ ↦ hSLi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (angularSquareMean_eq_physical_integral ν _ A L hA hL hKA hKL hb p theta w).symm
  have hISA : (∫ g, SA g ∂τ) = ∑ i, angularSquareMean ν (coordinateObservable A i) A L p theta w := by
    rw [show SA = fun g ↦ ∑ i, (expectation μ (coordinateObservable A i) L (Real.sin theta • g))^2 from rfl,
      integral_finsetSum _ (fun i _ ↦ hSAi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (angularSquareMean_eq_physical_integral ν _ A L hA hL hKA hKL hb p theta w).symm
  have hRel : commonTrace ν A L p theta w-physicalTrace ν A L p theta w =
      (∫ g, DL g-DA g+(p-1)*(SL g-SA g) ∂τ)+
      p*(∑ i, (angularMean ν (coordinateObservable A i) A L p theta w)^2) := by
    change commonTrace ν A L p theta w-physicalTrace ν A L p theta w =
      (∫ g, (DL-DA) g+(p-1)*(SL-SA) g ∂τ)+
      p*(∑ i, (angularMean ν (coordinateObservable A i) A L p theta w)^2)
    rw [integral_add (hDL.sub hDA) ((hSL.sub hSA).const_mul (p-1))]
    simp only [Pi.sub_apply]
    rw [integral_sub hDL hDA,integral_const_mul,integral_sub hSL hSA,hID,hIA,hISL,hISA]
    simp only [commonTrace,physicalTrace,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  rw [hRel]
  exact hLower.trans (le_add_of_nonneg_right (mul_nonneg hp.1 (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))))

theorem angular_pressure_comparison [DecidableEq ι] [DecidableEq κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ≠ 0) (K : ℝ)
    (hTrace : ∀ theta ∈ Set.Icc (0 : ℝ) (Real.pi/2), K ≤
      ∫ w, commonTrace ν A L p theta w-physicalTrace ν A L p theta w
        ∂SYK.standardGaussianMeasureOnEuclidean κ) :
    averagedAngularPressure ν A L p 0 ≤ averagedAngularPressure ν A L p (Real.pi/2)-K/2 := by
  let f : ℝ → ℝ := fun theta ↦ averagedAngularPressure ν A L p theta-(K/2)*(Real.sin theta)^2
  let f' : ℝ → ℝ := fun theta ↦ Real.sin theta*Real.cos theta*
    ((∫ w, commonTrace ν A L p theta w-physicalTrace ν A L p theta w
      ∂SYK.standardGaussianMeasureOnEuclidean κ)-K)
  have hDeriv (theta : ℝ) : HasDerivAt f (f' theta) theta := by
    have H := (averagedAngularPressure_hasDerivAt_trace ν A L hA hL hKA hKL hb p hp theta).sub
      (((Real.hasDerivAt_sin theta).pow 2).const_mul (K/2))
    convert H using 1 <;> dsimp only [f,f']
    ring
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun theta ↦ (hDeriv theta).continuousAt)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont.continuousOn
      (fun theta _ ↦ (hDeriv theta).hasDerivWithinAt)
    intro theta htheta
    have ht : theta ∈ Set.Icc (0 : ℝ) (Real.pi/2) := interior_subset htheta
    have hs := Real.sin_nonneg_of_mem_Icc (show theta ∈ Set.Icc (0 : ℝ) Real.pi from
      ⟨ht.1,ht.2.trans (by linarith [Real.pi_pos])⟩)
    have hc := Real.cos_nonneg_of_mem_Icc (show theta ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [Real.pi_pos,ht.1],ht.2⟩)
    exact mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hTrace theta ht))
  have H := hmono (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi/2) from ⟨le_rfl,Real.pi_div_two_pos.le⟩)
    (show Real.pi/2 ∈ Set.Icc (0 : ℝ) (Real.pi/2) from ⟨Real.pi_div_two_pos.le,le_rfl⟩) Real.pi_div_two_pos.le
  simpa only [f,Real.sin_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,sub_zero,
    Real.sin_pi_div_two,one_pow,mul_one] using H

theorem angular_pressure_comparison_of_covariance_bounds [DecidableEq ι] [DecidableEq κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) (B C : ℝ)
    (hDiag : ∀ᵐ v ∂ν, B ≤ coordinateCovariance (L v) (L v)-coordinateCovariance (A v) (A v))
    (hCross : ∀ v u, coordinateCovariance (L v) (L u)-coordinateCovariance (A v) (A u) ≤ C) :
    averagedAngularPressure ν A L p 0 ≤ averagedAngularPressure ν A L p (Real.pi/2)-(B+(p-1)*C)/2 := by
  apply angular_pressure_comparison ν A L hA hL hKA hKL hb p (ne_of_gt hp.1) (B+(p-1)*C)
  intro theta _
  have H := integral_mono_ae (integrable_const (B+(p-1)*C))
    ((common_trace_integrable ν A L hA hL hKA hKL hb p theta).sub
      (physical_trace_integrable ν A L hA hL hKA hKL hb p theta))
    (Filter.Eventually.of_forall (angular_trace_lower ν A L hA hL hKA hKL hb p ⟨hp.1.le,hp.2⟩ B C hDiag hCross theta))
  simpa only [integral_const,probReal_univ,one_smul,Pi.sub_apply] using H

end
end TensorPCA.GaussianAngularComparisonProofs
