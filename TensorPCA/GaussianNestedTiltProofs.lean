-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianNestedExpectationProofs

/-! The common-disorder probability tilt and its full physical replica response. -/
@[expose] public section
namespace TensorPCA.GaussianNestedTiltProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

def nestedTilt (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : Measure (EuclideanSpace ℝ ι) :=
  (SYK.standardGaussianMeasureOnEuclidean ι).withDensity (fun g ↦ ENNReal.ofReal
    (nestedIntegrand ν (fun _ ↦ 1) A L p w g/nestedNumerator ν (fun _ ↦ 1) A L p w))

theorem nestedIntegrand_one_pos (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    0 < nestedIntegrand ν (fun _ ↦ 1) A L p w g := by
  rw [nestedIntegrand_one_eq ν A L hA hL hb]
  exact mul_pos (powerWeight_pos ν L p g) (powerWeight_pos (gibbsMeasure ν L g) A p w)

theorem nestedTilt_probability (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hKA : 0 ≤ KA) (hKL : 0 ≤ KL) (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : IsProbabilityMeasure (nestedTilt ν A L p w) := by
  have hz := nestedNumerator_one_pos ν A L hA hL hKA hKL hb p w
  have hi := nestedIntegrand_integrable ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
    (hb.mono (fun _ hv ↦ ⟨by norm_num,hv⟩)) p w
  constructor
  rw [nestedTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Filter.Eventually.of_forall (fun g ↦ (div_pos (nestedIntegrand_one_pos ν A L hA hL hb p w g) hz).le)),
    integral_div]
  change ENNReal.ofReal (nestedNumerator ν (fun _ ↦ 1) A L p w /
    nestedNumerator ν (fun _ ↦ 1) A L p w) = 1
  rw [div_self hz.ne', ENNReal.ofReal_one]

theorem nestedTilt_integral_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hKA : 0 ≤ KA) (hKL : 0 ≤ KL) (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ g, f g ∂nestedTilt ν A L p w) =
      (∫ g, nestedIntegrand ν (fun _ ↦ 1) A L p w g*f g ∂SYK.standardGaussianMeasureOnEuclidean ι) /
        nestedNumerator ν (fun _ ↦ 1) A L p w := by
  have hz := nestedNumerator_one_pos ν A L hA hL hKA hKL hb p w
  have hm := ((nestedIntegrand_continuous ν (fun _ ↦ 1) A L measurable_const hA hL
    zero_le_one hKA hKL (hb.mono (fun _ hv ↦ ⟨by norm_num,hv⟩)) p w).measurable.div_const
      (nestedNumerator ν (fun _ ↦ 1) A L p w)).ennreal_ofReal
  rw [nestedTilt, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_pos (nestedIntegrand_one_pos ν A L hA hL hb p w _) hz).le,
    smul_eq_mul]
  rw [← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g ↦ by ring)

theorem nestedExpectation_eq_integral (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hKA : 0 ≤ KA) (hKL : 0 ≤ KL) (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    nestedExpectation ν ρ A L p w =
      ∫ g, expectation (gibbsMeasure ν L g) ρ A w ∂nestedTilt ν A L p w := by
  rw [nestedTilt_integral_eq ν A L hA hL hKA hKL hb]
  unfold nestedExpectation nestedNumerator
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g ↦ by
    change nestedIntegrand ν ρ A L p w g =
      nestedIntegrand ν (fun _ ↦ 1) A L p w g*expectation (gibbsMeasure ν L g) ρ A w
    rw [nestedIntegrand_one_eq ν A L hA hL hb]
    unfold nestedIntegrand powerObservable
    ring)

theorem inner_expectation_one (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    expectation (gibbsMeasure ν L g) (fun _ ↦ 1) A w = 1 := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2)) g
  have hAg := (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ hv.1))
  unfold expectation
  exact div_self (moment_one_pos (gibbsMeasure ν L g) A hA hAg w).ne'

/-- The full physical response has both the common-field p-1 correction and
the separate negative p product of nested means. -/
theorem nestedExpectationDerivative_apply (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w d : EuclideanSpace ℝ κ) :
    nestedExpectationDerivative ν ρ A L p w d =
      (∫ g, expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*A v d) A w+
        (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
          expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w ∂nestedTilt ν A L p w)-
      p*nestedExpectation ν ρ A L p w*
        (∫ g, expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w ∂nestedTilt ν A L p w) := by
  have hf := hb.mono (fun _ hv ↦ hv.2)
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have hD : nestedNumeratorDerivative ν ρ A L p w d = ∫ g,
      nestedIntegrand ν (fun _ ↦ 1) A L p w g*
        (expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*A v d) A w+
          (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
            expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w)
              ∂SYK.standardGaussianMeasureOnEuclidean ι := by
    rw [nestedNumeratorDerivative_apply ν ρ A L hρ hA hL hC hKA hKL hb]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g ↦ by
      change (powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w)*
        (expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*A v d) A w+
          (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
            expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w) =
        nestedIntegrand ν (fun _ ↦ 1) A L p w g*
          (expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*A v d) A w+
            (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
              expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w)
      rw [nestedIntegrand_one_eq ν A L hA hL hf])
  have hD1 : nestedNumeratorDerivative ν (fun _ ↦ 1) A L p w d = p*∫ g,
      nestedIntegrand ν (fun _ ↦ 1) A L p w g*
        expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w
          ∂SYK.standardGaussianMeasureOnEuclidean ι := by
    rw [nestedNumeratorDerivative_apply ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL h1,
      ← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro g
    change powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w*
      (expectation (gibbsMeasure ν L g) (fun v ↦ 1*A v d) A w+
        (p-1)*expectation (gibbsMeasure ν L g) (fun _ ↦ 1) A w*
          expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w) =
      p*(nestedIntegrand ν (fun _ ↦ 1) A L p w g*
        expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w)
    rw [inner_expectation_one ν A L hA hL hf, nestedIntegrand_one_eq ν A L hA hL hf]
    simp only [one_mul]
    ring
  simp only [nestedExpectationDerivative, smul_apply, sub_apply, smul_eq_mul]
  rw [hD,hD1,nestedTilt_integral_eq ν A L hA hL hKA hKL hf,
    nestedTilt_integral_eq ν A L hA hL hKA hKL hf]
  simp only [div_eq_mul_inv]
  ring

end
end TensorPCA.GaussianNestedTiltProofs
