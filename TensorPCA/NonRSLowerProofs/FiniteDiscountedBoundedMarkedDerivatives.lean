-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransformJets
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedTransformDerivativeBinding
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionLaw

/-! Bounded-mark power/logarithm derivatives as moments of the proved finite discounted
partition PMF. This is a finite coefficient identity; no physical hierarchy
identification is asserted.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedBoundedMarkedDerivatives
open MeasureTheory ProbabilityTheory
open FiniteDiscountedPartitionProofs FiniteDiscountedPartitionLaw
open FiniteDiscountedTransformDerivativeBinding BoundedMarkedPowerTransform
open scoped BigOperators
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem power_markTransform_iteratedDeriv (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) {alpha p : ℝ}
    (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun t : ℝ => (markTransform nu Z alpha t)^(p/alpha)) 0 =
      (-p*normalizer p n)*∑c : OrderedFinpartition n,
        (discountedPartitionPMF alpha p hp hpa ha n c).toReal*
          (∏i,∫v,(Z v)^(c.partSize i) ∂nu) := by
  have halpha : alpha≠0 := ne_of_gt (hp.trans_lt hpa)
  have H := power_comp_derivative_eq_partition_moment halpha (hpa.trans_le ha) hn
    (markTransform_contDiffAt_zero nu hZ hA hb alpha n)
    (markTransform_zero nu Z alpha) (fun j => ∫v,(Z v)^j ∂nu)
    (fun j _ _ => markTransform_iteratedDeriv_zero nu hZ hA hb alpha j)
  simpa only [discountedPartitionPMF_apply,ENNReal.toReal_ofReal (eppf_nonneg hp hpa ha _)] using H

theorem log_markTransform_iteratedDeriv (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) {alpha : ℝ}
    (halpha : 0<alpha) (ha : alpha≤1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun t : ℝ => Real.log (markTransform nu Z alpha t)/alpha) 0 =
      -normalizer 0 n*∑c : OrderedFinpartition n,
        (discountedPartitionPMF alpha 0 le_rfl halpha ha n c).toReal*
          (∏i,∫v,(Z v)^(c.partSize i) ∂nu) := by
  have H := log_comp_derivative_eq_partition_moment halpha.ne' hn
    (markTransform_contDiffAt_zero nu hZ hA hb alpha n)
    (markTransform_zero nu Z alpha) (fun j => ∫v,(Z v)^j ∂nu)
    (fun j _ _ => markTransform_iteratedDeriv_zero nu hZ hA hb alpha j)
  simpa only [discountedPartitionPMF_apply,ENNReal.toReal_ofReal (eppf_nonneg le_rfl halpha ha _)] using H

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedBoundedMarkedDerivatives
