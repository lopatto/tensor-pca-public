-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteIIDLabelCollision
public import TensorPCA.NonRSLowerProofs.GGFiniteEmpiricalNormalizer
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! The empirical mean power is an independent uniform-label replica product integral,
using the canonical finite empirical normalization.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteIIDLabelEmpiricalMoments
open MeasureTheory ProbabilityTheory
open FiniteIIDLabelCollision GGFiniteEmpiricalNormalizer
open scoped BigOperators ENNReal
noncomputable section

theorem uniformLabelLaw_integral (K : ℕ) (hK : 0<K) (marks : Fin K→ℝ) :
    (∫i,marks i ∂uniformLabelLaw K hK)=empiricalMean K (fun x : ℝ => x) marks := by
  rw [uniformLabelLaw,PMF.integral_eq_sum]
  change (∑i : Fin K,((K : ℝ≥0∞)⁻¹).toReal • marks i)=_
  simp only [ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,empiricalMean]
  rw [← Finset.mul_sum,div_eq_mul_inv,mul_comm]

theorem empiricalMean_pow_eq_label_integral (n K : ℕ) (hK : 0<K) (marks : Fin K→ℝ) :
    (empiricalMean K (fun x : ℝ => x) marks)^n=
      ∫labels : Fin n→Fin K,∏j : Fin n,marks (labels j) ∂iidLabelLaw n K hK := by
  rw [iidLabelLaw,integral_fintype_prod_eq_pow,uniformLabelLaw_integral]
  simp only [Fintype.card_fin]

end
end TensorPCA.NonRSLowerProofs.FiniteIIDLabelEmpiricalMoments
