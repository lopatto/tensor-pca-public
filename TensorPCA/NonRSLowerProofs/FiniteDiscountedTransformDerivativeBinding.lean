-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedScalarDerivatives
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! The standard all-order chain rule with the exact discounted partition
coefficients. The inner transform's mark-moment derivatives are explicit proof
parameters here: this does not claim differentiation under a mark integral. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedTransformDerivativeBinding
open FiniteDiscountedPartitionProofs FiniteDiscountedPartitionCoefficients
open FiniteDiscountedScalarDerivatives
open scoped BigOperators ContDiff
noncomputable section

theorem power_comp_derivative_eq_partition_moment {alpha p : ℝ}
    (ha : alpha≠0) (hp : p<1) {n : ℕ} (hn : 0<n) {f : ℝ→ℝ}
    (hf : ContDiffAt ℝ n f 0) (hf0 : f 0=1) (moment : ℕ→ℝ)
    (hjet : ∀j,0<j→j≤n→iteratedDeriv j f 0=
      ((-1 : ℝ)^j*(descPochhammer ℝ j).eval alpha)*moment j) :
    iteratedDeriv n (fun t : ℝ => (f t)^(p/alpha)) 0 =
      (-p*normalizer p n)*
        ∑c : OrderedFinpartition n,eppf alpha p c*(∏i,moment (c.partSize i)) := by
  have hg : ContDiffAt ℝ n (fun y : ℝ => y^(p/alpha)) (f 0) := by
    rw [hf0]
    exact contDiffAt_id.rpow_const_of_ne one_ne_zero
  change iteratedDeriv n ((fun y : ℝ => y^(p/alpha))∘f) 0=_
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf le_rfl,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [hf0,iteratedDeriv_rpow_one]
  rw [← outer_partition_coefficient ha hp hn c (fun i => moment (c.partSize i))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact hjet _ (c.partSize_pos i) (c.partSize_le i)

theorem log_comp_derivative_eq_partition_moment {alpha : ℝ}
    (ha : alpha≠0) {n : ℕ} (hn : 0<n) {f : ℝ→ℝ}
    (hf : ContDiffAt ℝ n f 0) (hf0 : f 0=1) (moment : ℕ→ℝ)
    (hjet : ∀j,0<j→j≤n→iteratedDeriv j f 0=
      ((-1 : ℝ)^j*(descPochhammer ℝ j).eval alpha)*moment j) :
    iteratedDeriv n (fun t : ℝ => Real.log (f t)/alpha) 0 =
      -normalizer 0 n*
        ∑c : OrderedFinpartition n,eppf alpha 0 c*(∏i,moment (c.partSize i)) := by
  have hg : ContDiffAt ℝ n (fun y : ℝ => Real.log y/alpha) (f 0) := by
    rw [hf0]
    exact (Real.contDiffAt_log.mpr one_ne_zero).div_const alpha
  change iteratedDeriv n ((fun y : ℝ => Real.log y/alpha)∘f) 0=_
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf le_rfl,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [hf0]
  have H : iteratedDeriv c.length (fun y : ℝ => Real.log y/alpha) 1=
      ((-1 : ℝ)^(c.length-1)*((c.length-1).factorial : ℝ))/alpha := by
    obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (c.length_pos hn))
    rw [hs]
    simpa using iteratedDeriv_log_div_one alpha s
  rw [H,← logarithmic_partition_coefficient ha hn c (fun i => moment (c.partSize i))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact hjet _ (c.partSize_pos i) (c.partSize_le i)

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedTransformDerivativeBinding
