-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumIntegralLimitProofs
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The expected MLE maximum upper bound follows from finite derivative
integration, Bayesian values and a pure null ground-state baseline.
No MLE-value comparison or limiting maximum is assumed. -/
@[expose] public section
namespace TensorPCA.MaximumExpectedUpperProofs
open MeasureTheory ProbabilityTheory Set Filter MaximumDerivativeProofs MaximumIntegralLimitProofs
open scoped Topology RealInnerProductSpace
noncomputable section

theorem selectedSlope_integral_abs_le (N k : ℕ) (hN : 0 < N) {lam : ℝ} (hlam : 0 ≤ lam) :
    |∫ t in (0 : ℝ)..lam, selectedSlope N k hN t| ≤ lam := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := lam)
    (C := (1 : ℝ)) (f := selectedSlope N k hN) (fun t _ht ↦ by
      simpa only [Real.norm_eq_abs] using selectedSlope_abs_le_one N k hN t)
  simpa only [Real.norm_eq_abs,sub_zero,one_mul,abs_of_nonneg hlam] using H

/-- Genuine Lemma5.8 route: reverse Fatou bounds the actual finite-N signed
MLE derivative integrals, and pure null convergence supplies only the baseline. -/
theorem expectedMaximum_limsup_upper_of_values_and_baseline (k : ℕ) (hk : 2 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence (k+1))
    (hbase : Tendsto (fun n : ℕ ↦ Model.expectedMaximum (n+1) (k+1) 0) atTop
      (𝓝 (Scalar.gs (k+1)))) {lam : ℝ} (hlam : 0 ≤ lam) :
    limsup (fun n : ℕ ↦ Model.expectedMaximum (n+1) (k+1) lam) atTop ≤
      Scalar.mleValue (k+1) lam := by
  let b := fun n : ℕ ↦ Model.expectedMaximum (n+1) (k+1) 0
  let I := fun n : ℕ ↦ ∫ t in (0 : ℝ)..lam, selectedSlope (n+1) k (Nat.succ_pos n) t
  have hIbound (n : ℕ) : |I n| ≤ lam := selectedSlope_integral_abs_le (n+1) k (Nat.succ_pos n) hlam
  have hIlower : atTop.IsCoboundedUnder (· ≤ ·) I :=
    isCoboundedUnder_le_of_le atTop (fun n ↦ (abs_le.mp (hIbound n)).1)
  have hIupper : atTop.IsBoundedUnder (· ≤ ·) I :=
    isBoundedUnder_of ⟨lam,fun n ↦ (abs_le.mp (hIbound n)).2⟩
  have hsum : limsup (fun n ↦ b n+I n) atTop ≤ Scalar.gs (k+1)+
      ∫ t in (0 : ℝ)..lam, (Real.sqrt (Scalar.qStar (k+1) t))^(k+1) := by
    have H := limsup_add_le hbase.isBoundedUnder_ge hbase.isBoundedUnder_le hIlower hIupper
    apply (show limsup (fun n ↦ b n+I n) atTop ≤ limsup b atTop+limsup I atTop from H).trans
    rw [hbase.limsup_eq]
    exact add_le_add (le_refl _) (integrated_selectedSlope_limsup_le_of_values k hk hvalues hlam)
  have heq : limsup (fun n : ℕ ↦ Model.expectedMaximum (n+1) (k+1) lam) atTop =
      limsup (fun n ↦ b n+I n) atTop := by
    apply limsup_congr
    exact Eventually.of_forall (fun n ↦ expectedMaximum_integral_identity (n+1) k (Nat.succ_pos n) 0 lam)
  rw [heq]
  apply hsum.trans_eq
  exact (ScalarValueProofs.valueIdentity (k+1) (by omega) hlam).symm

end
end TensorPCA.MaximumExpectedUpperProofs
