-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumIntegralProofs
public import TensorPCA.ScalarValueProofs

/-! The bounded derivative integrands satisfy reverse Fatou under
Lebesgue measure. The sole asymptotic statistical premise is Bayesian value convergence; the critical strength is removed only on a null singleton. -/
@[expose] public section
namespace TensorPCA.MaximumIntegralLimitProofs
open MeasureTheory ProbabilityTheory Set Filter MaximumDerivativeProofs MaximumIntegralProofs
open scoped Topology RealInnerProductSpace
noncomputable section

theorem qStar_measurable (k : ℕ) (hk : 3 ≤ k) : Measurable (Scalar.qStar k) := by
  apply measurable_of_continuousOn_compl_singleton (Scalar.lambdaC k)
  intro x hx
  exact (ValidationControlProofs.continuousAt_qStar k hk (by simpa only [mem_compl_iff,mem_singleton_iff] using hx)).continuousWithinAt

theorem qStar_mem_Ico_all (k : ℕ) (hk : 3 ≤ k) (t : ℝ) :
    Scalar.qStar k t ∈ Ico (0 : ℝ) 1 := by
  by_cases ht : 0 ≤ t
  · exact (ScalarSelectionProofs.selectionLaws k hk).2.2.2.2.2.2 t ht
  · have hc := ScalarStaticRatioProofs.lambdaC_pos k hk
    have hle : t ≤ Scalar.lambdaC k := by linarith
    simp only [Scalar.qStar,ite_eq_left hle,mem_Ico]
    exact ⟨le_rfl,zero_lt_one⟩

theorem qStar_rootPower_abs_le_one (k : ℕ) (hk : 3 ≤ k) (t : ℝ) :
    |(Real.sqrt (Scalar.qStar k t))^k| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
  exact pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (qStar_mem_Ico_all k hk t).2.le)

/-- Genuine integrated signed-overlap limsup upper bound. No MLE-value upper
bound or limiting derivative is taken as a hypothesis. -/
theorem integrated_selectedSlope_limsup_le_of_values (k : ℕ) (hk : 2 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence (k+1)) {lam : ℝ} (hlam : 0 ≤ lam) :
    limsup (fun n : ℕ ↦ ∫ t in (0 : ℝ)..lam,
      selectedSlope (n+1) k (Nat.succ_pos n) t) atTop ≤
      ∫ t in (0 : ℝ)..lam, (Real.sqrt (Scalar.qStar (k+1) t))^(k+1) := by
  have hAE : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) lam),
      limsup (fun n : ℕ ↦ selectedSlope (n+1) k (Nat.succ_pos n) t) atTop ≤
        (Real.sqrt (Scalar.qStar (k+1) t))^(k+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (show ∀ᵐ t : ℝ ∂volume, t ≠ Scalar.lambdaC (k+1) from by simp [ae_iff]))] with t ht hne
    exact selectedSlope_limsup_le_of_values k hk hvalues ht.1.le hne
  have H := limsup_integral_le_of_unit_bound (volume.restrict (Ioc (0 : ℝ) lam))
    (fun n : ℕ ↦ selectedSlope (n+1) k (Nat.succ_pos n))
    (fun t ↦ (Real.sqrt (Scalar.qStar (k+1) t))^(k+1))
    (fun n ↦ selectedSlope_measurable (n+1) k (Nat.succ_pos n))
    (((qStar_measurable (k+1) (by omega)).sqrt).pow_const (k+1))
    (fun n t ↦ selectedSlope_abs_le_one (n+1) k (Nat.succ_pos n) t)
    (qStar_rootPower_abs_le_one (k+1) (by omega)) hAE
  simpa only [intervalIntegral.integral_of_le hlam] using H

end
end TensorPCA.MaximumIntegralLimitProofs
