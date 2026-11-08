-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarBranchProofs
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The scalar value identity and derivative, independent of probabilistic limits. -/
@[expose] public section
namespace TensorPCA.ScalarValueProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs ScalarBranchProofs
open MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def branchEnergy (k : ℕ) (lam : ℝ) : ℝ :=
  lam*(Real.sqrt (Scalar.qS k lam))^k + Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam))

theorem stationary_sqrt_identity (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    lam*(Real.sqrt (Scalar.qS k lam))^(k-2)*
      Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)) = 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hs := (qS_spec k hk hlam).1
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans hs.1.1
  have hs0 : 0 < (k : ℝ)*(1-Scalar.qS k lam) := mul_pos hk0 (sub_pos.mpr hs.1.2)
  have hp : ((Real.sqrt (Scalar.qS k lam))^(k-2))^2 = (Scalar.qS k lam)^(k-2) := by
    rw [← pow_mul, Nat.mul_comm (k-2) 2, pow_mul, Real.sq_sqrt hq0.le]
  have heq : (lam*(Real.sqrt (Scalar.qS k lam))^(k-2)*
      Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)))^2 = 1 := by
    rw [mul_pow, mul_pow, hp, Real.sq_sqrt hs0.le]
    nlinarith [hs.2]
  have hpos : 0 < lam*(Real.sqrt (Scalar.qS k lam))^(k-2)*
      Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)) :=
    mul_pos (mul_pos hlam0 (pow_pos (Real.sqrt_pos.mpr hq0) _)) (Real.sqrt_pos.mpr hs0)
  nlinarith

theorem hasDerivAt_branchEnergy (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    HasDerivAt (branchEnergy k) ((Real.sqrt (Scalar.qS k lam))^k) lam := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := (qS_spec k hk hlam).1
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans hs.1.1
  have hR0 := mul_pos hk0 (sub_pos.mpr hs.1.2)
  have hq := hasDerivAt_qS k hk hlam
  generalize hderiv : (2*Scalar.qS k lam*(1-Scalar.qS k lam) /
    (lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2)))) = d at hq
  have hm := hq.sqrt hq0.ne'
  have hR := (((hasDerivAt_const lam (1 : ℝ)).sub hq).const_mul (k : ℝ)).sqrt hR0.ne'
  have hp : (Real.sqrt (Scalar.qS k lam))^(k-1) =
      (Real.sqrt (Scalar.qS k lam))^(k-2)*Real.sqrt (Scalar.qS k lam) := by
    rw [← pow_succ]
    congr 1
    omega
  have hid := stationary_sqrt_identity k hk hlam
  convert (((hasDerivAt_id lam).mul (hm.pow k)).add hR) using 1
  · funext mu
    rfl
  · dsimp
    rw [hp]
    field_simp [(Real.sqrt_pos.mpr hq0).ne', (Real.sqrt_pos.mpr hR0).ne']
    nlinarith [congrArg (fun x : ℝ => x*((k : ℝ)*d)) hid]

theorem branchEnergy_eq_explicit (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    branchEnergy k lam = Real.sqrt (k : ℝ)*
      (1+lam^2*(Scalar.qS k lam)^(k-1)) /
      Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := (qS_spec k hk hlam).1
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans hs.1.1
  have hR0 := mul_pos hk0 (sub_pos.mpr hs.1.2)
  have hD0 : 0 < 1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1) := by positivity
  have hpow : (Scalar.qS k lam)^(k-1) =
      (Scalar.qS k lam)^(k-2)*Scalar.qS k lam := by
    rw [← pow_succ]
    congr 1
    omega
  have hsqrt : Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1))*
      Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)) = Real.sqrt (k : ℝ) := by
    rw [← Real.sqrt_mul hD0.le]
    congr 1
    rw [hpow]
    nlinarith [congrArg (fun x : ℝ => x*((k : ℝ)*Scalar.qS k lam)) hs.2]
  have hmpow : (Scalar.qS k lam)^(k-1) =
      (Real.sqrt (Scalar.qS k lam))^k*(Real.sqrt (Scalar.qS k lam))^(k-2) := by
    conv_lhs => rw [← Real.sq_sqrt hq0.le]
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hmag : lam^2*(Scalar.qS k lam)^(k-1)*
      Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)) = lam*(Real.sqrt (Scalar.qS k lam))^k := by
    rw [hmpow]
    calc
      _ = (lam*(Real.sqrt (Scalar.qS k lam))^k)*
          (lam*(Real.sqrt (Scalar.qS k lam))^(k-2)*
            Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam))) := by ring
      _ = _ := by rw [stationary_sqrt_identity k hk hlam, mul_one]
  apply (eq_div_iff (Real.sqrt_pos.mpr hD0).ne').mpr
  unfold branchEnergy
  rw [← hsqrt]
  nlinarith [congrArg (fun x : ℝ => x*
    Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1))) hmag]

theorem supercriticalValue_eq_branchEnergy (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) : Scalar.supercriticalValue k lam = branchEnergy k lam := by
  rw [branchEnergy_eq_explicit k hk ((lambdaS_lt_lambdaC k hk).trans hlam)]
  unfold Scalar.supercriticalValue
  rw [qStar_eq_qS k hk hlam]

theorem branchEnergy_critical (k : ℕ) (hk : 3 ≤ k) :
    branchEnergy k (Scalar.lambdaC k) = Scalar.gs k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : (Scalar.lambdaC k)^2*(Scalar.qS k (Scalar.lambdaC k))^(k-1) = Scalar.zK k/(k : ℝ) := by
    apply (eq_div_iff hk0.ne').mpr
    simpa only [Scalar.CriticalRootIdentity, mul_comm, mul_left_comm, mul_assoc] using criticalRootIdentity k hk
  rw [branchEnergy_eq_explicit k hk (lambdaS_lt_lambdaC k hk)]
  have hden : (Scalar.lambdaC k)^2*(k : ℝ)*(Scalar.qS k (Scalar.lambdaC k))^(k-1) = Scalar.zK k := by
    simpa only [Scalar.CriticalRootIdentity, mul_comm, mul_left_comm, mul_assoc] using criticalRootIdentity k hk
  rw [hx, hden]
  unfold Scalar.gs
  ring

theorem continuousOn_rootPower (k : ℕ) (hk : 3 ≤ k) {a b : ℝ}
    (ha : Scalar.lambdaS k < a) :
    ContinuousOn (fun t : ℝ => (Real.sqrt (Scalar.qS k t))^k) (Icc a b) := by
  intro t ht
  exact (((continuousAt_qS k hk (ha.trans_le ht.1)).sqrt).pow k).continuousWithinAt

/-- The manuscript's integral identity on the supercritical branch. -/
theorem branchEnergy_integral (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) :
    branchEnergy k lam = Scalar.gs k +
      ∫ t in (Scalar.lambdaC k)..lam, (Real.sqrt (Scalar.qS k t))^k := by
  have hc := continuousOn_rootPower k hk (b := lam) (lambdaS_lt_lambdaC k hk)
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hlam.le
  have hderiv : ∀ t ∈ uIcc (Scalar.lambdaC k) lam,
      HasDerivAt (branchEnergy k) ((Real.sqrt (Scalar.qS k t))^k) t := by
    intro t ht
    rw [uIcc_of_le hlam.le] at ht
    exact hasDerivAt_branchEnergy k hk ((lambdaS_lt_lambdaC k hk).trans_le ht.1)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi
  rw [branchEnergy_critical k hk] at heq
  linarith

theorem qStar_rootPower_eq_zero (k : ℕ) (hk : 3 ≤ k) {t : ℝ}
    (ht : t ≤ Scalar.lambdaC k) : (Real.sqrt (Scalar.qStar k t))^k = 0 := by
  simp [Scalar.qStar, ht, show k ≠ 0 by omega]

theorem qStar_rootPower_eq_qS (k : ℕ) (hk : 3 ≤ k) {t : ℝ}
    (ht : Scalar.lambdaC k < t) :
    (Real.sqrt (Scalar.qStar k t))^k = (Real.sqrt (Scalar.qS k t))^k := by
  rw [qStar_eq_qS k hk ht]

/-- The full frozen value agrees with its actual qStar integral for every
nonnegative strength, including the convention at the critical threshold. -/
theorem valueIdentity (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 ≤ lam) :
    Scalar.ValueIdentity k lam := by
  unfold Scalar.ValueIdentity
  by_cases hle : lam ≤ Scalar.lambdaC k
  · have hz : (∫ t in (0 : ℝ)..lam, (Real.sqrt (Scalar.qStar k t))^k) = 0 := by
      calc
        _ = ∫ _t in (0 : ℝ)..lam, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hlam] at ht
          exact qStar_rootPower_eq_zero k hk (ht.2.trans hle)
        _ = 0 := by simp
    simp only [Scalar.mleValue, ite_eq_left hle, hz, add_zero]
  · have hgt := lt_of_not_ge hle
    have hc := continuousOn_rootPower k hk (b := lam) (lambdaS_lt_lambdaC k hk)
    have hi := hc.intervalIntegrable_of_Icc (μ := volume) hgt.le
    have heq0 : EqOn (fun _t : ℝ => (0 : ℝ))
        (fun t : ℝ => (Real.sqrt (Scalar.qStar k t))^k) (uIoc 0 (Scalar.lambdaC k)) := by
      intro t ht
      rw [uIoc_of_le (lambdaC_pos k hk).le] at ht
      exact (qStar_rootPower_eq_zero k hk ht.2).symm
    have hi0 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (Scalar.qStar k t))^k)
        volume 0 (Scalar.lambdaC k) :=
      IntervalIntegrable.congr heq0 (continuous_const.intervalIntegrable _ _)
    have heq1 : EqOn (fun t : ℝ => (Real.sqrt (Scalar.qS k t))^k)
        (fun t : ℝ => (Real.sqrt (Scalar.qStar k t))^k)
        (uIoc (Scalar.lambdaC k) lam) := by
      intro t ht
      rw [uIoc_of_le hgt.le] at ht
      exact (qStar_rootPower_eq_qS k hk ht.1).symm
    have hi1 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (Scalar.qStar k t))^k)
        volume (Scalar.lambdaC k) lam := IntervalIntegrable.congr heq1 hi
    have hz : (∫ t in (0 : ℝ)..(Scalar.lambdaC k),
        (Real.sqrt (Scalar.qStar k t))^k) = 0 := by
      calc
        _ = ∫ _t in (0 : ℝ)..(Scalar.lambdaC k), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le (lambdaC_pos k hk).le] at ht
          exact qStar_rootPower_eq_zero k hk ht.2
        _ = 0 := by simp
    have heqint : (∫ t in (Scalar.lambdaC k)..lam,
        (Real.sqrt (Scalar.qStar k t))^k) =
        ∫ t in (Scalar.lambdaC k)..lam, (Real.sqrt (Scalar.qS k t))^k := by
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall (fun t ht => (heq1 ht).symm)
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, hz, zero_add, heqint]
    rw [Scalar.mleValue, ite_eq_right hle, supercriticalValue_eq_branchEnergy k hk hgt]
    exact branchEnergy_integral k hk hgt

/-- Derivative away from the discontinuous selection threshold. -/
theorem valueDerivative (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (_hlam : 0 < lam) (hne : lam ≠ Scalar.lambdaC k) : Scalar.ValueDerivative k lam := by
  unfold Scalar.ValueDerivative
  by_cases hle : lam ≤ Scalar.lambdaC k
  · have hlt : lam < Scalar.lambdaC k := lt_of_le_of_ne hle hne
    rw [qStar_rootPower_eq_zero k hk hle]
    apply (hasDerivAt_const lam (Scalar.gs k)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with t ht
    simp only [Scalar.mleValue, ite_eq_left ht.le]
  · have hgt := lt_of_not_ge hle
    rw [qStar_rootPower_eq_qS k hk hgt]
    apply (hasDerivAt_branchEnergy k hk ((lambdaS_lt_lambdaC k hk).trans hgt)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with t ht
    rw [Scalar.mleValue, ite_eq_right (not_le_of_gt ht)]
    exact supercriticalValue_eq_branchEnergy k hk ht

end
end TensorPCA.ScalarValueProofs
