-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledScalarProofs

/-! Explicit logarithmic remainder estimates for the local quadratic trial gap. -/
@[expose] public section
namespace TensorPCA.CoupledSmallOverlapProofs
open Set Filter ScalarThresholdProofs CoupledScalarProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem log_one_add_upper {z : ℝ} (hz : 0 ≤ z) :
    Real.log (1+z) ≤ (z+z^2/2)/(1+z) := by
  by_cases hzero : z = 0
  · subst z
    norm_num
  · have hzpos := lt_of_le_of_ne hz (Ne.symm hzero)
    have hu := strictAntiOn_upsilon.antitoneOn (show (0 : ℝ) ∈ Ici 0 from le_rfl) hz hz
    rw [upsilon_zero, upsilon_eq hzpos] at hu
    have hh := (div_le_iff₀ (sq_pos_of_pos hzpos)).mp hu
    apply (le_div_iff₀ (by linarith : 0 < 1+z)).mpr
    nlinarith

theorem neg_log_one_sub_upper {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    -Real.log (1-u) ≤ u+u^2/(2*(1-u)) := by
  have hden : 0 < 1-u := sub_pos.mpr hu.2
  have hz : 0 ≤ u/(1-u) := div_nonneg hu.1 hden.le
  have h := log_one_add_upper hz
  have hsum : 1+u/(1-u) = (1-u)⁻¹ := by field_simp [hden.ne']; ring
  have hrat : (u/(1-u)+(u/(1-u))^2/2)/(1+u/(1-u)) = u+u^2/(2*(1-u)) := by
    rw [hsum]
    field_simp [hden.ne']
  rw [hsum] at hrat
  rw [hsum, Real.log_inv] at h
  exact h.trans_eq hrat

theorem log_ratio_upper {A u : ℝ} (hu : 0 ≤ u) (hA : u < A) :
    Real.log ((A-u)/(A+u)) ≤ -2*u/A := by
  have hden : 0 < A-u := sub_pos.mpr hA
  have hAp : 0 < A+u := by linarith
  have hA0 : 0 < A := by linarith
  by_cases hzero : u = 0
  · subst u
    simp [hA0.ne']
  · have hupos := lt_of_le_of_ne hu (Ne.symm hzero)
    let z : ℝ := 2*u/(A-u)
    have hz : 0 < z := div_pos (by linarith) hden
    have h := two_mul_div_add_two_lt_log hz
    have hsum : 1+z = (A+u)/(A-u) := by unfold z; field_simp [hden.ne']; ring
    have hrat : 2*z/(z+2) = 2*u/A := by
      unfold z
      field_simp [hden.ne',hA0.ne']
      ring
    rw [hsum, hrat, Real.log_div hAp.ne' hden.ne'] at h
    rw [Real.log_div hden.ne' hAp.ne']
    have hneg : -2*u/A = -(2*u/A) := by ring
    rw [hneg]
    linarith

/-- Exact m=1 diagonal trial, on the positive logarithm domain. -/
theorem diagonal_trial_eq (k : ℕ) (lam : ℝ) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    Coupled.trial k lam 1 u u = lam^2-u^2-Real.log (1-u)+
      (1/2 : ℝ)*Real.log ((1+Coupled.xiPrime k lam u-u)/(1+Coupled.xiPrime k lam u+u)) := by
  have ha : 0 ≤ Coupled.xiPrime k lam u := by unfold Coupled.xiPrime; have := hu.1; positivity
  have hA : 0 < 1+Coupled.xiPrime k lam u-u := by linarith [hu.2]
  have hB : 0 < 1+Coupled.xiPrime k lam u+u := by linarith [hu.1]
  have hD : 0 < 1-u := sub_pos.mpr hu.2
  unfold Coupled.trial
  simp only [sub_self, zero_mul, add_zero, one_div, inv_one, one_mul]
  rw [Real.log_div hA.ne' hD.ne',Real.log_div hA.ne' hB.ne']
  ring

/-- The exact diagonal trial has a uniform negative quadratic remainder.
This supplies the needed local Taylor bound with an explicit small radius. -/
theorem uniform_diagonal_trial_gap (k : ℕ) (hk : 4 ≤ k) {barLam : ℝ} (hbar : 0 ≤ barLam) :
    ∃ c : ℝ, c ∈ Ioo (0 : ℝ) (1/2) ∧ ∀ lam ∈ Icc (0 : ℝ) barLam,
      ∀ u ∈ Icc (0 : ℝ) c, (1/2 : ℝ) ≤ 1+(1-1)*Coupled.xiPrime k lam u-u ∧
        Coupled.trial k lam 1 u u ≤ lam^2-u^2/4 := by
  let T : ℝ := (k : ℝ)*barLam^2
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  let c : ℝ := min (1/4 : ℝ) (1/(12*(1+T)))
  have hcpos : 0 < c := lt_min (by norm_num) (one_div_pos.mpr (by positivity))
  have hcquarter : c ≤ (1/4 : ℝ) := min_le_left _ _
  have hcrat : c ≤ 1/(12*(1+T)) := min_le_right _ _
  refine ⟨c,⟨hcpos,by linarith⟩,?_⟩
  intro lam hlam u hu
  have hu0 := hu.1
  have huquarter : u ≤ (1/4 : ℝ) := hu.2.trans hcquarter
  have hu1 : u < 1 := by linarith
  have ha : 0 ≤ Coupled.xiPrime k lam u := by unfold Coupled.xiPrime; positivity
  have hcoeff : (k : ℝ)*lam^2 ≤ T :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hlam.1 hbar).mpr hlam.2) (Nat.cast_nonneg k)
  have hpow : u^(k-1) ≤ u^3 := pow_le_pow_of_le_one hu0 hu1.le (by omega)
  have huc : u ≤ 1/(12*(1+T)) := hu.2.trans hcrat
  have hprod := (le_div_iff₀ (by positivity : 0 < 12*(1+T))).mp huc
  have hTu : T*u ≤ 1/12 := by nlinarith
  have hu2 : u^2 ≤ u := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1.le)]
  have hTu2 : T*u^2 ≤ 1/12 := (mul_le_mul_of_nonneg_left hu2 hT).trans hTu
  have hsmall : Coupled.xiPrime k lam u ≤ u/12 := by
    have hh := mul_le_mul hcoeff hpow (pow_nonneg hu0 (k-1)) hT
    have hh' := mul_le_mul_of_nonneg_right hTu2 hu0
    unfold Coupled.xiPrime
    nlinarith
  refine ⟨by simp only [sub_self,zero_mul,add_zero]; linarith,?_⟩
  have hlog := neg_log_one_sub_upper ⟨hu0,hu1⟩
  have hrem : u^2/(2*(1-u)) ≤ (2/3 : ℝ)*u^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2*(1-u))).mpr
    have hh := mul_le_mul_of_nonneg_left huquarter (sq_nonneg u)
    nlinarith
  have hlogbound : -Real.log (1-u) ≤ u+(2/3 : ℝ)*u^2 := by linarith
  let a := Coupled.xiPrime k lam u
  have hA : 0 < 1+a := by dsimp [a]; linarith
  have hratio := log_ratio_upper hu0 (by dsimp [a]; linarith : u < 1+a)
  have hhalf : (1/2 : ℝ)*Real.log ((1+a-u)/(1+a+u)) ≤ -(u/(1+a)) := by
    calc
      _ ≤ (1/2 : ℝ)*(-2*u/(1+a)) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = _ := by ring
  have hcor : u-u/(1+a) ≤ u^2/12 := by
    have hid : u-u/(1+a) = u*a/(1+a) := by field_simp [hA.ne']; ring
    have hua : 0 ≤ u*a := mul_nonneg hu0 ha
    have hdiv : u*a/(1+a) ≤ u*a := by
      apply (div_le_iff₀ hA).mpr
      nlinarith [mul_nonneg hua ha]
    have hmul := mul_le_mul_of_nonneg_left hsmall hu0
    rw [hid]
    exact hdiv.trans (by nlinarith)
  rw [diagonal_trial_eq k lam ⟨hu0,hu1⟩]
  change lam^2-u^2-Real.log (1-u)+(1/2 : ℝ)*Real.log ((1+a-u)/(1+a+u)) ≤ lam^2-u^2/4
  linarith

end
end TensorPCA.CoupledSmallOverlapProofs
