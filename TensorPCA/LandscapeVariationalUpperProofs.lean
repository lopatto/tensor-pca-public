-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PureVariationalProofs
public import TensorPCA.ScalarStationaryProofs
public import TensorPCA.PlateauVariationalTrialProofs

/-! A direct variational certificate for the critical low-overlap landscape.
The competitor is the pure affine profile, made constant before one breakpoint.
Its scalar remainder is exactly minus the critical scalar potential. -/
@[expose] public section
namespace TensorPCA.LandscapeVariationalUpperProofs

open Set MeasureTheory
open PureVariationalProofs ScalarThresholdProofs ScalarStaticRatioProofs
  ScalarStationaryProofs

noncomputable section

theorem xiSlice_variationalValue_le_half_functional (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) {p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p) :
    Scalar.variationalValue (Scalar.xiSlice k m) 0 ≤
      (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0 p := by
  let S : Set ℝ := {v | ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧
    v = Scalar.parisiFunctional (Scalar.xiSlice k m) 0 p}
  have hbeta := VariationalProofs.one_sub_sq_nonneg hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hdd : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ deriv (deriv (Scalar.xiSlice k m)) t := by
    intro t ht
    rw [(VariationalProofs.hasDerivAt_deriv_xiSlice (show 1 ≤ k by omega) m t).deriv]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (sq_nonneg _)) (pow_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hbeta ht.1)) _)
  have hb : 0 ≤ deriv (Scalar.xiSlice k m) 0 := by
    rw [VariationalProofs.deriv_xiSlice]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hbeta)
      (pow_nonneg (by nlinarith [sq_nonneg m]) _)
  have hbb : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro v ⟨r, hr, rfl⟩
    unfold Scalar.parisiFunctional
    apply add_nonneg
    · apply intervalIntegral.integral_nonneg zero_le_one
      intro t ht
      exact add_nonneg (mul_nonneg (hdd t ht) (hr.2.2.2 t ht).le)
        (one_div_pos.mpr (hr.2.2.2 t ht)).le
    · simpa using mul_nonneg hb (hr.2.2.2 0 (by norm_num)).le
  exact mul_le_mul_of_nonneg_left (csInf_le hbb ⟨p, hp, rfl⟩) (by norm_num)

theorem pureA_div_initial (k : ℕ) (hk : 3 ≤ k) :
    pureA k / (pureC k + pureA k) = criticalOverlap k := by
  have hz := (zK_spec k hk).1
  have hc := pureC_pos k hk
  unfold pureA criticalOverlap staticOverlap
  field_simp

theorem pureA_eq_critical_signal (k : ℕ) (hk : 3 ≤ k) :
    pureA k = Scalar.lambdaC k * (Real.sqrt (criticalOverlap k)) ^ k := by
  have hc := pureC_pos k hk
  have ha := pureA_pos k hk
  have hq := criticalOverlap_mem_Ioo k hk
  have hlam := lambdaC_pos k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hstation := (criticalOverlap_stable k hk).2
  have hp : ((Real.sqrt (criticalOverlap k)) ^ k) ^ 2 = (criticalOverlap k) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hq.1.le]
  have hqpow : (criticalOverlap k) ^ k =
      (criticalOverlap k) ^ (k - 2) * (criticalOverlap k) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hratio : (criticalOverlap k) ^ 2 / (1 - criticalOverlap k) =
      (Scalar.zK k) ^ 2 / (1 + Scalar.zK k) := by
    have hz := (zK_spec k hk).1
    unfold criticalOverlap staticOverlap
    field_simp
    ring
  have hsq : (pureA k) ^ 2 =
      (Scalar.lambdaC k * (Real.sqrt (criticalOverlap k)) ^ k) ^ 2 := by
    rw [mul_pow, hp, hqpow]
    have hst : (Scalar.lambdaC k) ^ 2 * (criticalOverlap k) ^ (k - 2) =
        1 / ((k : ℝ) * (1 - criticalOverlap k)) := by
      apply (eq_div_iff (mul_pos hk0 (sub_pos.mpr hq.2)).ne').mpr
      nlinarith [hstation]
    rw [← mul_assoc, hst]
    unfold pureA
    rw [mul_pow, pureC_sq k hk]
    have hkr : (k : ℝ) ≠ 0 := by positivity
    calc
      Scalar.zK k ^ 2 * (1 / ((k : ℝ) * (1 + Scalar.zK k))) =
          (Scalar.zK k ^ 2 / (1 + Scalar.zK k)) / (k : ℝ) := by field_simp
      _ = ((criticalOverlap k) ^ 2 / (1 - criticalOverlap k)) / (k : ℝ) := by rw [hratio]
      _ = _ := by field_simp
  have hright : 0 < Scalar.lambdaC k * (Real.sqrt (criticalOverlap k)) ^ k :=
    mul_pos hlam (pow_pos (Real.sqrt_pos.mpr hq.1) _)
  nlinarith

theorem gs_eq_pure_coefficients (k : ℕ) (hk : 3 ≤ k) :
    Scalar.gs k = (k : ℝ) * pureC k + pureA k := by
  rw [gs_eq_normalized k hk]
  dsimp [pureC, pureA]
  ring

theorem pure_log_ratio (k : ℕ) (hk : 3 ≤ k) :
    Real.log ((pureC k + pureA k) / pureC k) = pureA k * Scalar.gs k := by
  have hc := pureC_pos k hk
  have hratio : (pureC k + pureA k) / pureC k = 1 + Scalar.zK k := by
    unfold pureA
    field_simp
  rw [hratio, log_one_add_zK k hk, gs_eq_pure_coefficients k hk]
  unfold pureA
  rw [show Scalar.zK k * pureC k * ((k : ℝ) * pureC k + Scalar.zK k * pureC k) =
    Scalar.zK k * ((k : ℝ) + Scalar.zK k) * (pureC k) ^ 2 by ring,
    pureC_sq k hk]
  ring

/-- The explicit half-cost after substituting the critical-overlap cutoff.
Its identification with an admissible slice profile is proved separately. -/
def criticalTrialHalfCost (k : ℕ) (r : ℝ) : ℝ :=
  ((k : ℝ) * pureC k + pureA k * (1 - r ^ k) +
    Real.log (affineProfile (pureC k) (pureA k) r / pureC k) / pureA k +
    r / (pureC k + pureA k)) / 2

theorem critical_trial_gap (k : ℕ) (hk : 3 ≤ k) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    2 * pureA k * (Scalar.gs k - criticalTrialHalfCost k r -
      Scalar.lambdaC k * (Real.sqrt (criticalOverlap k) * r) ^ k) =
      -Scalar.f k (Scalar.lambdaC k) (criticalOverlap k * r) := by
  have hc := pureC_pos k hk
  have ha := pureA_pos k hk
  have hq := criticalOverlap_mem_Ioo k hk
  have hP : 0 < pureC k + pureA k := by positivity
  have hu : 0 < 1 - criticalOverlap k * r := by
    apply sub_pos.mpr
    exact (mul_le_mul_of_nonneg_left hr.2 hq.1.le).trans_lt (by simpa using hq.2)
  have hprofile : affineProfile (pureC k) (pureA k) r =
      (pureC k + pureA k) * (1 - criticalOverlap k * r) := by
    rw [← pureA_div_initial k hk]
    unfold affineProfile
    field_simp
    ring
  have hlog : Real.log (affineProfile (pureC k) (pureA k) r / pureC k) =
      pureA k * Scalar.gs k + Real.log (1 - criticalOverlap k * r) := by
    rw [hprofile, mul_div_right_comm, Real.log_mul
      (div_pos hP hc).ne' hu.ne', pure_log_ratio k hk]
  have hscale : (Scalar.lambdaC k) ^ 2 * (criticalOverlap k * r) ^ k =
      (pureA k) ^ 2 * r ^ k := by
    rw [mul_pow, pureA_eq_critical_signal k hk, mul_pow, ← pow_mul,
      Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hq.1.le]
    ring
  have hsignal : pureA k *
      (Scalar.lambdaC k * (Real.sqrt (criticalOverlap k) * r) ^ k) =
      (pureA k) ^ 2 * r ^ k := by
    calc
      _ = pureA k * (Scalar.lambdaC k * (Real.sqrt (criticalOverlap k)) ^ k) * r ^ k := by
        rw [mul_pow]
        ring
      _ = _ := by rw [← pureA_eq_critical_signal k hk]; ring
  have hratio := pureA_div_initial k hk
  have hgs := gs_eq_pure_coefficients k hk
  have H : pureA k * (r / (pureC k + pureA k)) = criticalOverlap k * r := by
    rw [← hratio]
    ring
  have hcost : 2 * pureA k * criticalTrialHalfCost k r =
      pureA k * ((k : ℝ) * pureC k + pureA k * (1 - r ^ k)) +
        pureA k * Scalar.gs k + Real.log (1 - criticalOverlap k * r) +
        criticalOverlap k * r := by
    calc
      _ = pureA k * ((k : ℝ) * pureC k + pureA k * (1 - r ^ k)) +
          Real.log (affineProfile (pureC k) (pureA k) r / pureC k) +
          pureA k * (r / (pureC k + pureA k)) := by
        unfold criticalTrialHalfCost
        field_simp
      _ = _ := by rw [hlog, H]; ring
  calc
    _ = 2 * pureA k * Scalar.gs k - 2 * pureA k * criticalTrialHalfCost k r -
        2 * (pureA k * (Scalar.lambdaC k * (Real.sqrt (criticalOverlap k) * r) ^ k)) := by ring
    _ = -Scalar.f k (Scalar.lambdaC k) (criticalOverlap k * r) := by
      rw [hcost, hsignal]
      unfold Scalar.f
      rw [hscale, hgs]
      ring

theorem critical_trial_bound (k : ℕ) (hk : 3 ≤ k) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    Scalar.lambdaC k * (Real.sqrt (criticalOverlap k) * r) ^ k +
      criticalTrialHalfCost k r ≤ Scalar.gs k := by
  have hq := criticalOverlap_mem_Ioo k hk
  have hu : criticalOverlap k * r ∈ Ico (0 : ℝ) 1 := by
    refine ⟨mul_nonneg hq.1.le hr.1, ?_⟩
    exact (mul_le_mul_of_nonneg_left hr.2 hq.1.le).trans_lt (by simpa using hq.2)
  have H := f_nonpos_at_critical k hk _ hu
  have hgap := critical_trial_gap k hk hr
  have ha := pureA_pos k hk
  nlinarith

theorem critical_energy_param_le_gs (k : ℕ) (hk : 3 ≤ k) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    Scalar.energy k (Scalar.lambdaC k) (Real.sqrt (criticalOverlap k) * r) ≤
      Scalar.gs k := by
  let m := Real.sqrt (criticalOverlap k) * r
  let beta := 1 - m ^ 2
  let s := (r - m ^ 2) / beta
  let delta := pureC k / beta
  have hc := pureC_pos k hk
  have ha := pureA_pos k hk
  have hq := criticalOverlap_mem_Ioo k hk
  have hP : 0 < pureC k + pureA k := by positivity
  have hm0 : 0 ≤ m := mul_nonneg (Real.sqrt_nonneg _) hr.1
  have hm2 : m ^ 2 = criticalOverlap k * r ^ 2 := by
    dsimp [m]
    rw [mul_pow, Real.sq_sqrt hq.1.le]
  have hr2 : r ^ 2 ≤ r := by nlinarith [hr.1, hr.2]
  have hm2r : m ^ 2 ≤ r := by
    rw [hm2]
    exact (mul_le_of_le_one_left (sq_nonneg r) hq.2.le).trans hr2
  have hm2Q : m ^ 2 ≤ criticalOverlap k := by
    rw [hm2]
    exact mul_le_of_le_one_right hq.1.le (hr2.trans hr.2)
  have hb : 0 < beta := sub_pos.mpr (hm2Q.trans_lt hq.2)
  have hm : m ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · linarith
    · nlinarith [hm2Q, hq.2]
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hm2r) hb.le, ?_⟩
    exact (div_le_one hb).mpr (by dsimp [beta]; linarith [hr.2])
  have hd : 0 < delta := div_pos hc hb
  have had : Scalar.AdmissibleProfile (Scalar.fourParameterProfile delta 0 (pureA k) s) :=
    VariationalProofs.fourParameterProfile_admissible _ _ _ _ ⟨hd, le_rfl, ha.le, hs⟩
  have hbase : m ^ 2 + (1 - m ^ 2) * s = r := by
    dsimp [s, beta]
    field_simp [show 1 - m ^ 2 ≠ 0 from hb.ne']
    ring
  have hprofile : affineProfile (pureC k) (pureA k) r =
      (pureC k + pureA k) * (1 - criticalOverlap k * r) := by
    rw [← pureA_div_initial k hk]
    unfold affineProfile
    field_simp
    ring
  have hu : 0 < 1 - criticalOverlap k * r := by
    apply sub_pos.mpr
    exact (mul_le_mul_of_nonneg_left hr.2 hq.1.le).trans_lt (by simpa using hq.2)
  have hhead : delta + pureA k * (1 - s) =
      affineProfile (pureC k) (pureA k) r / beta := by
    dsimp [delta, s, beta]
    unfold affineProfile
    field_simp [show 1 - m ^ 2 ≠ 0 from hb.ne']
    ring
  have hrecip : s / (delta + pureA k * (1 - s)) = r / (pureC k + pureA k) := by
    rw [hhead, hprofile]
    dsimp [s]
    rw [hm2]
    field_simp [hb.ne', hP.ne', hu.ne',
      show 1 - r * criticalOverlap k ≠ 0 by nlinarith [hu]]
  have hlogarg : (delta + pureA k * (1 - s)) / delta =
      affineProfile (pureC k) (pureA k) r / pureC k := by
    rw [hhead]
    dsimp [delta]
    field_simp
  have hxi : Scalar.xiSlice k m 1 - Scalar.xiSlice k m s = 1 - r ^ k := by
    unfold Scalar.xiSlice
    rw [hbase]
    have H : m ^ 2 + (1 - m ^ 2) * 1 = 1 := by ring
    rw [H, one_pow]
    ring
  have hcost : Scalar.parisiFunctional (Scalar.xiSlice k m) 0
      (Scalar.fourParameterProfile delta 0 (pureA k) s) =
      2 * criticalTrialHalfCost k r := by
    rw [PlateauVariationalTrialProofs.parisiFunctional_xiSlice_plateau k
      (show 1 ≤ k by omega) m hd ha hs,
      VariationalProofs.deriv_xiSlice_one, hxi, hrecip, hlogarg]
    unfold criticalTrialHalfCost
    dsimp [delta, beta]
    field_simp [show 1 - m ^ 2 ≠ 0 from hb.ne']
    ring
  have hvar := xiSlice_variationalValue_le_half_functional k hk hm had
  have htrial := critical_trial_bound k hk hr
  change Scalar.lambdaC k * m ^ k + Scalar.variationalValue (Scalar.xiSlice k m) 0 ≤ _
  rw [hcost] at hvar
  change Scalar.lambdaC k * m ^ k + criticalTrialHalfCost k r ≤ _ at htrial
  linarith

theorem critical_energy_le_gs (k : ℕ) (hk : 3 ≤ k) {m : ℝ} (hm0 : 0 ≤ m)
    (hmC : m ≤ Real.sqrt (criticalOverlap k)) :
    Scalar.energy k (Scalar.lambdaC k) m ≤ Scalar.gs k := by
  have hq := criticalOverlap_mem_Ioo k hk
  have hroot := Real.sqrt_pos.mpr hq.1
  have hr : m / Real.sqrt (criticalOverlap k) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hm0 hroot.le, (div_le_one hroot).mpr hmC⟩
  have H := critical_energy_param_le_gs k hk hr
  simpa only [mul_div_cancel₀ _ hroot.ne'] using H


end
end TensorPCA.LandscapeVariationalUpperProofs
