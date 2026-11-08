-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarStaticRatioProofs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! Stationary-branch calculus for the scalar potential. Central scalar
selections retain their supremum definitions. -/
@[expose] public section
namespace TensorPCA.ScalarStationaryProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def turningPoint (k : ℕ) : ℝ := ((k : ℝ)-2)/((k : ℝ)-1)
def beta (k : ℕ) (q : ℝ) : ℝ := q^(k-2)*(1-q)

theorem turningPoint_mem_Ioo (k : ℕ) (hk : 3 ≤ k) :
    turningPoint k ∈ Ioo (0 : ℝ) 1 := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold turningPoint
  constructor
  · exact div_pos (by linarith) (by linarith)
  · exact (div_lt_one (by linarith : 0 < (k : ℝ)-1)).mpr (by linarith)

theorem hasDerivAt_beta (k : ℕ) (hk : 3 ≤ k) (q : ℝ) :
    HasDerivAt (beta k) (q^(k-3)*((k : ℝ)-2-((k : ℝ)-1)*q)) q := by
  have h := (hasDerivAt_pow (k-2) q).mul
    ((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q))
  have hpow : q^(k-2) = q^(k-3)*q := by
    rw [← pow_succ]
    congr 1
    omega
  convert h using 1
  · ext u
    rfl
  · dsimp
    simp only [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_ofNat, Nat.sub_sub]
    rw [hpow]
    ring

theorem strictAntiOn_beta_right (k : ℕ) (hk : 3 ≤ k) :
    StrictAntiOn (beta k) (Icc (turningPoint k) 1) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ht := turningPoint_mem_Ioo k hk
  have hc : Continuous (beta k) := by unfold beta; fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc.continuousOn
  intro q hq
  have hq' : turningPoint k < q ∧ q < 1 := by
    simpa only [interior_Icc, mem_Ioo] using hq
  have hq0 : 0 < q := ht.1.trans hq'.1
  have hlinear : (k : ℝ)-2-((k : ℝ)-1)*q < 0 := by
    have hleft := (div_lt_iff₀ (by linarith : 0 < (k : ℝ)-1)).mp hq'.1
    nlinarith
  rw [(hasDerivAt_beta k hk q).deriv]
  exact mul_neg_of_pos_of_neg (pow_pos hq0 _) hlinear

theorem stableStationaryPoint_unique (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {q r : ℝ}
    (hq : Scalar.StableStationaryPoint k lam q)
    (hr : Scalar.StableStationaryPoint k lam r) : q = r := by
  have hqeq : ((k : ℝ)*lam^2)*beta k q = 1 := by
    simpa only [beta, mul_assoc] using hq.2
  have hreq : ((k : ℝ)*lam^2)*beta k r = 1 := by
    simpa only [beta, mul_assoc] using hr.2
  have hnonzero : (k : ℝ)*lam^2 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hqeq
    norm_num at hqeq
  have heq : beta k q = beta k r := mul_left_cancel₀ hnonzero (hqeq.trans hreq.symm)
  exact (strictAntiOn_beta_right k hk).injOn
    ⟨hq.1.1.le, hq.1.2.le⟩ ⟨hr.1.1.le, hr.1.2.le⟩ heq

theorem criticalOverlap_gt_turningPoint (k : ℕ) (hk : 3 ≤ k) :
    turningPoint k < criticalOverlap k := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hz := zK_spec k hk
  unfold turningPoint criticalOverlap staticOverlap
  apply (div_lt_div_iff₀ (by linarith : 0 < (k : ℝ)-1)
    (by linarith [hz.1] : 0 < 1+Scalar.zK k)).mpr
  nlinarith [zK_gt_sub_two k hk]

theorem criticalOverlap_stable (k : ℕ) (hk : 3 ≤ k) :
    Scalar.StableStationaryPoint k (Scalar.lambdaC k) (criticalOverlap k) := by
  have hq := criticalOverlap_mem_Ioo k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨⟨criticalOverlap_gt_turningPoint k hk, hq.2⟩, ?_⟩
  rw [lambdaC_sq k hk]
  unfold criticalSquared
  rw [criticalRatio_value k hk]
  field_simp [hk0.ne', hq.1.ne', (sub_pos.mpr hq.2).ne']

theorem qS_at_critical (k : ℕ) (hk : 3 ≤ k) :
    Scalar.qS k (Scalar.lambdaC k) = criticalOverlap k := by
  have hstable := criticalOverlap_stable k hk
  have hset : {q : ℝ | Scalar.StableStationaryPoint k (Scalar.lambdaC k) q} =
      {criticalOverlap k} := by
    ext q
    constructor
    · intro hq
      exact mem_singleton_iff.mpr (stableStationaryPoint_unique k hk _ hq hstable)
    · intro hq
      have heq : q = criticalOverlap k := mem_singleton_iff.mp hq
      change Scalar.StableStationaryPoint k (Scalar.lambdaC k) q
      simpa only [heq] using hstable
  unfold Scalar.qS
  rw [hset]
  simp

/-- Exact critical matching, derived from the actual supremum-selected branch. -/
theorem criticalRootIdentity (k : ℕ) (hk : 3 ≤ k) : Scalar.CriticalRootIdentity k := by
  have hq := criticalOverlap_mem_Ioo k hk
  have hz := zK_spec k hk
  have hpow : (criticalOverlap k)^(k-1) = (criticalOverlap k)^(k-2)*criticalOverlap k := by
    rw [← pow_succ]
    congr 1
    omega
  have hchange : criticalOverlap k/(1-criticalOverlap k) = Scalar.zK k := by
    unfold criticalOverlap staticOverlap
    field_simp [show 1+Scalar.zK k ≠ 0 by linarith [hz.1]]
    ring
  unfold Scalar.CriticalRootIdentity
  rw [qS_at_critical k hk, hpow, ← hchange]
  apply (eq_div_iff (sub_pos.mpr hq.2).ne').mpr
  calc
    _ = ((k : ℝ)*(Scalar.lambdaC k)^2*(criticalOverlap k)^(k-2)*
      (1-criticalOverlap k))*criticalOverlap k := by ring
    _ = criticalOverlap k := by rw [(criticalOverlap_stable k hk).2, one_mul]

theorem beta_turningPoint (k : ℕ) (hk : 3 ≤ k) :
    beta k (turningPoint k) = ((k : ℝ)-2)^(k-2)/((k : ℝ)-1)^(k-1) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (k : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have hsub : 1-((k : ℝ)-2)/((k : ℝ)-1) = 1/((k : ℝ)-1) := by
    field_simp [hden]
    ring
  have hpow : ((k : ℝ)-1)^(k-1) = ((k : ℝ)-1)^(k-2)*((k : ℝ)-1) := by
    rw [← pow_succ]
    congr 1
    omega
  unfold beta turningPoint
  rw [div_pow, hsub, hpow, div_mul_div_comm, mul_one]

theorem lambdaS_pos (k : ℕ) (hk : 3 ≤ k) : 0 < Scalar.lambdaS k := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold Scalar.lambdaS
  apply Real.sqrt_pos.mpr
  exact div_pos (pow_pos (by linarith) _)
    (mul_pos (by linarith) (pow_pos (by linarith) _))

theorem lambdaS_sq (k : ℕ) (hk : 3 ≤ k) :
    (Scalar.lambdaS k)^2 = 1/((k : ℝ)*beta k (turningPoint k)) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h1 : (k : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : (k : ℝ)-2 ≠ 0 := ne_of_gt (by linarith)
  unfold Scalar.lambdaS
  rw [Real.sq_sqrt (div_pos (pow_pos (by linarith) _)
    (mul_pos (by linarith) (pow_pos (by linarith) _))).le, beta_turningPoint k hk]
  field_simp [hk0, h1, h2]

theorem lambdaC_sq_beta (k : ℕ) (hk : 3 ≤ k) :
    (Scalar.lambdaC k)^2 = 1/((k : ℝ)*beta k (criticalOverlap k)) := by
  rw [lambdaC_sq k hk]
  unfold criticalSquared
  rw [criticalRatio_value k hk]
  simp only [beta, mul_assoc]

/-- The statistical threshold is strictly above the spinodal threshold. -/
theorem lambdaS_lt_lambdaC (k : ℕ) (hk : 3 ≤ k) :
    Scalar.lambdaS k < Scalar.lambdaC k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ht := turningPoint_mem_Ioo k hk
  have hq := criticalOverlap_mem_Ioo k hk
  have hbelow := (strictAntiOn_beta_right k hk)
    ⟨le_rfl, ht.2.le⟩ ⟨(criticalOverlap_gt_turningPoint k hk).le, hq.2.le⟩
    (criticalOverlap_gt_turningPoint k hk)
  have hBt : 0 < beta k (turningPoint k) :=
    mul_pos (pow_pos ht.1 _) (sub_pos.mpr ht.2)
  have hBq : 0 < beta k (criticalOverlap k) :=
    mul_pos (pow_pos hq.1 _) (sub_pos.mpr hq.2)
  apply (sq_lt_sq₀ (lambdaS_pos k hk).le (lambdaC_pos k hk).le).mp
  rw [lambdaS_sq k hk, lambdaC_sq_beta k hk]
  apply (div_lt_div_iff₀ (mul_pos hk0 hBt) (mul_pos hk0 hBq)).mpr
  simpa only [one_mul] using mul_lt_mul_of_pos_left hbelow hk0

/-- Above the spinodal threshold the actual stable stationary set is a singleton. -/
theorem existsUnique_stableStationaryPoint (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) : ∃! q : ℝ, Scalar.StableStationaryPoint k lam q := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 : 0 < lam := (lambdaS_pos k hk).trans hlam
  have ht := turningPoint_mem_Ioo k hk
  have hBt : 0 < beta k (turningPoint k) :=
    mul_pos (pow_pos ht.1 _) (sub_pos.mpr ht.2)
  have hcoeff : 0 < (k : ℝ)*lam^2 := mul_pos hk0 (sq_pos_of_pos hlam0)
  have htarget : 0 < 1/((k : ℝ)*lam^2) := one_div_pos.mpr hcoeff
  have hsq := (sq_lt_sq₀ (lambdaS_pos k hk).le hlam0.le).mpr hlam
  rw [lambdaS_sq k hk] at hsq
  have hbelow : 1/((k : ℝ)*lam^2) < beta k (turningPoint k) := by
    apply (div_lt_iff₀ hcoeff).mpr
    have hh := (div_lt_iff₀ (mul_pos hk0 hBt)).mp hsq
    nlinarith
  have hc : ContinuousOn (beta k) (Icc (turningPoint k) 1) := by
    unfold beta
    fun_prop
  obtain ⟨q, hq, heq⟩ := intermediate_value_Icc' ht.2.le hc
    ⟨by simpa only [beta, one_pow, sub_self, mul_zero] using htarget.le, hbelow.le⟩
  have hqlo : turningPoint k < q := by
    by_contra hn
    have hqeq : q = turningPoint k := le_antisymm (le_of_not_gt hn) hq.1
    rw [hqeq] at heq
    linarith
  have hqhi : q < 1 := by
    by_contra hn
    have hqeq : q = 1 := le_antisymm hq.2 (le_of_not_gt hn)
    rw [hqeq] at heq
    simp only [beta, one_pow, sub_self, mul_zero] at heq
    linarith
  have hstable : Scalar.StableStationaryPoint k lam q := by
    refine ⟨⟨hqlo, hqhi⟩, ?_⟩
    have heq' : ((k : ℝ)*lam^2)*beta k q = 1 := by
      rw [heq]
      exact mul_one_div_cancel hcoeff.ne'
    simpa only [beta, mul_assoc] using heq'
  exact ⟨q, hstable, fun r hr => stableStationaryPoint_unique k hk lam hr hstable⟩

/-- The frozen supremum-selected qS has exactly the intended stable-root meaning. -/
theorem qS_spec (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : Scalar.lambdaS k < lam) :
    Scalar.StableStationaryPoint k lam (Scalar.qS k lam) ∧
      ∀ q : ℝ, Scalar.StableStationaryPoint k lam q → q = Scalar.qS k lam := by
  obtain ⟨q, hq, huniq⟩ := existsUnique_stableStationaryPoint k hk hlam
  have hset : {r : ℝ | Scalar.StableStationaryPoint k lam r} = {q} := by
    ext r
    constructor
    · intro hr
      exact mem_singleton_iff.mpr (huniq r hr)
    · intro hr
      have heq : r = q := mem_singleton_iff.mp hr
      change Scalar.StableStationaryPoint k lam r
      simpa only [heq] using hq
  have hs : Scalar.qS k lam = q := by unfold Scalar.qS; rw [hset]; simp
  rw [hs]
  exact ⟨hq, fun r hr => huniq r hr⟩

end
end TensorPCA.ScalarStationaryProofs
