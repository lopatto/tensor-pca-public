-- SPDX-License-Identifier: Apache-2.0
/-
The static-ratio proof block is adapted from
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/PureScalarStatic.lean
Original Apache-2.0 notice retained; see LICENSE. The general Thresholds import
is replaced by the explicit pure scalar ratio below. The bridges to the frozen
supremum definition of lambdaC are new proofs, with no changed central meaning.
-/
module
public import TensorPCA.ScalarThresholdProofs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace TensorPCA.ScalarStaticRatioProofs
noncomputable section
open Set Filter MeasureTheory ScalarThresholdProofs
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The exact pure-model ratio in the critical-threshold characterization. -/
def staticRatio (k : ℕ) (r : ℝ) : ℝ := (-r-Real.log (1-r))/r^k

/-- The static critical overlap associated with a scalar parameter. -/
def staticOverlap (z : ℝ) : ℝ := z/(1+z)

theorem staticOverlap_mem_Ioo {z : ℝ} (hz : 0 < z) :
    staticOverlap z ∈ Ioo (0 : ℝ) 1 := by
  unfold staticOverlap
  refine ⟨div_pos hz (by linarith), ?_⟩
  exact (div_lt_one (by linarith : 0 < 1+z)).mpr (by linarith)

/-- Exact scalar sign identity under the genuine change of variables
`z=r/(1-r)`. -/
theorem staticDerivativeNumerator_eq (p : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    r^2/(1-r)-(p : ℝ)*(-r-Real.log (1-r)) =
      r^2/(1-r)*(1-(p : ℝ)*upsilon (r/(1-r))) := by
  have hden : 1-r ≠ 0 := (sub_pos.mpr hr.2).ne'
  have hz : 0 < r/(1-r) := div_pos hr.1 (sub_pos.mpr hr.2)
  have hsum : 1+r/(1-r) = (1-r)⁻¹ := by field_simp [hden]; ring
  rw [upsilon_eq hz, hsum, Real.log_inv]
  field_simp [hden, hr.1.ne']
  ring

/-- Actual derivative of the ordinary pure-spin static ratio, with the
positive power factor and its scalar sign numerator explicitly separated. -/
theorem hasDerivAt_staticRatio_pure (p : ℕ) (hp : 1 ≤ p)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (staticRatio p)
      (r^(p-1)/(r^p)^2*(r^2/(1-r)-(p : ℝ)*(-r-Real.log (1-r)))) r := by
  have hden : 1-r ≠ 0 := (sub_pos.mpr hr.2).ne'
  have hpow : r^p = r^(p-1)*r := by
    rw [← pow_succ]
    congr 1
    omega
  have hlog := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).log hden
  have hnum := (hasDerivAt_id r).neg.sub hlog
  convert hnum.div (hasDerivAt_pow p r) (pow_ne_zero p hr.1.ne') using 1
  · ext x
    rfl
  · dsimp
    rw [hpow]
    field_simp [hden, hr.1.ne', pow_ne_zero (p-1) hr.1.ne']
    ring

theorem staticRatio_pure_continuousOn (p : ℕ) :
    ContinuousOn (staticRatio p) (Ioo (0 : ℝ) 1) := by
  apply ((continuous_id.neg).continuousOn.sub
    ((continuous_const.sub continuous_id).continuousOn.log (fun r hr =>
      (sub_pos.mpr hr.2).ne'))).div (continuous_pow p).continuousOn
  intro r hr
  exact pow_ne_zero p hr.1.ne'

/-- The actual static ratio strictly decreases before the unique scalar
root overlap and strictly increases after it. -/
theorem staticRatio_pure_strict_monotonicity (p : ℕ) (hp : 3 ≤ p)
    {z : ℝ} (hz : 0 < z) (hroot : upsilon z = 1/(p : ℝ)) :
    StrictAntiOn (staticRatio p) (Ioc (0 : ℝ) (staticOverlap z)) ∧
    StrictMonoOn (staticRatio p) (Ico (staticOverlap z) 1) := by
  have hq := staticOverlap_mem_Ioo hz
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpInv : (p : ℝ)*(1/(p : ℝ)) = 1 := by field_simp
  have hderivSign (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      deriv (staticRatio p) r =
        r^(p-1)/(r^p)^2*(r^2/(1-r)*(1-(p : ℝ)*upsilon (r/(1-r)))) := by
    rw [(hasDerivAt_staticRatio_pure p (by omega) hr).deriv, staticDerivativeNumerator_eq p hr]
  have hfactor (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      0 < r^(p-1)/(r^p)^2 ∧ 0 < r^2/(1-r) := by
    have hr0 := hr.1
    have hden := sub_pos.mpr hr.2
    constructor <;> positivity
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (staticOverlap z))
    · exact (staticRatio_pure_continuousOn p).mono (fun r hr => ⟨hr.1, hr.2.trans_lt hq.2⟩)
    · intro r hr
      have hr' : r ∈ Ioo (0 : ℝ) (staticOverlap z) := by simpa only [interior_Ioc] using hr
      have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr'.1, hr'.2.trans hq.2⟩
      have hzr : 0 < r/(1-r) := div_pos hr'.1 (sub_pos.mpr hr01.2)
      have hzrz : r/(1-r) < z := by
        apply (div_lt_iff₀ (sub_pos.mpr hr01.2)).mpr
        have h := (lt_div_iff₀ (by linarith : 0 < 1+z)).mp hr'.2
        nlinarith
      have hu := strictAntiOn_upsilon hzr.le hz.le hzrz
      rw [hroot] at hu
      have hneg : 1-(p : ℝ)*upsilon (r/(1-r)) < 0 := by
        have hm := mul_lt_mul_of_pos_left hu hpR
        rw [hpInv] at hm
        linarith
      rw [hderivSign r hr01]
      exact mul_neg_of_pos_of_neg (hfactor r hr01).1
        (mul_neg_of_pos_of_neg (hfactor r hr01).2 hneg)
  · apply strictMonoOn_of_deriv_pos (convex_Ico (staticOverlap z) 1)
    · exact (staticRatio_pure_continuousOn p).mono (fun r hr => ⟨hq.1.trans_le hr.1, hr.2⟩)
    · intro r hr
      have hr' : r ∈ Ioo (staticOverlap z) 1 := by simpa only [interior_Ico] using hr
      have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hq.1.trans hr'.1, hr'.2⟩
      have hzr : 0 < r/(1-r) := div_pos hr01.1 (sub_pos.mpr hr01.2)
      have hzzr : z < r/(1-r) := by
        apply (lt_div_iff₀ (sub_pos.mpr hr01.2)).mpr
        have h := (div_lt_iff₀ (by linarith : 0 < 1+z)).mp hr'.1
        nlinarith
      have hu := strictAntiOn_upsilon hz.le hzr.le hzzr
      rw [hroot] at hu
      have hpos : 0 < 1-(p : ℝ)*upsilon (r/(1-r)) := by
        have hm := mul_lt_mul_of_pos_left hu hpR
        rw [hpInv] at hm
        linarith
      rw [hderivSign r hr01]
      exact mul_pos (hfactor r hr01).1 (mul_pos (hfactor r hr01).2 hpos)

/-- The scalar root overlap is the unique global minimum of the actual
pure-spin static ratio on the full physical interval. -/
theorem staticRatio_pure_unique_minimum (p : ℕ) (hp : 3 ≤ p)
    {z : ℝ} (hz : 0 < z) (hroot : upsilon z = 1/(p : ℝ)) :
    ∀ r ∈ Ioo (0 : ℝ) 1,
      staticRatio p (staticOverlap z) ≤
        staticRatio p r ∧
      (staticRatio p (staticOverlap z) =
        staticRatio p r ↔ r = staticOverlap z) := by
  have hq := staticOverlap_mem_Ioo hz
  obtain ⟨ha, hm⟩ := staticRatio_pure_strict_monotonicity p hp hz hroot
  intro r hr
  rcases lt_trichotomy r (staticOverlap z) with hlt | heq | hgt
  · have h := ha ⟨hr.1, hlt.le⟩ ⟨hq.1, le_rfl⟩ hlt
    exact ⟨h.le, ⟨fun he => (h.ne he).elim, fun he => (hlt.ne he).elim⟩⟩
  · simp [heq]
  · have h := hm ⟨le_rfl, hq.2⟩ ⟨hgt.le, hr.2⟩ hgt
    exact ⟨h.le, ⟨fun he => (h.ne he).elim, fun he => (hgt.ne he.symm).elim⟩⟩

/-- Exact value of the genuine pure-spin static minimum, deduced from the
root equation and actual global minimum rather than assumed stationarity. -/
theorem staticRatio_pure_at_root (p : ℕ) (hp : 3 ≤ p)
    {z : ℝ} (hz : 0 < z) (hroot : upsilon z = 1/(p : ℝ)) :
    let q := staticOverlap z
    staticRatio p q =
      1/((p : ℝ)*q^(p-2)*(1-q)) := by
  let q := staticOverlap z
  have hq := staticOverlap_mem_Ioo hz
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hzchange : q/(1-q) = z := by
    dsimp [q, staticOverlap]
    field_simp [show 1+z ≠ 0 by linarith]
    ring
  have hD := staticDerivativeNumerator_eq p hq
  rw [hzchange, hroot, mul_one_div_cancel hpR.ne', sub_self, mul_zero] at hD
  have hnum : -q-Real.log (1-q) = q^2/((p : ℝ)*(1-q)) := by
    apply (eq_div_iff (mul_ne_zero hpR.ne' (sub_pos.mpr hq.2).ne')).mpr
    have hD' : q^2 = ((p : ℝ)*(-q-Real.log (1-q)))*(1-q) := by
      apply (div_eq_iff (sub_pos.mpr hq.2).ne').mp
      linarith
    nlinarith
  have hpow : q^p = q^(p-2)*q^2 := by
    rw [← pow_add]
    congr 1
    omega
  change (-q-Real.log (1-q))/q^p = 1/((p : ℝ)*q^(p-2)*(1-q))
  rw [hnum, hpow]
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1-q ≠ 0 := (sub_pos.mpr hq.2).ne'
  field_simp [hpR.ne', hq0, hq1, pow_ne_zero (p-2) hq0]

/-- The overlap determined by the already proved unique positive varphi root. -/
def criticalOverlap (k : ℕ) : ℝ := staticOverlap (Scalar.zK k)

theorem upsilon_zK (k : ℕ) (hk : 3 ≤ k) :
    upsilon (Scalar.zK k) = 1/(k : ℝ) := by
  have h := (zK_spec k hk).2.1
  rw [varphi_eq_upsilon_sub k (zK_spec k hk).1] at h
  exact sub_eq_zero.mp h

theorem criticalOverlap_mem_Ioo (k : ℕ) (hk : 3 ≤ k) :
    criticalOverlap k ∈ Ioo (0 : ℝ) 1 := staticOverlap_mem_Ioo (zK_spec k hk).1

theorem criticalRatio_unique_minimum (k : ℕ) (hk : 3 ≤ k) :
    ∀ r ∈ Ioo (0 : ℝ) 1, staticRatio k (criticalOverlap k) ≤ staticRatio k r ∧
      (staticRatio k (criticalOverlap k) = staticRatio k r ↔ r = criticalOverlap k) :=
  staticRatio_pure_unique_minimum k hk (zK_spec k hk).1 (upsilon_zK k hk)

theorem criticalRatio_value (k : ℕ) (hk : 3 ≤ k) :
    staticRatio k (criticalOverlap k) =
      1/((k : ℝ)*(criticalOverlap k)^(k-2)*(1-criticalOverlap k)) :=
  staticRatio_pure_at_root k hk (zK_spec k hk).1 (upsilon_zK k hk)

def criticalSquared (k : ℕ) : ℝ := staticRatio k (criticalOverlap k)

theorem criticalSquared_pos (k : ℕ) (hk : 3 ≤ k) : 0 < criticalSquared k := by
  unfold criticalSquared
  rw [criticalRatio_value k hk]
  have hq := criticalOverlap_mem_Ioo k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  exact one_div_pos.mpr (mul_pos (mul_pos hk0 (pow_pos hq.1 _)) (sub_pos.mpr hq.2))

theorem f_nonpos_iff_sq_le_ratio (k : ℕ) (lam : ℝ) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) : Scalar.f k lam q ≤ 0 ↔ lam^2 ≤ staticRatio k q := by
  unfold staticRatio
  rw [le_div_iff₀ (pow_pos hq.1 k)]
  unfold Scalar.f
  constructor <;> intro h <;> linarith

theorem f_nonpos_iff_le_critical (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ q ∈ Ico (0 : ℝ) 1, Scalar.f k lam q ≤ 0) ↔
      lam ≤ Real.sqrt (criticalSquared k) := by
  have hA := criticalSquared_pos k hk
  have hq := criticalOverlap_mem_Ioo k hk
  constructor
  · intro h
    apply (sq_le_sq₀ hlam (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hA.le]
    exact (f_nonpos_iff_sq_le_ratio k lam hq).mp (h _ ⟨hq.1.le, hq.2⟩)
  · intro h q hq01
    have hsq : lam^2 ≤ criticalSquared k := by
      have hh := (sq_le_sq₀ hlam (Real.sqrt_nonneg (criticalSquared k))).mpr h
      simpa only [Real.sq_sqrt hA.le] using hh
    by_cases hzero : q = 0
    · subst q
      simp [Scalar.f, show k ≠ 0 by omega]
    · have hqpos : 0 < q := lt_of_le_of_ne hq01.1 (Ne.symm hzero)
      apply (f_nonpos_iff_sq_le_ratio k lam ⟨hqpos, hq01.2⟩).mpr
      exact hsq.trans ((criticalRatio_unique_minimum k hk q ⟨hqpos, hq01.2⟩).1)

/-- The entire actual nonpositive-strength set is an ordinary closed interval. -/
theorem nonpositiveStrengths_eq_Icc (k : ℕ) (hk : 3 ≤ k) :
    {lam : ℝ | 0 ≤ lam ∧ ∀ q ∈ Ico (0 : ℝ) 1, Scalar.f k lam q ≤ 0} =
      Icc (0 : ℝ) (Real.sqrt (criticalSquared k)) := by
  ext lam
  change (0 ≤ lam ∧ ∀ q ∈ Ico (0 : ℝ) 1, Scalar.f k lam q ≤ 0) ↔
    0 ≤ lam ∧ lam ≤ Real.sqrt (criticalSquared k)
  constructor
  · rintro ⟨hlam, hf⟩
    exact ⟨hlam, (f_nonpos_iff_le_critical k hk hlam).mp hf⟩
  · rintro ⟨hlam, hle⟩
    exact ⟨hlam, (f_nonpos_iff_le_critical k hk hlam).mpr hle⟩

/-- Identifies the frozen supremum-selected lambdaC with the genuine minimum. -/
theorem lambdaC_eq_sqrt_criticalSquared (k : ℕ) (hk : 3 ≤ k) :
    Scalar.lambdaC k = Real.sqrt (criticalSquared k) := by
  unfold Scalar.lambdaC
  rw [nonpositiveStrengths_eq_Icc k hk]
  exact csSup_Icc (Real.sqrt_nonneg _)

theorem lambdaC_pos (k : ℕ) (hk : 3 ≤ k) : 0 < Scalar.lambdaC k := by
  rw [lambdaC_eq_sqrt_criticalSquared k hk]
  exact Real.sqrt_pos.mpr (criticalSquared_pos k hk)

theorem lambdaC_sq (k : ℕ) (hk : 3 ≤ k) : (Scalar.lambdaC k)^2 = criticalSquared k := by
  rw [lambdaC_eq_sqrt_criticalSquared k hk, Real.sq_sqrt (criticalSquared_pos k hk).le]

theorem nonpositiveStrengths_bddAbove (k : ℕ) (hk : 3 ≤ k) :
    BddAbove {lam : ℝ | 0 ≤ lam ∧ ∀ q ∈ Ico (0 : ℝ) 1, Scalar.f k lam q ≤ 0} := by
  rw [nonpositiveStrengths_eq_Icc k hk]
  exact ⟨Real.sqrt (criticalSquared k), fun _ h => h.2⟩

theorem lambdaC_sq_isLeast (k : ℕ) (hk : 3 ≤ k) :
    IsLeast (staticRatio k '' Ioo (0 : ℝ) 1) ((Scalar.lambdaC k)^2) := by
  rw [lambdaC_sq k hk]
  refine ⟨⟨criticalOverlap k, criticalOverlap_mem_Ioo k hk, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact (criticalRatio_unique_minimum k hk q hq).1

theorem f_neg_iff_sq_lt_ratio (k : ℕ) (lam : ℝ) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) : Scalar.f k lam q < 0 ↔ lam^2 < staticRatio k q := by
  unfold staticRatio
  rw [lt_div_iff₀ (pow_pos hq.1 k)]
  unfold Scalar.f
  constructor <;> intro h <;> linarith

theorem f_eq_zero_iff_sq_eq_ratio (k : ℕ) (lam : ℝ) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) : Scalar.f k lam q = 0 ↔ lam^2 = staticRatio k q := by
  unfold staticRatio
  rw [eq_div_iff (pow_pos hq.1 k).ne']
  unfold Scalar.f
  constructor <;> intro h <;> linarith

theorem f_neg_of_subcritical (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : 0 ≤ lam) (hbelow : lam < Scalar.lambdaC k) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) : Scalar.f k lam q < 0 := by
  have hsq := (sq_lt_sq₀ hlam (lambdaC_pos k hk).le).mpr hbelow
  rw [lambdaC_sq k hk] at hsq
  apply (f_neg_iff_sq_lt_ratio k lam hq).mpr
  exact hsq.trans_le (criticalRatio_unique_minimum k hk q hq).1

theorem f_nonpos_at_critical (k : ℕ) (hk : 3 ≤ k) :
    ∀ q ∈ Ico (0 : ℝ) 1, Scalar.f k (Scalar.lambdaC k) q ≤ 0 := by
  apply (f_nonpos_iff_le_critical k hk (lambdaC_pos k hk).le).mpr
  exact (lambdaC_eq_sqrt_criticalSquared k hk).le

theorem f_zero_at_criticalOverlap (k : ℕ) (hk : 3 ≤ k) :
    Scalar.f k (Scalar.lambdaC k) (criticalOverlap k) = 0 :=
  (f_eq_zero_iff_sq_eq_ratio k (Scalar.lambdaC k) (criticalOverlap_mem_Ioo k hk)).mpr
    (lambdaC_sq k hk)

/-- Exact critical maximizer set for f, using the genuinely minimized ratio. -/
theorem critical_scalarMaximizers (k : ℕ) (hk : 3 ≤ k) (q : ℝ) :
    Scalar.IsScalarMaximizer k (Scalar.lambdaC k) q ↔ q = 0 ∨ q = criticalOverlap k := by
  have hfzero : Scalar.f k (Scalar.lambdaC k) 0 = 0 := by
    simp [Scalar.f, show k ≠ 0 by omega]
  constructor
  · rintro ⟨hq, hmax⟩
    have hge : 0 ≤ Scalar.f k (Scalar.lambdaC k) q := by
      rw [← hfzero]
      exact hmax 0 (by constructor <;> norm_num)
    have hzero : Scalar.f k (Scalar.lambdaC k) q = 0 :=
      le_antisymm (f_nonpos_at_critical k hk q hq) hge
    by_cases hqzero : q = 0
    · exact Or.inl hqzero
    · apply Or.inr
      have hq' : q ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hqzero), hq.2⟩
      have heq := (f_eq_zero_iff_sq_eq_ratio k (Scalar.lambdaC k) hq').mp hzero
      rw [lambdaC_sq k hk] at heq
      exact ((criticalRatio_unique_minimum k hk q hq').2).mp heq
  · rintro (rfl | rfl)
    · refine ⟨by constructor <;> norm_num, ?_⟩
      intro r hr
      rw [hfzero]
      exact f_nonpos_at_critical k hk r hr
    · have hq := criticalOverlap_mem_Ioo k hk
      refine ⟨⟨hq.1.le, hq.2⟩, ?_⟩
      intro r hr
      rw [f_zero_at_criticalOverlap k hk]
      exact f_nonpos_at_critical k hk r hr

end
end TensorPCA.ScalarStaticRatioProofs
