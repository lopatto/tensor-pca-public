-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.RSVariationalProof
public import TensorPCA.VariationalProofs
public import TensorPCA.ScalarThresholdProofs
public import Mathlib.Analysis.Convex.Slope

/-! Elementary certificates for the pure-model variational minimum.  These
arguments concern the profile infimum and assume no physical limit. -/
@[expose] public section
namespace TensorPCA.PureVariationalProofs
open Set MeasureTheory
noncomputable section

/-- The affine line through two values of a real function. -/
def chord (p : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  p a + (p b-p a)/(b-a)*(t-a)

theorem chord_le_of_mem {p : ℝ → ℝ}
    (hp : ConcaveOn ℝ (Icc (0 : ℝ) 1) p)
    {a b t : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (ht : t ∈ Icc a b) : chord p a b t ≤ p t := by
  have hba : 0 < b-a := sub_pos.mpr hab
  have hA : 0 ≤ (b-t)/(b-a) := div_nonneg (sub_nonneg.mpr ht.2) hba.le
  have hB : 0 ≤ (t-a)/(b-a) := div_nonneg (sub_nonneg.mpr ht.1) hba.le
  have hsum : (b-t)/(b-a)+(t-a)/(b-a) = 1 := by field_simp; ring
  have htEq : (b-t)/(b-a)*a+(t-a)/(b-a)*b = t := by field_simp; ring
  have H := hp.2 ha hb hA hB hsum
  simp only [smul_eq_mul, htEq] at H
  have hline : (b-t)/(b-a)*p a+(t-a)/(b-a)*p b = chord p a b t := by
    unfold chord
    field_simp
    ring
  rwa [hline] at H

theorem le_chord_of_le_left {p : ℝ → ℝ}
    (hp : ConcaveOn ℝ (Icc (0 : ℝ) 1) p)
    {a b t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hta : t ≤ a) : p t ≤ chord p a b t := by
  rcases eq_or_lt_of_le hta with rfl | hta
  · simp [chord]
  have H := hp.slope_anti_adjacent ht hb hta hab
  have h := (div_le_div_iff₀ (sub_pos.mpr hab) (sub_pos.mpr hta)).mp H
  have hba : 0 < b-a := sub_pos.mpr hab
  have hline : chord p a b t = ((b-a)*p a+(p b-p a)*(t-a))/(b-a) := by
    unfold chord
    field_simp
  rw [hline]
  exact (le_div_iff₀ hba).mpr (by nlinarith)

theorem le_chord_of_right_le {p : ℝ → ℝ}
    (hp : ConcaveOn ℝ (Icc (0 : ℝ) 1) p)
    {a b t : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hbt : b ≤ t) : p t ≤ chord p a b t := by
  rcases eq_or_lt_of_le hbt with rfl | hbt
  · simp [chord, ne_of_gt (sub_pos.mpr hab)]
  have H := hp.slope_anti_adjacent ha ht hab hbt
  have h := (div_le_div_iff₀ (sub_pos.mpr hbt) (sub_pos.mpr hab)).mp H
  have hba : 0 < b-a := sub_pos.mpr hab
  have hline : chord p a b t = ((b-a)*p a+(p b-p a)*(t-a))/(b-a) := by
    unfold chord
    field_simp
  rw [hline]
  exact (le_div_iff₀ hba).mpr (by nlinarith)

/-- A continuous signed weight with the negative-positive-negative pattern and
vanishing affine moments has nonnegative pairing with every concave profile.
The comparison uses a secant line, so no derivative of the profile is needed. -/
theorem integral_mul_concave_nonneg {w p : ℝ → ℝ}
    (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hp : ContinuousOn p (Icc (0 : ℝ) 1))
    (hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) p)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b)
    (hneg : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ a ∨ b ≤ t → w t ≤ 0)
    (hpos : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hmass : (∫ t in (0 : ℝ)..1, w t) = 0)
    (hfirst : (∫ t in (0 : ℝ)..1, t*w t) = 0) :
    0 ≤ ∫ t in (0 : ℝ)..1, w t*p t := by
  have hc : Continuous (chord p a b) := by unfold chord; fun_prop
  have hcint : IntervalIntegrable (fun t ↦ w t*chord p a b t) volume 0 1 :=
    (hw.mul hc.continuousOn).intervalIntegrable_of_Icc zero_le_one
  have hpint : IntervalIntegrable (fun t ↦ w t*p t) volume 0 1 :=
    (hw.mul hp).intervalIntegrable_of_Icc zero_le_one
  have hline : (∫ t in (0 : ℝ)..1, w t*chord p a b t) = 0 := by
    have heq : (fun t ↦ w t*chord p a b t) =
        (fun t ↦ (p a-(p b-p a)/(b-a)*a)*w t +
          ((p b-p a)/(b-a))*(t*w t)) := by
      funext t
      unfold chord
      ring
    have htw : ContinuousOn (fun t ↦ t*w t) (Icc (0 : ℝ) 1) :=
      continuousOn_id.mul hw
    rw [heq, intervalIntegral.integral_add
      (f := fun t ↦ (p a-(p b-p a)/(b-a)*a)*w t)
      (g := fun t ↦ ((p b-p a)/(b-a))*(t*w t))
      ((continuousOn_const.mul hw).intervalIntegrable_of_Icc zero_le_one)
      ((continuousOn_const.mul htw).intervalIntegrable_of_Icc zero_le_one),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hmass, hfirst]
    ring
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t*(p t-chord p a b t) := by
    intro t ht
    by_cases hleft : t ≤ a
    · exact mul_nonneg_of_nonpos_of_nonpos (hneg t ht (Or.inl hleft))
        (sub_nonpos.mpr (le_chord_of_le_left hconc ht hb hab hleft))
    by_cases hright : b ≤ t
    · exact mul_nonneg_of_nonpos_of_nonpos (hneg t ht (Or.inr hright))
        (sub_nonpos.mpr (le_chord_of_right_le hconc ha ht hab hright))
    · have hmid : t ∈ Icc a b := ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩
      exact mul_nonneg (hpos t hmid) (sub_nonneg.mpr (chord_le_of_mem hconc ha hb hab hmid))
  have H := intervalIntegral.integral_nonneg (μ := volume) zero_le_one hpoint
  simp_rw [mul_sub] at H
  rw [intervalIntegral.integral_sub hpint hcint, hline, sub_zero] at H
  exact H


/-- The pointwise supporting-line inequality for the reciprocal. -/
theorem reciprocal_tangent {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    2/s-p/s^2 ≤ 1/p := by
  have h : 0 ≤ (s-p)^2/(p*s^2) :=
    div_nonneg (sq_nonneg _) (mul_nonneg hp.le (sq_nonneg _))
  have hid : 1/p-(2/s-p/s^2) = (s-p)^2/(p*s^2) := by
    field_simp
    ring
  linarith

/-- A nonnegative first variation at a positive comparison profile gives the
ordinary global functional inequality, by the reciprocal support inequality. -/
theorem integral_minimal_of_dual {w r p : ℝ → ℝ}
    (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hr : ContinuousOn r (Icc (0 : ℝ) 1))
    (hp : ContinuousOn p (Icc (0 : ℝ) 1))
    (hrpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < r t)
    (hppos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < p t)
    (hdual : 0 ≤ ∫ t in (0 : ℝ)..1, (w t-1/(r t)^2)*(p t-r t)) :
    (∫ t in (0 : ℝ)..1, w t*r t+1/r t) ≤
      ∫ t in (0 : ℝ)..1, w t*p t+1/p t := by
  have hrinv : ContinuousOn (fun t ↦ 1/r t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hr (fun t ht ↦ (hrpos t ht).ne')
  have hpinv : ContinuousOn (fun t ↦ 1/p t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp (fun t ht ↦ (hppos t ht).ne')
  have hv : ContinuousOn (fun t ↦ w t-1/(r t)^2) (Icc (0 : ℝ) 1) :=
    hw.sub (continuousOn_const.div (hr.pow 2) (fun t ht ↦ pow_ne_zero _ (hrpos t ht).ne'))
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      w t*r t+1/r t+(w t-1/(r t)^2)*(p t-r t) ≤ w t*p t+1/p t := by
    intro t ht
    have H := reciprocal_tangent (hrpos t ht) (hppos t ht)
    have hid : w t*r t+1/r t+(w t-1/(r t)^2)*(p t-r t) =
        w t*p t+(2/r t-p t/(r t)^2) := by
      field_simp [(hrpos t ht).ne']
      ring
    rw [hid]
    linarith
  have H := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (f := fun t ↦ w t*r t+1/r t+(w t-1/(r t)^2)*(p t-r t))
    (g := fun t ↦ w t*p t+1/p t)
    ((((hw.mul hr).add hrinv).add (hv.mul (hp.sub hr))).intervalIntegrable_of_Icc zero_le_one)
    (((hw.mul hp).add hpinv).intervalIntegrable_of_Icc zero_le_one) hpoint
  rw [intervalIntegral.integral_add
    (f := fun t ↦ w t*r t+1/r t)
    (g := fun t ↦ (w t-1/(r t)^2)*(p t-r t))
    (((hw.mul hr).add hrinv).intervalIntegrable_of_Icc zero_le_one)
    ((hv.mul (hp.sub hr)).intervalIntegrable_of_Icc zero_le_one)] at H
  linarith

/-- The affine profile is globally minimal if its dual weight has the
two-crossing pattern and vanishing zeroth and first moments. -/
theorem affine_integral_minimal_of_certificate {w : ℝ → ℝ} {c d a b : ℝ}
    (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hrpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < c+d*t)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hneg : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ a ∨ b ≤ t → w t-1/(c+d*t)^2 ≤ 0)
    (hpos : ∀ t ∈ Icc a b, 0 ≤ w t-1/(c+d*t)^2)
    (hmass : (∫ t in (0 : ℝ)..1, w t-1/(c+d*t)^2) = 0)
    (hfirst : (∫ t in (0 : ℝ)..1, t*(w t-1/(c+d*t)^2)) = 0)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    (∫ t in (0 : ℝ)..1, w t*(c+d*t)+1/(c+d*t)) ≤
      ∫ t in (0 : ℝ)..1, w t*p t+1/p t := by
  have hr : ContinuousOn (fun t : ℝ ↦ c+d*t) (Icc (0 : ℝ) 1) := by fun_prop
  have hv : ContinuousOn (fun t ↦ w t-1/(c+d*t)^2) (Icc (0 : ℝ) 1) :=
    hw.sub (continuousOn_const.div (hr.pow 2) (fun t ht ↦ pow_ne_zero _ (hrpos t ht).ne'))
  apply integral_minimal_of_dual hw hr hp.1 hrpos hp.2.2.2
  have H := integral_mul_concave_nonneg hv hp.1 hp.2.2.1 ha hb hab hneg hpos hmass hfirst
  have hzero : (∫ t in (0 : ℝ)..1, (w t-1/(c+d*t)^2)*(c+d*t)) = 0 := by
    have heq : (fun t ↦ (w t-1/(c+d*t)^2)*(c+d*t)) =
        (fun t ↦ c*(w t-1/(c+d*t)^2)+d*(t*(w t-1/(c+d*t)^2))) := by
      funext t
      ring
    have htv := continuousOn_id.mul hv
    rw [heq, intervalIntegral.integral_add
      (f := fun t ↦ c*(w t-1/(c+d*t)^2))
      (g := fun t ↦ d*(t*(w t-1/(c+d*t)^2)))
      ((continuousOn_const.mul hv).intervalIntegrable_of_Icc zero_le_one)
      ((continuousOn_const.mul htv).intervalIntegrable_of_Icc zero_le_one),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hmass, hfirst]
    ring
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
    (f := fun t ↦ (w t-1/(c+d*t)^2)*p t)
    (g := fun t ↦ (w t-1/(c+d*t)^2)*(c+d*t))
    ((hv.mul hp.1).intervalIntegrable_of_Icc zero_le_one)
    ((hv.mul hr).intervalIntegrable_of_Icc zero_le_one), hzero, sub_zero]
  exact H


/-- A positive affine decreasing profile, parameterized by its terminal value. -/
def affineProfile (c a t : ℝ) : ℝ := c+a*(1-t)

theorem affineProfile_pos {c a t : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < affineProfile c a t := by
  unfold affineProfile
  have := mul_nonneg ha (sub_nonneg.mpr ht.2)
  linarith

theorem hasDerivAt_affineProfile (c a t : ℝ) :
    HasDerivAt (affineProfile c a) (-a) t := by
  convert! (((hasDerivAt_id t).const_sub (1 : ℝ)).const_mul a).const_add c using 1
  simp

theorem affineProfile_admissible {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    Scalar.AdmissibleProfile (affineProfile c a) := by
  have H := VariationalProofs.fourParameterProfile_admissible c a 0 0
    ⟨hc, ha, le_rfl, by simp⟩
  have heq : Scalar.fourParameterProfile c a 0 0 = affineProfile c a := by
    funext t
    simp [Scalar.fourParameterProfile, affineProfile]
  rw [heq] at H
  exact H

theorem integral_inv_affineProfile {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..1, 1/affineProfile c a t) = Real.log ((c+a)/c)/a := by
  have hr : ContinuousOn (affineProfile c a) (Icc (0 : ℝ) 1) := by unfold affineProfile; fun_prop
  have hinv : ContinuousOn (fun t ↦ 1/affineProfile c a t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hr (fun t ht ↦ (affineProfile_pos hc ha.le ht).ne')
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t ↦ -Real.log (affineProfile c a t)/a)
        (1/affineProfile c a t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hp := affineProfile_pos hc ha.le ht
    convert ((hasDerivAt_affineProfile c a t).log hp.ne').neg.div_const a using 1
    field_simp [ha.ne', hp.ne']
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hinv.intervalIntegrable_of_Icc zero_le_one)
  rw [H]
  simp only [affineProfile, sub_self, mul_zero, add_zero, sub_zero, mul_one]
  rw [Real.log_div (by positivity : c+a ≠ 0) hc.ne']
  ring

theorem integral_inv_sq_affineProfile {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..1, 1/(affineProfile c a t)^2) = 1/(c*(c+a)) := by
  have hr : ContinuousOn (affineProfile c a) (Icc (0 : ℝ) 1) := by unfold affineProfile; fun_prop
  have hinv : ContinuousOn (fun t ↦ 1/(affineProfile c a t)^2) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (hr.pow 2)
      (fun t ht ↦ pow_ne_zero _ (affineProfile_pos hc ha.le ht).ne')
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t ↦ (1/affineProfile c a t)/a)
        (1/(affineProfile c a t)^2) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hp := affineProfile_pos hc ha.le ht
    convert ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_affineProfile c a t) hp.ne').div_const a using 1
    field_simp [ha.ne', hp.ne']
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hinv.intervalIntegrable_of_Icc zero_le_one)
  rw [H]
  simp only [affineProfile, sub_self, mul_zero, add_zero, sub_zero, mul_one]
  field_simp [hc.ne', ha.ne', (show c+a ≠ 0 by positivity)]
  ring

theorem integral_mul_inv_sq_affineProfile {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..1, t/(affineProfile c a t)^2) =
      1/(a*c)-Real.log ((c+a)/c)/a^2 := by
  have hr : ContinuousOn (affineProfile c a) (Icc (0 : ℝ) 1) := by unfold affineProfile; fun_prop
  have hneq : ∀ t ∈ Icc (0 : ℝ) 1, affineProfile c a t ≠ 0 :=
    fun t ht ↦ (affineProfile_pos hc ha.le ht).ne'
  have hinv : ContinuousOn (fun t ↦ 1/affineProfile c a t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hr hneq
  have hinv2 : ContinuousOn (fun t ↦ 1/(affineProfile c a t)^2) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (hr.pow 2) (fun t ht ↦ pow_ne_zero _ (hneq t ht))
  have heq : ∀ t ∈ Icc (0 : ℝ) 1,
      t/(affineProfile c a t)^2 =
        ((c+a)/a)*(1/(affineProfile c a t)^2)-(1/a)*(1/affineProfile c a t) := by
    intro t ht
    field_simp [ha.ne', hneq t ht]
    unfold affineProfile
    ring
  rw [intervalIntegral.integral_congr (fun t ht ↦ heq t (by simpa using ht)),
    intervalIntegral.integral_sub
      (f := fun t ↦ ((c+a)/a)*(1/(affineProfile c a t)^2))
      (g := fun t ↦ (1/a)*(1/affineProfile c a t))
      ((continuousOn_const.mul hinv2).intervalIntegrable_of_Icc zero_le_one)
      ((continuousOn_const.mul hinv).intervalIntegrable_of_Icc zero_le_one),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_sq_affineProfile hc ha, integral_inv_affineProfile hc ha]
  field_simp [hc.ne', ha.ne', (show c+a ≠ 0 by positivity)]

theorem gs_eq_normalized (k : ℕ) (hk : 3 ≤ k) :
    Scalar.gs k = ((k : ℝ)+Scalar.zK k)/Real.sqrt ((k : ℝ)*(1+Scalar.zK k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz0 : 0 < 1+Scalar.zK k := by linarith [(ScalarThresholdProofs.zK_spec k hk).1]
  unfold Scalar.gs
  rw [Real.sqrt_mul hk0.le]
  field_simp [hk0.ne', (Real.sqrt_pos.mpr hk0).ne', (Real.sqrt_pos.mpr hz0).ne']
  nlinarith [Real.sq_sqrt hk0.le]


def pureWeight (k : ℕ) (t : ℝ) : ℝ := (k : ℝ)*((k : ℝ)-1)*t^(k-2)

theorem pureWeight_moments (k : ℕ) (hk : 3 ≤ k) :
    (∫ t in (0 : ℝ)..1, pureWeight k t) = k ∧
    (∫ t in (0 : ℝ)..1, t*pureWeight k t) = (k : ℝ)-1 := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR1 : (k : ℝ)-1 ≠ 0 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hN : k-2+1 = k-1 := by omega
  constructor
  · unfold pureWeight
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, hN, zero_pow (show k-1 ≠ 0 by omega), sub_zero,
      Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_ofNat]
    rw [show (k : ℝ)-2+1 = (k : ℝ)-1 by ring]
    field_simp
  · have heq : (fun t : ℝ ↦ t*pureWeight k t) =
        (fun t ↦ ((k : ℝ)*((k : ℝ)-1))*t^(k-1)) := by
      funext t
      unfold pureWeight
      rw [← hN, pow_succ]
      ring
    rw [heq, intervalIntegral.integral_const_mul, integral_pow]
    have hN2 : k-1+1 = k := by omega
    simp only [hN2, one_pow, zero_pow (Nat.ne_of_gt (show 0 < k by omega)), sub_zero,
      Nat.cast_sub hk1, Nat.cast_one]
    rw [sub_add_cancel]
    field_simp

def pureC (k : ℕ) : ℝ := 1/Real.sqrt ((k : ℝ)*(1+Scalar.zK k))
def pureA (k : ℕ) : ℝ := Scalar.zK k*pureC k

theorem pureC_pos (k : ℕ) (hk : 3 ≤ k) : 0 < pureC k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  unfold pureC
  positivity

theorem pureA_pos (k : ℕ) (hk : 3 ≤ k) : 0 < pureA k :=
  mul_pos (ScalarThresholdProofs.zK_spec k hk).1 (pureC_pos k hk)

theorem pureC_sq (k : ℕ) (hk : 3 ≤ k) :
    (pureC k)^2 = 1/((k : ℝ)*(1+Scalar.zK k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  unfold pureC
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

theorem pureProfile_reciprocal_moments (k : ℕ) (hk : 3 ≤ k) :
    (∫ t in (0 : ℝ)..1, 1/(affineProfile (pureC k) (pureA k) t)^2) = (k : ℝ) ∧
    (∫ t in (0 : ℝ)..1, t/(affineProfile (pureC k) (pureA k) t)^2) = (k : ℝ)-1 ∧
    (∫ t in (0 : ℝ)..1, 1/affineProfile (pureC k) (pureA k) t) =
      ((k : ℝ)+Scalar.zK k)*pureC k := by
  have hc := pureC_pos k hk
  have ha := pureA_pos k hk
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz1 : 0 < 1+Scalar.zK k := by linarith
  have hratio : (pureC k+pureA k)/pureC k = 1+Scalar.zK k := by
    unfold pureA
    field_simp
  have hprod : pureA k*pureC k = Scalar.zK k*(pureC k)^2 := by unfold pureA; ring
  have hapow : (pureA k)^2 = (Scalar.zK k)^2*(pureC k)^2 := by unfold pureA; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_inv_sq_affineProfile hc ha]
    apply (div_eq_iff (mul_ne_zero hc.ne' (show pureC k+pureA k ≠ 0 by positivity))).mpr
    have HH : (k : ℝ)*(1+Scalar.zK k)*(pureC k)^2 = 1 := by
      rw [pureC_sq k hk]
      field_simp
    unfold pureA
    nlinarith
  · rw [integral_mul_inv_sq_affineProfile hc ha, hratio, hprod, hapow,
      pureC_sq k hk, ScalarThresholdProofs.log_one_add_zK k hk]
    field_simp
    ring
  · rw [integral_inv_affineProfile hc ha, hratio, ScalarThresholdProofs.log_one_add_zK k hk]
    apply (div_eq_iff ha.ne').mpr
    rw [show ((k : ℝ)+Scalar.zK k)*pureC k*pureA k =
      ((k : ℝ)+Scalar.zK k)*Scalar.zK k*(pureC k)^2 by unfold pureA; ring, pureC_sq k hk]
    ring


def pureDualWeight (k : ℕ) (t : ℝ) : ℝ :=
  pureWeight k t-1/(affineProfile (pureC k) (pureA k) t)^2

theorem pureDualWeight_continuousOn (k : ℕ) (hk : 3 ≤ k) :
    ContinuousOn (pureDualWeight k) (Icc (0 : ℝ) 1) := by
  have hw : ContinuousOn (pureWeight k) (Icc (0 : ℝ) 1) := by unfold pureWeight; fun_prop
  have hr : ContinuousOn (affineProfile (pureC k) (pureA k)) (Icc (0 : ℝ) 1) := by
    unfold affineProfile
    fun_prop
  exact hw.sub (continuousOn_const.div (hr.pow 2)
    (fun t ht ↦ pow_ne_zero _ (affineProfile_pos (pureC_pos k hk) (pureA_pos k hk).le ht).ne'))

theorem pureDualWeight_moments (k : ℕ) (hk : 3 ≤ k) :
    (∫ t in (0 : ℝ)..1, pureDualWeight k t) = 0 ∧
    (∫ t in (0 : ℝ)..1, t*pureDualWeight k t) = 0 := by
  have hw : ContinuousOn (pureWeight k) (Icc (0 : ℝ) 1) := by unfold pureWeight; fun_prop
  have hr : ContinuousOn (affineProfile (pureC k) (pureA k)) (Icc (0 : ℝ) 1) := by
    unfold affineProfile
    fun_prop
  have hi : ContinuousOn (fun t ↦ 1/(affineProfile (pureC k) (pureA k) t)^2)
      (Icc (0 : ℝ) 1) := continuousOn_const.div (hr.pow 2)
    (fun t ht ↦ pow_ne_zero _ (affineProfile_pos (pureC_pos k hk) (pureA_pos k hk).le ht).ne')
  obtain ⟨hwm, hwt⟩ := pureWeight_moments k hk
  obtain ⟨him, hit, _⟩ := pureProfile_reciprocal_moments k hk
  constructor
  · unfold pureDualWeight
    rw [intervalIntegral.integral_sub (f := pureWeight k)
      (g := fun t ↦ 1/(affineProfile (pureC k) (pureA k) t)^2)
      (hw.intervalIntegrable_of_Icc zero_le_one) (hi.intervalIntegrable_of_Icc zero_le_one),
      hwm, him, sub_self]
  · have heq : (fun t ↦ t*pureDualWeight k t) =
        (fun t ↦ t*pureWeight k t-t/(affineProfile (pureC k) (pureA k) t)^2) := by
      funext t
      unfold pureDualWeight
      ring
    rw [heq, intervalIntegral.integral_sub
      (f := fun t ↦ t*pureWeight k t)
      (g := fun t ↦ t/(affineProfile (pureC k) (pureA k) t)^2)
      ((continuousOn_id.mul hw).intervalIntegrable_of_Icc zero_le_one)
      ((continuousOn_id.div (hr.pow 2)
        (fun t ht ↦ pow_ne_zero _ (affineProfile_pos (pureC_pos k hk) (pureA_pos k hk).le ht).ne')).intervalIntegrable_of_Icc zero_le_one),
      hwt, hit, sub_self]

theorem pureProfile_integral_value (k : ℕ) (hk : 3 ≤ k) :
    (∫ t in (0 : ℝ)..1,
      pureWeight k t*affineProfile (pureC k) (pureA k) t+
        1/affineProfile (pureC k) (pureA k) t) = 2*Scalar.gs k := by
  have hw : ContinuousOn (pureWeight k) (Icc (0 : ℝ) 1) := by unfold pureWeight; fun_prop
  have hr : ContinuousOn (affineProfile (pureC k) (pureA k)) (Icc (0 : ℝ) 1) := by
    unfold affineProfile
    fun_prop
  have hi : ContinuousOn (fun t ↦ 1/affineProfile (pureC k) (pureA k) t)
      (Icc (0 : ℝ) 1) := continuousOn_const.div hr
    (fun t ht ↦ (affineProfile_pos (pureC_pos k hk) (pureA_pos k hk).le ht).ne')
  have heq : (fun t ↦ pureWeight k t*affineProfile (pureC k) (pureA k) t) =
      (fun t ↦ (pureC k+pureA k)*pureWeight k t-pureA k*(t*pureWeight k t)) := by
    funext t
    unfold affineProfile
    ring
  rw [intervalIntegral.integral_add
    (f := fun t ↦ pureWeight k t*affineProfile (pureC k) (pureA k) t)
    (g := fun t ↦ 1/affineProfile (pureC k) (pureA k) t)
    ((hw.mul hr).intervalIntegrable_of_Icc zero_le_one)
    (hi.intervalIntegrable_of_Icc zero_le_one), heq,
    intervalIntegral.integral_sub
      (f := fun t ↦ (pureC k+pureA k)*pureWeight k t)
      (g := fun t ↦ pureA k*(t*pureWeight k t))
      ((continuousOn_const.mul hw).intervalIntegrable_of_Icc zero_le_one)
      ((continuousOn_const.mul (continuousOn_id.mul hw)).intervalIntegrable_of_Icc zero_le_one),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    (pureWeight_moments k hk).1, (pureWeight_moments k hk).2,
    (pureProfile_reciprocal_moments k hk).2.2, gs_eq_normalized k hk]
  unfold pureA pureC
  ring


/-- A continuous unimodal function crossing a level below its peak and above
both endpoint values has the required two-crossing sign pattern. -/
theorem two_crossings_of_unimodal {g : ℝ → ℝ} {d K : ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hm : MonotoneOn g (Icc (0 : ℝ) d)) (ha : AntitoneOn g (Icc d 1))
    (h0 : g 0 < K) (h1 : g 1 < K) (hpeak : K < g d) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1, a < b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t ≤ a ∨ b ≤ t → g t ≤ K) ∧
      (∀ t ∈ Icc a b, K ≤ g t) := by
  obtain ⟨a, hat, hva⟩ := intermediate_value_Icc hd.1.le
    (hg.mono (by intro t ht; exact ⟨ht.1, ht.2.trans hd.2.le⟩)) ⟨h0.le, hpeak.le⟩
  obtain ⟨b, hbt, hvb⟩ := intermediate_value_Icc' hd.2.le
    (hg.mono (by intro t ht; exact ⟨hd.1.le.trans ht.1, ht.2⟩)) ⟨h1.le, hpeak.le⟩
  have had : a < d := by
    by_contra h
    have hae : a = d := le_antisymm hat.2 (le_of_not_gt h)
    rw [hae] at hva
    linarith
  have hdb : d < b := by
    by_contra h
    have hbe : b = d := le_antisymm (le_of_not_gt h) hbt.1
    rw [hbe] at hvb
    linarith
  refine ⟨a, ⟨hat.1, hat.2.trans hd.2.le⟩, b,
    ⟨hd.1.le.trans hbt.1, hbt.2⟩, had.trans hdb, ?_, ?_⟩
  · intro t ht hout
    rcases hout with hta | hbt'
    · simpa only [hva] using hm ⟨ht.1, hta.trans hat.2⟩ hat hta
    · simpa only [hvb] using ha hbt ⟨hbt.1.trans hbt', ht.2⟩ hbt'
  · intro t ht
    by_cases htd : t ≤ d
    · simpa only [hva] using hm hat ⟨hat.1.trans ht.1, htd⟩ ht.1
    · simpa only [hvb] using ha ⟨(lt_of_not_ge htd).le, ht.2.trans hbt.2⟩ hbt ht.2

def pureSignPolynomial (k : ℕ) (c a t : ℝ) : ℝ := t^(k-2)*(affineProfile c a t)^2

theorem hasDerivAt_pureSignPolynomial (k : ℕ) (hk : 3 ≤ k) (c a t : ℝ) :
    HasDerivAt (pureSignPolynomial k c a)
      (t^(k-3)*affineProfile c a t*(((k : ℝ)-2)*(c+a)-(k : ℝ)*a*t)) t := by
  have hpow := hasDerivAt_pow (k-2) t
  have hsq := (hasDerivAt_affineProfile c a t).pow 2
  convert! hpow.mul hsq using 1
  have hN : k-2 = k-3+1 := by omega
  simp only [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_ofNat,
    show k-2-1 = k-3 by omega, Pi.pow_apply]
  rw [hN, pow_succ]
  unfold affineProfile
  ring

theorem pureSignPolynomial_unimodal (k : ℕ) (hk : 3 ≤ k)
    {c a d : ℝ} (hc : 0 < c) (ha : 0 < a) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hpeak : d = ((k : ℝ)-2)*(c+a)/((k : ℝ)*a)) :
    MonotoneOn (pureSignPolynomial k c a) (Icc (0 : ℝ) d) ∧
      AntitoneOn (pureSignPolynomial k c a) (Icc d 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcont : Continuous (pureSignPolynomial k c a) := by
    unfold pureSignPolynomial affineProfile
    fun_prop
  constructor
  · apply (strictMonoOn_of_deriv_pos (convex_Icc 0 d) hcont.continuousOn ?_).monotoneOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_pureSignPolynomial k hk c a t).deriv]
    have htp : 0 < affineProfile c a t := affineProfile_pos hc ha.le ⟨ht.1.le, ht.2.le.trans hd.2.le⟩
    have hlin : 0 < ((k : ℝ)-2)*(c+a)-(k : ℝ)*a*t := by
      have H : t < ((k : ℝ)-2)*(c+a)/((k : ℝ)*a) := ht.2.trans_eq hpeak
      have := (lt_div_iff₀ (mul_pos hk0 ha)).mp H
      nlinarith
    exact mul_pos (mul_pos (pow_pos ht.1 _) htp) hlin
  · apply (strictAntiOn_of_deriv_neg (convex_Icc d 1) hcont.continuousOn ?_).antitoneOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_pureSignPolynomial k hk c a t).deriv]
    have htp : 0 < affineProfile c a t := affineProfile_pos hc ha.le ⟨hd.1.le.trans ht.1.le, ht.2.le⟩
    have hlin : ((k : ℝ)-2)*(c+a)-(k : ℝ)*a*t < 0 := by
      have H : ((k : ℝ)-2)*(c+a)/((k : ℝ)*a) < t := hpeak.symm.trans_lt ht.1
      have := (div_lt_iff₀ (mul_pos hk0 ha)).mp H
      nlinarith
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos (hd.1.trans ht.1) _) htp) hlin


theorem pureDualWeight_sign (k : ℕ) (hk : 3 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (pureDualWeight k t ≤ 0 ↔
      pureSignPolynomial k (pureC k) (pureA k) t ≤ 1/((k : ℝ)*((k : ℝ)-1))) ∧
    (0 ≤ pureDualWeight k t ↔
      1/((k : ℝ)*((k : ℝ)-1)) ≤ pureSignPolynomial k (pureC k) (pureA k) t) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hu : 0 < (k : ℝ)*((k : ℝ)-1) := mul_pos (by linarith) (by linarith)
  have hr := affineProfile_pos (pureC_pos k hk) (pureA_pos k hk).le ht
  unfold pureDualWeight pureWeight pureSignPolynomial
  constructor
  · rw [sub_nonpos, le_div_iff₀ (sq_pos_of_pos hr), le_div_iff₀ hu]
    ring_nf
  · rw [sub_nonneg, div_le_iff₀ (sq_pos_of_pos hr), div_le_iff₀ hu]
    ring_nf

/-- The concrete pure dual weight has the two-crossing sign pattern. -/
theorem pureDualWeight_two_crossings (k : ℕ) (hk : 3 ≤ k) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1, a < b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t ≤ a ∨ b ≤ t → pureDualWeight k t ≤ 0) ∧
      (∀ t ∈ Icc a b, 0 ≤ pureDualWeight k t) := by
  have hc := pureC_pos k hk
  have ha := pureA_pos k hk
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  have hzlt := ScalarThresholdProofs.zK_gt_sub_two k hk
  let d : ℝ := ((k : ℝ)-2)*(pureC k+pureA k)/((k : ℝ)*pureA k)
  let K : ℝ := 1/((k : ℝ)*((k : ℝ)-1))
  let g := pureSignPolynomial k (pureC k) (pureA k)
  have hd : d ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (mul_pos (by linarith) (add_pos hc ha)) (mul_pos hk0 ha)
    · apply (div_lt_iff₀ (mul_pos hk0 ha)).mpr
      have H : ((k : ℝ)-2)*pureC k < pureA k := by
        exact mul_lt_mul_of_pos_right hzlt hc
      nlinarith
  have hmono := pureSignPolynomial_unimodal k hk hc ha hd rfl
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    change ContinuousOn (pureSignPolynomial k (pureC k) (pureA k)) (Icc (0 : ℝ) 1)
    unfold pureSignPolynomial affineProfile
    fun_prop
  have h0 : g 0 < K := by
    dsimp [g, pureSignPolynomial]
    rw [zero_pow (show k-2 ≠ 0 by omega), zero_mul]
    exact div_pos zero_lt_one (mul_pos hk0 (by linarith))
  have h1 : g 1 < K := by
    dsimp [g, pureSignPolynomial, affineProfile]
    simp only [one_pow, sub_self, mul_zero, add_zero, one_mul]
    rw [pureC_sq k hk]
    apply (div_lt_div_iff₀ (mul_pos hk0 (by linarith : 0 < 1+Scalar.zK k))
      (mul_pos hk0 (by linarith : 0 < (k : ℝ)-1))).mpr
    nlinarith
  have hw0 : pureDualWeight k 0 < 0 := by
    unfold pureDualWeight pureWeight
    rw [zero_pow (show k-2 ≠ 0 by omega), mul_zero, zero_sub]
    exact neg_neg_of_pos (div_pos zero_lt_one
      (sq_pos_of_pos (affineProfile_pos hc ha.le (by simp))))
  have hex : ∃ t ∈ Icc (0 : ℝ) 1, 0 < pureDualWeight k t := by
    by_contra h
    push Not at h
    have H := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      zero_lt_one (pureDualWeight_continuousOn k hk) continuousOn_const
      (fun t ht ↦ h t ⟨ht.1.le, ht.2⟩) ⟨0, by simp, hw0⟩
    rw [(pureDualWeight_moments k hk).1] at H
    simp at H
  obtain ⟨t, ht, htpos⟩ := hex
  have htK : K < g t := by
    by_contra h
    have H := (pureDualWeight_sign k hk ht).1.mpr (le_of_not_gt h)
    linarith
  have hpeak : K < g d := by
    apply htK.trans_le
    by_cases htd : t ≤ d
    · exact hmono.1 ⟨ht.1, htd⟩ ⟨hd.1.le, le_rfl⟩ htd
    · exact hmono.2 ⟨le_rfl, hd.2.le⟩ ⟨(lt_of_not_ge htd).le, ht.2⟩
        (lt_of_not_ge htd).le
  obtain ⟨a, hat, b, hbt, hab, hout, hin⟩ := two_crossings_of_unimodal hg hd hmono.1 hmono.2 h0 h1 hpeak
  refine ⟨a, hat, b, hbt, hab, ?_, ?_⟩
  · intro t ht hside
    exact (pureDualWeight_sign k hk ht).1.mpr (hout t ht hside)
  · intro t ht
    exact (pureDualWeight_sign k hk ⟨hat.1.trans ht.1, ht.2.trans hbt.2⟩).2.mpr (hin t ht)


theorem pureProfile_integral_minimal (k : ℕ) (hk : 3 ≤ k)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    (∫ t in (0 : ℝ)..1,
      pureWeight k t*affineProfile (pureC k) (pureA k) t+
        1/affineProfile (pureC k) (pureA k) t) ≤
      ∫ t in (0 : ℝ)..1, pureWeight k t*p t+1/p t := by
  obtain ⟨s, hs, t, ht, hst, hneg, hpos⟩ := pureDualWeight_two_crossings k hk
  have hw : ContinuousOn (pureWeight k) (Icc (0 : ℝ) 1) := by unfold pureWeight; fun_prop
  have hr (u : ℝ) : pureC k+pureA k+(-pureA k)*u = affineProfile (pureC k) (pureA k) u := by
    unfold affineProfile
    ring
  have H := affine_integral_minimal_of_certificate
    (w := pureWeight k) (c := pureC k+pureA k) (d := -pureA k) hw
    (by intro u hu; rw [hr]; exact affineProfile_pos (pureC_pos k hk) (pureA_pos k hk).le hu)
    hs ht hst
    (by intro u hu hside; rw [hr]; exact hneg u hu hside)
    (by intro u hu; rw [hr]; exact hpos u hu)
    (by simp_rw [hr]; exact (pureDualWeight_moments k hk).1)
    (by simp_rw [hr]; exact (pureDualWeight_moments k hk).2) hp
  simpa only [hr] using H

theorem parisiFunctional_xiSlice_zero (k : ℕ) (hk : 3 ≤ k) (p : ℝ → ℝ) :
    Scalar.parisiFunctional (Scalar.xiSlice k 0) 0 p =
      ∫ t in (0 : ℝ)..1, pureWeight k t*p t+1/p t := by
  have hxi2 : deriv (deriv (Scalar.xiSlice k 0)) = pureWeight k := by
    funext t
    rw [(VariationalProofs.hasDerivAt_deriv_xiSlice (show 1 ≤ k by omega) 0 t).deriv]
    simp [pureWeight]
  have hxi1 : deriv (Scalar.xiSlice k 0) 0 = 0 := by
    rw [VariationalProofs.deriv_xiSlice]
    simp [zero_pow (show k-1 ≠ 0 by omega)]
  unfold Scalar.parisiFunctional
  rw [hxi2, hxi1]
  simp

/-- The actual pure-model profile infimum is attained by the affine candidate. -/
theorem pureProfile_minimal (k : ℕ) (hk : 3 ≤ k) {p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p) :
    Scalar.parisiFunctional (Scalar.xiSlice k 0) 0 (affineProfile (pureC k) (pureA k)) ≤
      Scalar.parisiFunctional (Scalar.xiSlice k 0) 0 p := by
  rw [parisiFunctional_xiSlice_zero k hk, parisiFunctional_xiSlice_zero k hk]
  exact pureProfile_integral_minimal k hk hp

theorem pure_variationalValue_xiSlice_zero (k : ℕ) (hk : 3 ≤ k) :
    Scalar.variationalValue (Scalar.xiSlice k 0) 0 = Scalar.gs k := by
  have hvalue : Scalar.parisiFunctional (Scalar.xiSlice k 0) 0
      (affineProfile (pureC k) (pureA k)) = 2*Scalar.gs k := by
    rw [parisiFunctional_xiSlice_zero k hk, pureProfile_integral_value k hk]
  have hleast : IsLeast {v : ℝ | ∃ p : ℝ → ℝ,
      Scalar.AdmissibleProfile p ∧ v = Scalar.parisiFunctional (Scalar.xiSlice k 0) 0 p}
      (2*Scalar.gs k) := by
    constructor
    · exact ⟨_, affineProfile_admissible (pureC_pos k hk) (pureA_pos k hk).le, hvalue.symm⟩
    · intro v hv
      obtain ⟨p, hp, rfl⟩ := hv
      rw [← hvalue]
      exact pureProfile_minimal k hk hp
  unfold Scalar.variationalValue
  rw [hleast.csInf_eq]
  ring

/-- The pure zero-field variational value, proved without a physical Parisi
formula or any supplied minimizer assumption. -/
theorem pure_variationalValue (k : ℕ) (hk : 3 ≤ k) :
    Scalar.variationalValue (fun t : ℝ ↦ t^k) 0 = Scalar.gs k := by
  have hxi : Scalar.xiSlice k 0 = (fun t : ℝ ↦ t^k) := by
    funext t
    simp [Scalar.xiSlice, zero_pow (show 2*k ≠ 0 by omega)]
  rw [← hxi]
  exact pure_variationalValue_xiSlice_zero k hk


end
end TensorPCA.PureVariationalProofs
