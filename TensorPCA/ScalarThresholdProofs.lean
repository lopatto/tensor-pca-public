-- SPDX-License-Identifier: Apache-2.0
/-
Narrow attributed port of the integral scalar proof block from
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/PureScalarStatic.lean
Original source license: Apache-2.0, preserved by the SPDX notice above;
see the repository LICENSE. Only the canonical-Mathlib scalar integral block
is included, with the source namespace changed and the unrelated CSPureModels
import omitted. The bridges to the frozen TensorPCA.Scalar definitions are new.
-/
module

public import TensorPCA.Scalar
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
namespace TensorPCA.ScalarThresholdProofs
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The ordinary scalar integral appearing in the pure-spin stationarity
equations, with its continuous value at zero included. -/
def upsilon (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1-t)/(1+z*t)

theorem upsilon_integrand_continuousOn {z : ℝ} (hz : 0 ≤ z) :
    ContinuousOn (fun t : ℝ => (1-t)/(1+z*t)) (Icc (0 : ℝ) 1) := by
  apply (continuous_const.sub continuous_id).continuousOn.div
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  intro t ht
  change 1+z*t ≠ 0
  exact ne_of_gt (by have := mul_nonneg hz ht.1; linarith)

/-- Exact analytic evaluation of the ordinary scalar integral. -/
theorem upsilon_eq {z : ℝ} (hz : 0 < z) :
    upsilon z = ((1+z)*Real.log (1+z)-z)/z^2 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => ((1+z)*Real.log (1+z*t)-z*t)/z^2)
        ((1-t)/(1+z*t)) t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ht.1
    have hden : 1+z*t ≠ 0 := ne_of_gt (by have := mul_nonneg hz.le ht0; linarith)
    have hlin := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul z)
    have hlog := hlin.log hden
    convert ((hlog.const_mul (1+z)).sub ((hasDerivAt_id t).const_mul z)).div_const (z^2) using 1
    · ext s
      rfl
    · dsimp
      field_simp [hden, hz.ne']
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((upsilon_integrand_continuousOn hz.le).intervalIntegrable_of_Icc (by norm_num))
  simpa only [upsilon, mul_one, mul_zero, add_zero, Real.log_one, sub_zero, zero_div] using hi

/-- The endpoint value is the actual integral of `1-t`. -/
theorem upsilon_zero : upsilon 0 = (1/2 : ℝ) := by
  unfold upsilon
  simp only [zero_mul, add_zero, div_one]
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hconst hid]
  norm_num [integral_id]

/-- Genuine continuity on the whole nonnegative parameter interval,
obtained by integrating an actual globally continuous clamped kernel. -/
theorem continuousOn_upsilon : ContinuousOn upsilon (Ici (0 : ℝ)) := by
  let f : ℝ → ℝ → ℝ := fun z t => (1-t)/(1+max z 0*max t 0)
  have hf : Continuous f.uncurry := by
    apply (continuous_const.sub continuous_snd).div
      (continuous_const.add ((continuous_fst.max continuous_const).mul
        (continuous_snd.max continuous_const)))
    intro x
    change 1+max x.1 0*max x.2 0 ≠ 0
    exact ne_of_gt (by have := mul_nonneg (le_max_right x.1 0) (le_max_right x.2 0); linarith)
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  apply hc.continuousOn.congr
  intro z hz
  unfold upsilon
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp [f]
  rw [max_eq_left hz, max_eq_left ht.1]

/-- Strict monotonicity is proved by strict comparison of the actual
integrands, with a strict witness at the midpoint. -/
theorem strictAntiOn_upsilon : StrictAntiOn upsilon (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) (upsilon_integrand_continuousOn hy)
    (upsilon_integrand_continuousOn hx)
  · intro t ht
    have hdx : 0 < 1+x*t := by have := mul_nonneg hx ht.1.le; linarith
    have hdy : 0 < 1+y*t := by have := mul_nonneg hy ht.1.le; linarith
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr ht.2) hdx
      (by nlinarith [mul_nonneg (sub_pos.mpr hxy).le ht.1.le])
  · refine ⟨1/2, by norm_num, ?_⟩
    have hdx : 0 < 1+x*(1/2) := by linarith
    have hdy : 0 < 1+y*(1/2) := by linarith
    exact div_lt_div_of_pos_left (by norm_num) hdx (by nlinarith)

/-- The true scalar function tends to zero at infinity. -/
theorem tendsto_upsilon_atTop : Tendsto upsilon atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun z : ℝ => 1/z) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun z : ℝ => Real.log (1+z)/z) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    apply h.congr'
    filter_upwards with z
    simp only [pow_one, one_mul, Function.comp_def, id_eq]
    congr 1
    ring
  have hh : Tendsto (fun z : ℝ => (1+1/z)*(Real.log (1+z)/z)-1/z) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hi).mul hl |>.sub hi
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [upsilon_eq hz]
  field_simp [hz.ne']
  ring

/-- Each pure degree at least three has exactly one positive root of the
ordinary scalar stationarity equation `upsilon(z)=1/p`. -/
theorem existsUnique_upsilon_root (p : ℕ) (hp : 3 ≤ p) :
    ∃! z : ℝ, 0 < z ∧ upsilon z = 1/(p : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have htarget : 0 < 1/(p : ℝ) := by positivity
  have htargetHalf : 1/(p : ℝ) < (1/2 : ℝ) := by
    exact (div_lt_div_iff₀ (by positivity : (0 : ℝ) < p) (by norm_num)).mpr (by linarith)
  obtain ⟨z, hz0, hzlow⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (tendsto_upsilon_atTop.eventually (gt_mem_nhds htarget))).exists
  have hcont : ContinuousOn upsilon (Icc (0 : ℝ) z) :=
    continuousOn_upsilon.mono Icc_subset_Ici_self
  obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc' hz0.le hcont
    ⟨hzlow.le, by simpa only [upsilon_zero] using htargetHalf.le⟩
  have hw0 : 0 < w := by
    by_contra hn
    have hwzero : w = 0 := le_antisymm (le_of_not_gt hn) hw.1
    rw [hwzero, upsilon_zero] at hweq
    linarith
  refine ⟨w, ⟨hw0, hweq⟩, ?_⟩
  intro v hv
  exact strictAntiOn_upsilon.injOn hv.1.le hw0.le (hv.2.trans hweq.symm)

/-- The continuous integral is exactly the manuscript's varphi plus 1/k,
on its intended strictly positive domain. -/
theorem varphi_eq_upsilon_sub (k : ℕ) {z : ℝ} (hz : 0 < z) :
    Scalar.varphi k z = upsilon z - 1/(k : ℝ) := by
  have heval : ((1+z)*Real.log (1+z)-z)/z^2 =
      (1+z)/z^2*Real.log (1+z)-1/z := by
    field_simp [hz.ne']
  rw [upsilon_eq hz, heval]
  rfl

/-- Existence and uniqueness refer to the actual logarithmic varphi, not a
replacement scalar function or an assumed root. -/
theorem existsUnique_varphi_positive_zero (k : ℕ) (hk : 3 ≤ k) :
    ∃! z : ℝ, 0 < z ∧ Scalar.varphi k z = 0 := by
  obtain ⟨z, hz, huniq⟩ := existsUnique_upsilon_root k hk
  refine ⟨z, ⟨hz.1, ?_⟩, ?_⟩
  · rw [varphi_eq_upsilon_sub k hz.1, hz.2, sub_self]
  · intro v hv
    apply huniq
    refine ⟨hv.1, ?_⟩
    have h := hv.2
    rw [varphi_eq_upsilon_sub k hv.1] at h
    exact sub_eq_zero.mp h

/-- The frozen infimum-selected zK is the genuine unique positive zero. -/
theorem zK_spec (k : ℕ) (hk : 3 ≤ k) :
    0 < Scalar.zK k ∧ Scalar.varphi k (Scalar.zK k) = 0 ∧
      ∀ z : ℝ, 0 < z → Scalar.varphi k z = 0 → z = Scalar.zK k := by
  obtain ⟨z, hz, huniq⟩ := existsUnique_varphi_positive_zero k hk
  have hset : {w : ℝ | 0 < w ∧ Scalar.varphi k w = 0} = {z} := by
    ext w
    constructor
    · intro hw
      exact Set.mem_singleton_iff.mpr (huniq w hw)
    · intro hw
      have heq : w = z := Set.mem_singleton_iff.mp hw
      change 0 < w ∧ Scalar.varphi k w = 0
      simpa only [heq] using hz
  have hzk : Scalar.zK k = z := by
    unfold Scalar.zK
    rw [hset]
    simp
  rw [hzk]
  exact ⟨hz.1, hz.2, fun w hw hvarphi => huniq w ⟨hw, hvarphi⟩⟩

theorem strictAntiOn_varphi (k : ℕ) :
    StrictAntiOn (Scalar.varphi k) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [varphi_eq_upsilon_sub k hx, varphi_eq_upsilon_sub k hy]
  exact sub_lt_sub_right (strictAntiOn_upsilon hx.le hy.le hxy) _

theorem continuousOn_varphi (k : ℕ) :
    ContinuousOn (Scalar.varphi k) (Ioi (0 : ℝ)) := by
  have hc : ContinuousOn (fun z : ℝ => upsilon z - 1/(k : ℝ)) (Ioi (0 : ℝ)) :=
    (continuousOn_upsilon.mono Ioi_subset_Ici_self).sub continuousOn_const
  apply hc.congr
  intro z hz
  exact varphi_eq_upsilon_sub k hz

theorem tendsto_varphi_atTop (k : ℕ) :
    Tendsto (Scalar.varphi k) atTop (𝓝 (-1/(k : ℝ))) := by
  have h : Tendsto (fun z : ℝ => upsilon z - 1/(k : ℝ)) atTop
      (𝓝 (-1/(k : ℝ))) := by
    simpa only [zero_sub, neg_div] using tendsto_upsilon_atTop.sub_const (1/(k : ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [varphi_eq_upsilon_sub k hz]

/-- The elementary logarithmic gap needed to locate the pure scalar root. -/
def logGap (z : ℝ) : ℝ := Real.log (1+z)-2*z/(z+2)

theorem hasDerivAt_logGap {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt logGap (z^2/((1+z)*(z+2)^2)) z := by
  have h1 : 1+z ≠ 0 := ne_of_gt (by linarith)
  have h2 : z+2 ≠ 0 := ne_of_gt (by linarith)
  have hlog := ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)).log h1
  have hquot := ((hasDerivAt_id z).const_mul 2).div
    ((hasDerivAt_id z).add_const 2) h2
  convert hlog.sub hquot using 1
  · ext t
    rfl
  · dsimp
    field_simp [h1, h2]
    ring

theorem two_mul_div_add_two_lt_log {z : ℝ} (hz : 0 < z) :
    2*z/(z+2) < Real.log (1+z) := by
  have hc : ContinuousOn logGap (Ici (0 : ℝ)) := by
    intro x hx
    exact (hasDerivAt_logGap hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn logGap (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hc
    intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(hasDerivAt_logGap hx0.le).deriv]
    exact div_pos (sq_pos_of_pos hx0) (mul_pos (by linarith)
      (sq_pos_of_pos (by linarith : 0 < x+2)))
  have h := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) hz.le hz
  simp only [logGap, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at h
  exact sub_pos.mp h

/-- A strict lower bound for the exact scalar integral. -/
theorem inv_add_two_lt_upsilon {z : ℝ} (hz : 0 < z) : 1/(z+2) < upsilon z := by
  have h1 : 0 < 1+z := by linarith
  have h2 : z+2 ≠ 0 := ne_of_gt (by linarith)
  have hm := mul_lt_mul_of_pos_left (two_mul_div_add_two_lt_log hz) h1
  have hid : (1+z)*(2*z/(z+2))-z = z^2/(z+2) := by
    field_simp [h2]
    ring
  have hh : z^2/(z+2) < (1+z)*Real.log (1+z)-z := by rw [← hid]; linarith
  rw [upsilon_eq hz]
  apply (lt_div_iff₀ (sq_pos_of_pos hz)).mpr
  convert hh using 1; ring

/-- The critical pure scalar parameter lies strictly above k−2. -/
theorem zK_gt_sub_two (k : ℕ) (hk : 3 ≤ k) : (k : ℝ)-2 < Scalar.zK k := by
  have hz := zK_spec k hk
  have hu : upsilon (Scalar.zK k) = 1/(k : ℝ) := by
    have hv := hz.2.1
    rw [varphi_eq_upsilon_sub k hz.1] at hv
    exact sub_eq_zero.mp hv
  have hl := inv_add_two_lt_upsilon hz.1
  rw [hu] at hl
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz2 : 0 < Scalar.zK k+2 := by linarith [hz.1]
  have hc := (div_lt_div_iff₀ hz2 hk0).mp hl
  linarith

/-- The exact logarithmic root identity in the manuscript's pure evaluation. -/
theorem log_one_add_zK (k : ℕ) (hk : 3 ≤ k) :
    Real.log (1+Scalar.zK k) =
      Scalar.zK k*((k : ℝ)+Scalar.zK k)/((k : ℝ)*(1+Scalar.zK k)) := by
  have hz := zK_spec k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz1 : 1+Scalar.zK k ≠ 0 := ne_of_gt (by linarith [hz.1])
  have hv := hz.2.1
  unfold Scalar.varphi at hv
  field_simp [hz.1.ne', hk0.ne'] at hv
  apply (eq_div_iff (mul_ne_zero hk0.ne' hz1)).mpr
  nlinarith

end
end TensorPCA.ScalarThresholdProofs
