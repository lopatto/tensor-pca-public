-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTModelCurvatureProofs
public import TensorPCA.JTFirstVariationProofs

/-! Coercive and local Lipschitz bounds for the original variational
profiles. These are the compactness estimates for positive-floor minimization. -/
@[expose] public section
namespace TensorPCA.JTProfileBoundsProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def coercivityConstant (xi : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv (deriv xi) t*(1-t)

theorem profile_chord_lower {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (1-t)*p 0 ≤ p t := by
  have H := hp.2.2.1.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show 0 ≤ 1-t from sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t = 1)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add] at H
  have Hpos := mul_nonneg ht.1 (hp.2.2.2 1 (by norm_num)).le
  linarith

theorem functional_coercive {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ deriv (deriv xi) t)
    (hA : 0 ≤ h^2+deriv xi 0) :
    p 0*coercivityConstant xi ≤ Scalar.parisiFunctional xi h p := by
  have hpinv : ContinuousOn (fun t => 1/p t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp.1 (fun t ht => (hp.2.2.2 t ht).ne')
  have hc : ContinuousOn (fun t : ℝ => deriv (deriv xi) t*(1-t)) (Icc (0 : ℝ) 1) :=
    hxi.mul (continuousOn_const.sub continuousOn_id)
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      p 0*(deriv (deriv xi) t*(1-t)) ≤ deriv (deriv xi) t*p t+1/p t := by
    have H := mul_le_mul_of_nonneg_left (profile_chord_lower hp ht) (hw t ht)
    have Hinv : 0 ≤ 1/p t := (one_div_pos.mpr (hp.2.2.2 t ht)).le
    nlinarith
  have H := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (f := fun t => p 0*(deriv (deriv xi) t*(1-t)))
    (g := fun t => deriv (deriv xi) t*p t+1/p t)
    ((hc.const_mul (p 0)).intervalIntegrable_of_Icc zero_le_one)
    (((hxi.mul hp.1).add hpinv).intervalIntegrable_of_Icc zero_le_one) hpoint
  rw [intervalIntegral.integral_const_mul] at H
  unfold coercivityConstant Scalar.parisiFunctional
  exact H.trans (le_add_of_nonneg_right (mul_nonneg hA (hp.2.2.2 0 (by norm_num)).le))

theorem coercivityConstant_pos {xi : ℝ → ℝ}
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ deriv (deriv xi) t)
    (hpos : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv xi) t) :
    0 < coercivityConstant xi := by
  unfold coercivityConstant
  apply intervalIntegral.integral_pos zero_lt_one
    (hxi.mul (continuousOn_const.sub continuousOn_id))
  · intro t ht
    exact mul_nonneg (hw t ⟨ht.1.le,ht.2⟩) (sub_nonneg.mpr ht.2)
  · obtain ⟨t,ht,H⟩ := hpos
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,mul_pos H (sub_pos.mpr ht.2)⟩

theorem profile_initial_le_functional {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ deriv (deriv xi) t)
    (hpos : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv xi) t)
    (hA : 0 ≤ h^2+deriv xi 0) :
    p 0 ≤ Scalar.parisiFunctional xi h p/coercivityConstant xi :=
  (le_div_iff₀ (coercivityConstant_pos hxi hw hpos)).mpr (functional_coercive hp hxi h hw hA)

theorem profile_local_lipschitz {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {M r : ℝ} (hM : p 0 ≤ M) (hr : r < 1) :
    LipschitzOnWith ⟨M/(1-r),div_nonneg
      ((hp.2.2.2 0 (by norm_num)).le.trans hM) (sub_pos.mpr hr).le⟩ p (Icc (0 : ℝ) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this t ht s hs (le_of_not_ge hst)
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans hr.le⟩
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.trans hr.le⟩
  have hanti := hp.2.1 hs1 ht1 hst
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hanti),Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst),neg_sub]
  change p s-p t ≤ M/(1-r)*(t-s)
  rcases eq_or_lt_of_le hst with rfl | hst'
  · simp only [sub_self,mul_zero,le_refl]
  have htlt : t < 1 := ht.2.trans_lt hr
  have H := hp.2.2.1.slope_anti_adjacent hs1
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) hst' htlt
  have HH := (div_le_div_iff₀ (sub_pos.mpr htlt) (sub_pos.mpr hst')).mp H
  have H1 : (p s-p t)*(1-t) ≤ (p t-p 1)*(t-s) := by nlinarith only [HH]
  have H2 := mul_le_mul_of_nonneg_left (show 1-r ≤ 1-t by linarith [ht.2])
    (sub_nonneg.mpr hanti)
  have hpt : p t ≤ M := (hp.2.1 (by norm_num) ht1 ht.1).trans hM
  have H3 := mul_le_mul_of_nonneg_right (show p t-p 1 ≤ M by linarith [hp.2.2.2 1 (by norm_num)])
    (sub_nonneg.mpr hst)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
  exact H2.trans (H1.trans H3)

theorem xiSlice_secondDeriv_continuous (k : ℕ) (hk : 2 ≤ k) (m : ℝ) :
    Continuous (deriv (deriv (Scalar.xiSlice k m))) := by
  rw [JTModelCurvatureProofs.secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
  unfold JTModelCurvatureProofs.shiftedPower
  fun_prop

private theorem slice_curvature_coefficient_pos (k : ℕ) (hk : 2 ≤ k) {m : ℝ} (hm : |m| < 1) :
    0 < (k : ℝ)*((k : ℝ)-1)*(1-m^2)^2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  exact mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos hB)

theorem xiSlice_secondDeriv_nonneg (k : ℕ) (hk : 2 ≤ k) {m t : ℝ}
    (hm : |m| < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ deriv (deriv (Scalar.xiSlice k m)) t := by
  rw [JTModelCurvatureProofs.secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
  unfold JTModelCurvatureProofs.shiftedPower
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  exact mul_nonneg (slice_curvature_coefficient_pos k hk hm).le
    (pow_nonneg (add_nonneg (sq_nonneg m) (mul_nonneg hB.le ht.1)) _)

theorem xiSlice_secondDeriv_pos (k : ℕ) (hk : 2 ≤ k) {m t : ℝ}
    (hm : |m| < 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (deriv (Scalar.xiSlice k m)) t := by
  rw [JTModelCurvatureProofs.secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
  unfold JTModelCurvatureProofs.shiftedPower
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  exact mul_pos (slice_curvature_coefficient_pos k hk hm)
    (pow_pos (add_pos_of_nonneg_of_pos (sq_nonneg m) (mul_pos hB ht.1)) _)

theorem xiSlice_boundary_nonneg (k : ℕ) {m : ℝ} (hm : |m| < 1) (h : ℝ) :
    0 ≤ h^2+deriv (Scalar.xiSlice k m) 0 := by
  rw [VariationalProofs.deriv_xiSlice]
  simp only [mul_zero,add_zero]
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  exact add_nonneg (sq_nonneg h)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hB.le) (pow_nonneg (sq_nonneg m) _))

theorem xiSlice_coercivityConstant_pos (k : ℕ) (hk : 2 ≤ k) {m : ℝ} (hm : |m| < 1) :
    0 < coercivityConstant (Scalar.xiSlice k m) := by
  apply coercivityConstant_pos (xiSlice_secondDeriv_continuous k hk m).continuousOn
    (fun t ht => xiSlice_secondDeriv_nonneg k hk hm ht)
  exact ⟨1/2,by norm_num,xiSlice_secondDeriv_pos k hk hm (by norm_num)⟩

theorem xiSlice_profile_initial_bound (k : ℕ) (hk : 2 ≤ k) {m : ℝ} (hm : |m| < 1)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) (h : ℝ) :
    p 0 ≤ Scalar.parisiFunctional (Scalar.xiSlice k m) h p/coercivityConstant (Scalar.xiSlice k m) := by
  apply profile_initial_le_functional hp (xiSlice_secondDeriv_continuous k hk m).continuousOn h
    (fun t ht => xiSlice_secondDeriv_nonneg k hk hm ht) ?_ (xiSlice_boundary_nonneg k hm h)
  exact ⟨1/2,by norm_num,xiSlice_secondDeriv_pos k hk hm (by norm_num)⟩


end
end TensorPCA.JTProfileBoundsProofs
