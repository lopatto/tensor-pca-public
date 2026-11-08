-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianDensityProofs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Elementary radial Gaussian bounds, without gamma or Stirling estimates. -/
@[expose] public section
namespace TensorPCA.RadialTailBounds
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def radialDensity (p : ℕ) (r : ℝ) : ℝ := r^p*Real.exp (-r^2/2)

def radialMode (p : ℕ) : ℝ := Real.sqrt p

def radialNormalizer (p : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), radialDensity p r

/-- A fixed positive universal constant; no numerical estimate of pi is needed. -/
def tailLogConstant : ℝ := 4+2*Real.pi

theorem tailLogConstant_pos : 0 < tailLogConstant := by
  unfold tailLogConstant
  positivity

theorem radialDensity_nonneg (p : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ radialDensity p r :=
  mul_nonneg (pow_nonneg hr _) (Real.exp_pos _).le

theorem radialDensity_pos (p : ℕ) {r : ℝ} (hr : 0 < r) : 0 < radialDensity p r :=
  mul_pos (pow_pos hr _) (Real.exp_pos _)

theorem radialDensity_integrable (p : ℕ) : Integrable (radialDensity p) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ))
    (s := (p : ℝ)) (by norm_num) (by have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith)
  apply h.congr
  filter_upwards [] with r
  rw [Real.rpow_natCast]
  unfold radialDensity
  congr 1
  congr 1
  ring

theorem radialDensity_eq_exp (p : ℕ) {r : ℝ} (hr : 0 < r) :
    radialDensity p r = Real.exp ((p : ℝ)*Real.log r-r^2/2) := by
  unfold radialDensity
  calc
    _ = Real.exp (Real.log (r^p))*Real.exp (-r^2/2) := by
      rw [Real.exp_log (pow_pos hr _)]
    _ = _ := by
      rw [← Real.exp_add, Real.log_pow]
      congr 1
      ring

/-- The logarithm bound log x≤x−1 gives a sharp quadratic envelope at the
radial mode, with a dimension-independent Gaussian width. -/
theorem radialDensity_le_mode_gaussian (p : ℕ) {r : ℝ} (hr : 0 < r) :
    radialDensity p r ≤ radialDensity p (radialMode p) *
      Real.exp (-(r-radialMode p)^2/2) := by
  by_cases hp : p = 0
  · subst p
    simp [radialDensity, radialMode]
  · have hpp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
    have hm : 0 < radialMode p := Real.sqrt_pos.mpr hpp
    have hm2 : (radialMode p)^2 = (p : ℝ) := Real.sq_sqrt hpp.le
    have hlog := Real.log_le_sub_one_of_pos (div_pos hr hm)
    rw [Real.log_div hr.ne' hm.ne'] at hlog
    have hh := mul_le_mul_of_nonneg_left hlog hpp.le
    have halg : (p : ℝ)*(r/radialMode p-1) = radialMode p*r-(radialMode p)^2 := by
      rw [← hm2]
      field_simp [hm.ne']
    rw [halg] at hh
    rw [radialDensity_eq_exp p hr, radialDensity_eq_exp p hm, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith

theorem shiftedGaussian_integrable (m : ℝ) :
    Integrable (fun r : ℝ ↦ Real.exp (-(r-m)^2/2)) := by
  have hg := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
  have h := (measurePreserving_sub_right (volume : Measure ℝ) m).integrable_comp_of_integrable hg
  apply h.congr
  filter_upwards [] with r
  dsimp
  congr 1
  ring

theorem integral_shiftedGaussian (m : ℝ) :
    (∫ r : ℝ, Real.exp (-(r-m)^2/2)) = Real.sqrt (2*Real.pi) := by
  calc
    _ = ∫ r : ℝ, Real.exp (-(1/2 : ℝ)*(r-m)^2) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun r ↦ congrArg Real.exp (by ring)
    _ = ∫ r : ℝ, Real.exp (-(1/2 : ℝ)*r^2) :=
      integral_sub_right_eq_self (μ := volume) (fun r : ℝ ↦ Real.exp (-(1/2 : ℝ)*r^2)) m
    _ = _ := by
      rw [integral_gaussian]
      congr 1
      ring

theorem radialNormalizer_le_mode (p : ℕ) :
    radialNormalizer p ≤ Real.sqrt (2*Real.pi)*radialDensity p (radialMode p) := by
  have hpeak : 0 ≤ radialDensity p (radialMode p) := radialDensity_nonneg p (Real.sqrt_nonneg _)
  have hi := (shiftedGaussian_integrable (radialMode p)).const_mul (radialDensity p (radialMode p))
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), radialDensity p (radialMode p)*Real.exp (-(r-radialMode p)^2/2) := by
      apply integral_mono_ae (radialDensity_integrable p).integrableOn hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact radialDensity_le_mode_gaussian p hr
    _ = radialDensity p (radialMode p)*∫ r in Ioi (0 : ℝ), Real.exp (-(r-radialMode p)^2/2) :=
      integral_const_mul _ _
    _ ≤ radialDensity p (radialMode p)*∫ r : ℝ, Real.exp (-(r-radialMode p)^2/2) := by
      apply mul_le_mul_of_nonneg_left _ hpeak
      exact setIntegral_le_integral (shiftedGaussian_integrable _) (Eventually.of_forall fun r ↦ (Real.exp_pos _).le)
    _ = _ := by rw [integral_shiftedGaussian]; ring


theorem radius_window_sq_le {s r : ℝ} (hs : 1 ≤ s) (hr : r ∈ Icc s (s+s⁻¹)) :
    r^2 ≤ s^2+3 := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have hinv1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have hisq : (s⁻¹)^2 ≤ 1 := by nlinarith
  have hcross : s*s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  have hr0 : 0 ≤ r := hs0.le.trans hr.1
  have hup : r^2 ≤ (s+s⁻¹)^2 := (sq_le_sq₀ hr0 (by positivity)).mpr hr.2
  nlinarith

theorem radialDensity_window_lower (p : ℕ) {s r : ℝ} (hs : 1 ≤ s)
    (hr : r ∈ Icc s (s+s⁻¹)) :
    s^p*Real.exp (-(s^2+3)/2) ≤ radialDensity p r := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hp : s^p ≤ r^p := pow_le_pow_left₀ hs0 hr.1 p
  have he : Real.exp (-(s^2+3)/2) ≤ Real.exp (-r^2/2) :=
    Real.exp_le_exp.mpr (by linarith [radius_window_sq_le hs hr])
  exact mul_le_mul hp he (Real.exp_pos _).le (pow_nonneg (hs0.trans hr.1) _)

theorem radialTail_integral_lower (p : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    s⁻¹*s^p*Real.exp (-(s^2+3)/2) ≤ ∫ r in Ici s, radialDensity p r := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hle : s ≤ s+s⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr hs0.le)
  have hc : IntegrableOn (fun _r : ℝ ↦ s^p*Real.exp (-(s^2+3)/2)) (Icc s (s+s⁻¹)) :=
    continuous_const.integrableOn_Icc
  calc
    _ = ∫ _r in Icc s (s+s⁻¹), s^p*Real.exp (-(s^2+3)/2) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le hle]
      simp only [add_sub_cancel_left, smul_eq_mul]
      ring
    _ ≤ ∫ r in Icc s (s+s⁻¹), radialDensity p r := by
      apply setIntegral_mono_on hc (radialDensity_integrable p).integrableOn measurableSet_Icc
      exact fun r hr ↦ radialDensity_window_lower p hs hr
    _ ≤ ∫ r in Ici s, radialDensity p r := by
      apply setIntegral_mono_set (radialDensity_integrable p).integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
        exact radialDensity_nonneg p (hs0.le.trans hr)
      · exact Eventually.of_forall fun r hr ↦ hr.1

theorem radialTail_le_normalizer (p : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ r in Ici s, radialDensity p r) ≤ radialNormalizer p := by
  apply setIntegral_mono_set (radialDensity_integrable p).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact radialDensity_nonneg p hr.le
  · exact Eventually.of_forall fun r hr ↦ hs.trans_le hr

theorem radialNormalizer_pos (p : ℕ) : 0 < radialNormalizer p := by
  have h := radialTail_integral_lower p (s := 1) le_rfl
  have hpos : 0 < (1 : ℝ)⁻¹*1^p*Real.exp (-(1^2+3)/2) := by positivity
  exact hpos.trans_le (h.trans (radialTail_le_normalizer p zero_lt_one))


theorem radialNormalizer_dim_upper (N : ℕ) :
    radialNormalizer (N-1) ≤ Real.sqrt (2*Real.pi)*(Real.sqrt N)^(N-1)*
      Real.exp (-((N-1 : ℕ) : ℝ)/2) := by
  apply (radialNormalizer_le_mode (N-1)).trans
  have hp : ((N-1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hpow : (Real.sqrt ((N-1 : ℕ) : ℝ))^(N-1) ≤ (Real.sqrt (N : ℝ))^(N-1) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hp) _
  unfold radialDensity radialMode
  rw [Real.sq_sqrt (Nat.cast_nonneg (N-1))]
  have he := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-((N-1 : ℕ) : ℝ)/2)).le
  have hroot : 0 ≤ Real.sqrt (2*Real.pi) := Real.sqrt_nonneg _
  nlinarith

theorem half_le_log_two : (1/2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
  rw [one_div, Real.log_inv] at h
  linarith

theorem logarithmic_constant_bound {N : ℕ} (hN : 0 < N) :
    (1/2 : ℝ)*Real.log N+2+(1/2 : ℝ)*Real.log (2*Real.pi) ≤
      tailLogConstant*Real.log ((N : ℝ)+1) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hlogn : Real.log (N : ℝ) ≤ Real.log ((N : ℝ)+1) :=
    Real.log_le_log hn (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log ((N : ℝ)+1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hp := Real.log_le_sub_one_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have hd : (1/2 : ℝ) ≤ Real.log ((N : ℝ)+1) := half_le_log_two.trans hlog2
  unfold tailLogConstant
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hd)]

/-- The explicit positive window/upper-normalizer ratio has the required
uniform logarithmic lower bound, including N=1. -/
theorem log_window_ratio_lower {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    -(N : ℝ)/2*(b-1-Real.log b)-2*Real.log b-tailLogConstant*Real.log ((N : ℝ)+1) ≤
      Real.log (((Real.sqrt ((N : ℝ)*b))⁻¹*(Real.sqrt ((N : ℝ)*b))^(N-1)*
        Real.exp (-(((Real.sqrt ((N : ℝ)*b))^2)+3)/2)) /
        (Real.sqrt (2*Real.pi)*(Real.sqrt N)^(N-1)*
          Real.exp (-((N-1 : ℕ) : ℝ)/2))) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hs : 0 < Real.sqrt ((N : ℝ)*b) := Real.sqrt_pos.mpr (mul_pos hn hb0)
  have ht : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hp : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hN), Nat.cast_one]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (inv_pos.mpr hs).ne' (pow_pos hs _).ne', Real.log_inv, Real.log_pow,
    Real.log_exp, Real.log_mul (mul_pos hc (pow_pos ht _)).ne' (Real.exp_pos _).ne',
    Real.log_mul hc.ne' (pow_pos ht _).ne', Real.log_pow, Real.log_exp,
    Real.log_sqrt (mul_nonneg hn.le hb0.le), Real.log_mul hn.ne' hb0.ne',
    Real.log_sqrt hn.le, Real.log_sqrt (mul_nonneg (by norm_num) Real.pi_pos.le),
    Real.sq_sqrt (mul_nonneg hn.le hb0.le), hp]
  nlinarith [logarithmic_constant_bound hN, Real.log_nonneg hb]

/-- A uniform nonasymptotic lower bound for the radial Gaussian tail ratio.
The exponent matches the manuscript's logarithmic allowance with C=4+2*pi. -/
theorem radialTail_ratio_lower {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    Real.exp (-(N : ℝ)/2*(b-1-Real.log b)-2*Real.log b-tailLogConstant*Real.log ((N : ℝ)+1)) ≤
      (∫ r in Ici (Real.sqrt ((N : ℝ)*b)), radialDensity (N-1) r)/radialNormalizer (N-1) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  let s : ℝ := Real.sqrt ((N : ℝ)*b)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hn hb0)
  have hs1 : 1 ≤ s := by
    apply Real.one_le_sqrt.mpr
    nlinarith
  let L : ℝ := s⁻¹*s^(N-1)*Real.exp (-(s^2+3)/2)
  let U : ℝ := Real.sqrt (2*Real.pi)*(Real.sqrt N)^(N-1)*Real.exp (-((N-1 : ℕ) : ℝ)/2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hZ : 0 < radialNormalizer (N-1) := radialNormalizer_pos _
  have hlog := log_window_ratio_lower hN hb
  have hfirst : Real.exp (-(N : ℝ)/2*(b-1-Real.log b)-2*Real.log b-tailLogConstant*Real.log ((N : ℝ)+1)) ≤ L/U :=
    (Real.le_log_iff_exp_le (div_pos hL hU)).mp hlog
  apply hfirst.trans
  apply (div_le_div_of_nonneg_left hL.le hZ (radialNormalizer_dim_upper N)).trans
  exact div_le_div_of_nonneg_right (radialTail_integral_lower (N-1) hs1) hZ.le

end
end TensorPCA.RadialTailBounds
