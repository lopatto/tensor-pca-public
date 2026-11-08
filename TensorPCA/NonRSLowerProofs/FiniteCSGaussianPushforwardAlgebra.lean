-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSFunctionalTransport

/-! Constructive finite three-atom Gaussian-to-CS transport. All laws are probability
measures; their integrated CDF and ordinary entropy are computed from the measure,
including coincident nodes and zero atom weights.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianPushforwardAlgebra
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCS RetainedCountProofs.CrisantiSommers
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def threeAtomLaw (x z r0 r1 r2 : ℝ) : Measure ℝ :=
  ENNReal.ofReal x • Measure.dirac r0+
    ENNReal.ofReal (z-x) • Measure.dirac r1+
    ENNReal.ofReal (1-z) • Measure.dirac r2

theorem threeAtomLaw_probability {x z r0 r1 r2 : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) :
    IsProbabilityMeasure (threeAtomLaw x z r0 r1 r2) := by
  constructor
  simp only [threeAtomLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hx (sub_nonneg.mpr hxz),
    ← ENNReal.ofReal_add (by linarith : 0 ≤ x+(z-x)) (sub_nonneg.mpr hz)]
  convert ENNReal.ofReal_one using 1 <;> congr 1 <;> ring

theorem threeAtomLaw_hasCutoff {x z r0 r1 r2 : ℝ}
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1) :
    HasCutoff (threeAtomLaw x z r0 r1 r2) r2 := by
  refine ⟨hr0.trans (hr01.trans hr12), hr2, ?_⟩
  rw [threeAtomLaw, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨hr0, hr01.trans hr12⟩
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨hr0.trans hr01, hr12⟩
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨hr0.trans (hr01.trans hr12), le_rfl⟩

theorem integral_threeAtomLaw {x z r0 r1 r2 : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) (f : ℝ → ℝ) :
    (∫ r, f r ∂threeAtomLaw x z r0 r1 r2) = x*f r0+(z-x)*f r1+(1-z)*f r2 := by
  have h0 : Integrable f (ENNReal.ofReal x • Measure.dirac r0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have h1 : Integrable f (ENNReal.ofReal (z-x) • Measure.dirac r1) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable f (ENNReal.ofReal (1-z) • Measure.dirac r2) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [threeAtomLaw, integral_add_measure (h0.add_measure h1) h2,
    integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal hx,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxz), ENNReal.toReal_ofReal (sub_nonneg.mpr hz)]

theorem xHat_threeAtomLaw {x z r0 r1 r2 : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) (t : ℝ) :
    xHat (threeAtomLaw x z r0 r1 r2) t =
      x*(1-max t r0)+(z-x)*(1-max t r1)+(1-z)*(1-max t r2) := by
  unfold xHat
  rw [integral_threeAtomLaw hx hxz hz]

def threeAtomTrial (x z r0 r1 r2 : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1) : Trial :=
  letI := threeAtomLaw_probability (r0 := r0) (r1 := r1) (r2 := r2) hx hxz hz
  cutoffTrial (threeAtomLaw x z r0 r1 r2) (threeAtomLaw_hasCutoff hr0 hr01 hr12 hr2)

theorem realLaw_threeAtomTrial (x z r0 r1 r2 : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1) :
    realLaw (threeAtomTrial x z r0 r1 r2 hx hxz hz hr0 hr01 hr12 hr2) = threeAtomLaw x z r0 r1 r2 := by
  letI := threeAtomLaw_probability (r0 := r0) (r1 := r1) (r2 := r2) hx hxz hz
  unfold threeAtomTrial
  exact realLaw_cutoffTrial _ _

theorem threeAtomTrial_ae_le (x z r0 r1 r2 : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1) :
    ∀ᵐ (r : Overlap) ∂(threeAtomTrial x z r0 r1 r2 hx hxz hz hr0 hr01 hr12 hr2 : Measure Overlap), (r : ℝ) ≤ r2 := by
  letI := threeAtomLaw_probability (r0 := r0) (r1 := r1) (r2 := r2) hx hxz hz
  unfold threeAtomTrial
  exact cutoffTrial_ae_le _ _

theorem xHat_threeAtom_head {x z r0 r1 r2 t : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (ht : t ≤ r0) :
    xHat (threeAtomLaw x z r0 r1 r2) t = 1-r2+z*(r2-r1)+x*(r1-r0) := by
  rw [xHat_threeAtomLaw hx hxz hz, max_eq_right ht,
    max_eq_right (ht.trans hr01), max_eq_right (ht.trans (hr01.trans hr12))]
  ring

theorem xHat_threeAtom_middle {x z r0 r1 r2 t : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) (hr12 : r1 ≤ r2) (ht : t ∈ Icc r0 r1) :
    xHat (threeAtomLaw x z r0 r1 r2) t = 1-r2+z*(r2-r1)+x*(r1-t) := by
  rw [xHat_threeAtomLaw hx hxz hz, max_eq_left ht.1,
    max_eq_right ht.2, max_eq_right (ht.2.trans hr12)]
  ring

theorem xHat_threeAtom_top {x z r0 r1 r2 t : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) (hr01 : r0 ≤ r1) (ht : t ∈ Icc r1 r2) :
    xHat (threeAtomLaw x z r0 r1 r2) t = 1-r2+z*(r2-t) := by
  rw [xHat_threeAtomLaw hx hxz hz, max_eq_left (hr01.trans ht.1),
    max_eq_left ht.1, max_eq_right ht.2]
  ring

theorem profile_threeAtomTrial (beta x z r0 r1 r2 : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1) (t : ℝ) :
    profile beta (threeAtomTrial x z r0 r1 r2 hx hxz hz hr0 hr01 hr12 hr2) t =
      beta*(x*(1-max t r0)+(z-x)*(1-max t r1)+(1-z)*(1-max t r2)) := by
  rw [profile_eq_scaled_xHat_realLaw, realLaw_threeAtomTrial, xHat_threeAtomLaw hx hxz hz]

theorem integral_inverse_affine_segment {a b c x : ℝ} (hab : a ≤ b) (hc : 0 < c) (hx : 0 < x) :
    (∫ t in a..b, (c+x*(b-t))⁻¹) = Real.log ((c+x*(b-a))/c)/x := by
  have hp (t : ℝ) (ht : t ∈ Icc a b) : 0 < c+x*(b-t) :=
    add_pos_of_pos_of_nonneg hc (mul_nonneg hx.le (sub_nonneg.mpr ht.2))
  have hi : ContinuousOn (fun t : ℝ => (c+x*(b-t))⁻¹) (Icc a b) := by
    apply (continuous_const.add (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn.inv₀
    intro t ht
    exact (hp t ht).ne'
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun u : ℝ => -Real.log (c+x*(b-u))/x) ((c+x*(b-t))⁻¹) t := by
    rw [uIcc_of_le hab] at ht
    have haff : HasDerivAt (fun u : ℝ => c+x*(b-u)) (-x) t := by
      convert (((hasDerivAt_id t).const_sub b).const_mul x).const_add c using 1 <;>
        (try funext u) <;> (try simp only [id_eq]) <;> ring
    convert ((haff.log (hp t ht).ne').neg.div_const x) using 1
    field_simp [hx.ne', (hp t ht).ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.intervalIntegrable_of_Icc hab)]
  simp only [sub_self, mul_zero, add_zero]
  rw [Real.log_div (hp a ⟨le_rfl, hab⟩).ne' hc.ne']
  ring

theorem integral_inverse_xHat_threeAtom {x z r0 r1 r2 D0 D1 D2 : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1)
    (hD0 : 0 < D0) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (hhat2 : 1-r2=1/D2) (hhat1 : 1/D1=1/D2+z*(r2-r1))
    (hhat0 : 1/D0=1/D1+x*(r1-r0)) :
    (∫ t in (0 : ℝ)..r2, (xHat (threeAtomLaw x z r0 r1 r2) t)⁻¹) =
      r0*D0+Real.log (D1/D0)/x+Real.log (D2/D1)/z := by
  let mu := threeAtomLaw x z r0 r1 r2
  letI := threeAtomLaw_probability (r0 := r0) (r1 := r1) (r2 := r2) hx.le hxz hz
  have hcut := threeAtomLaw_hasCutoff (x := x) (z := z) hr0 hr01 hr12 hr2
  have h00 : (∫ t in (0 : ℝ)..r0, (xHat mu t)⁻¹) = r0*D0 := by
    calc
      _ = ∫ t in (0 : ℝ)..r0, (1/D0 : ℝ)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr0] at ht
        dsimp only [mu]
        rw [xHat_threeAtom_head hx.le hxz hz hr01 hr12 ht.2]
        congr 1
        linarith [hhat0, hhat1, hhat2]
      _ = _ := by simp
  have h01 : (∫ t in r0..r1, (xHat mu t)⁻¹) = Real.log (D1/D0)/x := by
    calc
      _ = ∫ t in r0..r1, (1/D1+x*(r1-t))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr01] at ht
        dsimp only [mu]
        rw [xHat_threeAtom_middle hx.le hxz hz hr12 ht]
        congr 1
        linarith [hhat1, hhat2]
      _ = _ := by
        rw [integral_inverse_affine_segment hr01 (one_div_pos.mpr hD1) hx, ← hhat0]
        congr 2
        field_simp
  have hzpos : 0 < z := hx.trans_le hxz
  have h12 : (∫ t in r1..r2, (xHat mu t)⁻¹) = Real.log (D2/D1)/z := by
    calc
      _ = ∫ t in r1..r2, (1/D2+z*(r2-t))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr12] at ht
        dsimp only [mu]
        rw [xHat_threeAtom_top hx.le hxz hz hr01 ht]
        rw [hhat2]
      _ = _ := by
        rw [integral_inverse_affine_segment hr12 (one_div_pos.mpr hD2) hzpos, ← hhat1]
        congr 2
        field_simp
  have hI00 := inverse_xHat_intervalIntegrable mu hcut (a := 0) (b := r0)
    (by norm_num) ((hr01.trans hr12).trans_lt hr2)
  have hI01 := inverse_xHat_intervalIntegrable mu hcut (a := r0) (b := r1)
    ((hr01.trans hr12).trans_lt hr2) (hr12.trans_lt hr2)
  have hI12 := inverse_xHat_intervalIntegrable mu hcut (a := r1) (b := r2) (hr12.trans_lt hr2) hr2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI00.trans hI01) hI12,
    ← intervalIntegral.integral_add_adjacent_intervals hI00 hI01, h00, h01, h12]

theorem functional_threeAtom_eval {x z r0 r1 r2 D0 D1 D2 : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1)
    (hD0 : 0 < D0) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (hhat2 : 1-r2=1/D2) (hhat1 : 1/D1=1/D2+z*(r2-r1))
    (hhat0 : 1/D0=1/D1+x*(r1-r0)) (beta : ℝ) (xi : ℝ → ℝ) :
    2*functional beta xi (threeAtomLaw x z r0 r1 r2) r2 =
      beta^2*(xi 1-(x*xi r0+(z-x)*xi r1+(1-z)*xi r2))+
        r0*D0+Real.log (D1/D0)/x+Real.log (D2/D1)/z-Real.log D2 := by
  unfold functional
  rw [integral_threeAtomLaw hx.le hxz hz,
    integral_inverse_xHat_threeAtom hx hxz hz hr0 hr01 hr12 hr2 hD0 hD1 hD2 hhat2 hhat1 hhat0,
    hhat2, Real.log_div one_ne_zero hD2.ne', Real.log_one]
  ring

theorem precision_pushforward_relations {x z y0 delta0 delta1 delta2 B : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z ≤ 1) (hy : 0 < y0)
    (hd0 : 0 ≤ delta0) (hd1 : 0 ≤ delta1) (hd2 : 0 ≤ delta2)
    (hB : x*delta0+z*delta1+delta2 < B)
    (hroot : y0/(B-(x*delta0+z*delta1+delta2))^2+
      delta0/((B-(x*delta0+z*delta1+delta2))*(B-(z*delta1+delta2)))+
      delta1/((B-(z*delta1+delta2))*(B-delta2))+delta2/((B-delta2)*B)=1-1/B) :
    let D0 := B-(x*delta0+z*delta1+delta2)
    let D1 := B-(z*delta1+delta2)
    let D2 := B-delta2
    let r0 := y0/D0^2
    let r1 := r0+delta0/(D0*D1)
    let r2 := r1+delta1/(D1*D2)
    0 < D0 ∧ 0 < D1 ∧ 0 < D2 ∧ 0 < B ∧ 0 < r0 ∧ r0 ≤ r1 ∧ r1 ≤ r2 ∧ r2 < 1 ∧
      1-r2=1/D2 ∧ 1/D1=1/D2+z*(r2-r1) ∧ 1/D0=1/D1+x*(r1-r0) := by
  dsimp only
  let D0 := B-(x*delta0+z*delta1+delta2)
  let D1 := B-(z*delta1+delta2)
  let D2 := B-delta2
  let r0 := y0/D0^2
  let r1 := r0+delta0/(D0*D1)
  let r2 := r1+delta1/(D1*D2)
  change 0 < D0 ∧ 0 < D1 ∧ 0 < D2 ∧ 0 < B ∧ 0 < r0 ∧ r0 ≤ r1 ∧ r1 ≤ r2 ∧ r2 < 1 ∧
    1-r2=1/D2 ∧ 1/D1=1/D2+z*(r2-r1) ∧ 1/D0=1/D1+x*(r1-r0)
  have hzpos : 0 < z := hx.trans_le hxz
  have hD0 : 0 < D0 := sub_pos.mpr hB
  have hD1 : 0 < D1 := by dsimp [D1]; nlinarith [mul_nonneg hx.le hd0]
  have hD2 : 0 < D2 := by dsimp [D2]; nlinarith [mul_nonneg hx.le hd0, mul_nonneg hzpos.le hd1]
  have hBp : 0 < B := by nlinarith [mul_nonneg hx.le hd0, mul_nonneg hzpos.le hd1]
  have hr0 : 0 < r0 := div_pos hy (sq_pos_of_pos hD0)
  have hr01 : r0 ≤ r1 := le_add_of_nonneg_right (div_nonneg hd0 (mul_nonneg hD0.le hD1.le))
  have hr12 : r1 ≤ r2 := le_add_of_nonneg_right (div_nonneg hd1 (mul_nonneg hD1.le hD2.le))
  have hgap1 : r1-r0=delta0/(D0*D1) := by dsimp [r1]; ring
  have hgap2 : r2-r1=delta1/(D1*D2) := by dsimp [r2]; ring
  change r2+delta2/(D2*B)=1-1/B at hroot
  have hlast : 1/B+delta2/(D2*B)=1/D2 := by
    field_simp [hBp.ne', hD2.ne']
    dsimp [D2]
    ring
  have hhat2 : 1-r2=1/D2 := by linarith [hroot, hlast]
  have hr2 : r2 < 1 := by linarith [one_div_pos.mpr hD2]
  have hhat1 : 1/D1=1/D2+z*(r2-r1) := by
    rw [hgap2]
    field_simp [hD1.ne', hD2.ne']
    dsimp [D1, D2]
    ring
  have hhat0 : 1/D0=1/D1+x*(r1-r0) := by
    rw [hgap1]
    field_simp [hD0.ne', hD1.ne']
    dsimp [D0, D1]
    ring
  exact ⟨hD0, hD1, hD2, hBp, hr0, hr01, hr12, hr2, hhat2, hhat1, hhat0⟩

theorem rawValue_le_threeAtomFunctional (k : ℕ) (hk : 1 ≤ k) {beta m x z r0 r1 r2 : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1)
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hr2 : r2 < 1) :
    beta*(rawValue k beta m).toReal ≤
      2*functional beta (Scalar.xiSlice k m) (threeAtomLaw x z r0 r1 r2) r2 := by
  let nu := threeAtomTrial x z r0 r1 r2 hx hxz hz hr0 hr01 hr12 hr2
  have hcut : r2 ∈ Ico (0 : ℝ) 1 := ⟨hr0.trans (hr01.trans hr12), hr2⟩
  have hae := threeAtomTrial_ae_le x z r0 r1 r2 hx hxz hz hr0 hr01 hr12 hr2
  have hfinite := rawFunctional_cutoff_ne_top k hk hbeta hm nu hcut hae
  have H : rawValue k beta m ≤ rawFunctional k beta m nu := sInf_le ⟨nu, rfl⟩
  have HR := ENNReal.toReal_mono hfinite H
  rw [rawFunctional_cutoff_toReal k hk hbeta hm nu hcut hae,
    realLaw_threeAtomTrial] at HR
  have HH := mul_le_mul_of_nonneg_left HR hbeta.le
  have heq : beta*(2*functional beta (Scalar.xiSlice k m) (threeAtomLaw x z r0 r1 r2) r2/beta) =
      2*functional beta (Scalar.xiSlice k m) (threeAtomLaw x z r0 r1 r2) r2 := by
    field_simp [hbeta.ne']
  rwa [heq] at HH

theorem weighted_increment_telescope {h y yn D Dn r rn : ℝ}
    (hD : D ≠ 0) (hDn : Dn ≠ 0)
    (hprec : Dn-D=h*(yn-y)) (hnode : rn-r=(yn-y)/(D*Dn)) :
    h*(rn*yn-r*y) = (rn*Dn-r*D)+(y/D-yn/Dn) := by
  have hrn : rn=r+(yn-y)/(D*Dn) := by linarith [hnode]
  have hdeq : Dn=D+h*(yn-y) := by linarith [hprec]
  have hDn' : D+h*(yn-y) ≠ 0 := by rwa [← hdeq]
  rw [hrn, hdeq]
  field_simp [hD, hDn']
  ring

private theorem moment_of_steps (x z y0 y1 y2 y3 B D0 D1 D2 r0 r1 r2 r3 : ℝ)
    (hB : B ≠ 0)
    (ht0 : x*(r1*y1-r0*y0)=(r1*D1-r0*D0)+(y0/D0-y1/D1))
    (ht1 : z*(r2*y2-r1*y1)=(r2*D2-r1*D1)+(y1/D1-y2/D2))
    (ht2 : (1 : ℝ)*(r3*y3-r2*y2)=(r3*B-r2*D2)+(y2/D2-y3/B))
    (hboundary : r0*D0=y0/D0) (hroot : r3=1-1/B) :
    x*r0*y0+(z-x)*r1*y1+(1-z)*r2*y2 = y3-B+1 := by
  have ht : x*(r1*y1-r0*y0)+z*(r2*y2-r1*y1)+(r3*y3-r2*y2) =
      r3*B-r0*D0+y0/D0-y3/B := by nlinarith [ht0, ht1, ht2]
  have hs : x*r0*y0+(z-x)*r1*y1+(1-z)*r2*y2 =
      r3*y3-(x*(r1*y1-r0*y0)+z*(r2*y2-r1*y1)+(r3*y3-r2*y2)) := by ring
  rw [hs, ht, hboundary, hroot]
  field_simp [hB]
  ring

theorem precision_weighted_moment {x z y0 y1 y2 y3 B : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz : z ≤ 1) (hy : 0 < y0)
    (h01 : y0 ≤ y1) (h12 : y1 ≤ y2) (h23 : y2 ≤ y3)
    (hB : x*(y1-y0)+z*(y2-y1)+(y3-y2) < B)
    (hroot : y0/(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)))^2+
      (y1-y0)/((B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)))*(B-(z*(y2-y1)+(y3-y2))))+
      (y2-y1)/((B-(z*(y2-y1)+(y3-y2)))*(B-(y3-y2)))+(y3-y2)/((B-(y3-y2))*B)=1-1/B) :
    let D0 := B-(x*(y1-y0)+z*(y2-y1)+(y3-y2))
    let D1 := B-(z*(y2-y1)+(y3-y2))
    let D2 := B-(y3-y2)
    let r0 := y0/D0^2
    let r1 := r0+(y1-y0)/(D0*D1)
    let r2 := r1+(y2-y1)/(D1*D2)
    x*r0*y0+(z-x)*r1*y1+(1-z)*r2*y2 = y3-B+1 := by
  dsimp only
  let delta0 := y1-y0
  let delta1 := y2-y1
  let delta2 := y3-y2
  let D0 := B-(x*delta0+z*delta1+delta2)
  let D1 := B-(z*delta1+delta2)
  let D2 := B-delta2
  let r0 := y0/D0^2
  let r1 := r0+delta0/(D0*D1)
  let r2 := r1+delta1/(D1*D2)
  let r3 := r2+delta2/(D2*B)
  change x*r0*y0+(z-x)*r1*y1+(1-z)*r2*y2 = y3-B+1
  have hzpos : 0 < z := hx.trans_le hxz
  have h0 : 0 ≤ delta0 := sub_nonneg.mpr h01
  have h1 : 0 ≤ delta1 := sub_nonneg.mpr h12
  have h2 : 0 ≤ delta2 := sub_nonneg.mpr h23
  have hD0 : 0 < D0 := sub_pos.mpr hB
  have hD1 : 0 < D1 := by dsimp [D1]; nlinarith [mul_nonneg hx.le h0]
  have hD2 : 0 < D2 := by dsimp [D2]; nlinarith [mul_nonneg hx.le h0, mul_nonneg hzpos.le h1]
  have hBp : 0 < B := by nlinarith [mul_nonneg hx.le h0, mul_nonneg hzpos.le h1]
  have hp0 : D1-D0=x*(y1-y0) := by dsimp [D0, D1, delta0, delta1, delta2]; ring
  have hp1 : D2-D1=z*(y2-y1) := by dsimp [D1, D2, delta1, delta2]; ring
  have hp2 : B-D2=(1 : ℝ)*(y3-y2) := by dsimp [D2, delta2]; ring
  have hn0 : r1-r0=(y1-y0)/(D0*D1) := by change (r0+(y1-y0)/(D0*D1))-r0=_; ring
  have hn1 : r2-r1=(y2-y1)/(D1*D2) := by change (r1+(y2-y1)/(D1*D2))-r1=_; ring
  have hn2 : r3-r2=(y3-y2)/(D2*B) := by change (r2+(y3-y2)/(D2*B))-r2=_; ring
  have ht0 := weighted_increment_telescope (h := x) (y := y0) (yn := y1)
    (D := D0) (Dn := D1) (r := r0) (rn := r1) hD0.ne' hD1.ne' hp0 hn0
  have ht1 := weighted_increment_telescope (h := z) (y := y1) (yn := y2)
    (D := D1) (Dn := D2) (r := r1) (rn := r2) hD1.ne' hD2.ne' hp1 hn1
  have ht2 := weighted_increment_telescope (h := 1) (y := y2) (yn := y3)
    (D := D2) (Dn := B) (r := r2) (rn := r3) hD2.ne' hBp.ne' hp2 hn2
  have hboundary : r0*D0=y0/D0 := by
    change (y0/D0^2)*D0=y0/D0
    field_simp [hD0.ne']
  change r3=1-1/B at hroot
  exact moment_of_steps x z y0 y1 y2 y3 B D0 D1 D2 r0 r1 r2 r3 hBp.ne'
    ht0 ht1 ht2 hboundary hroot


end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianPushforwardAlgebra
