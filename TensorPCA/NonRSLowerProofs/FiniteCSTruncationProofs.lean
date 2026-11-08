-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSTruncationKernel
public import TensorPCA.NonRSLowerProofs.FiniteCSPositivity
public import TensorPCA.NonRSLowerProofs.FiniteCSEnergyKernel

/-! Entropy improvement under overlap-law truncation. We compare nonnegative extended
costs additively, without subtracting infinite integrals. A conservative interval
estimate suffices for a uniform support cutoff.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem entropyExcess_truncate_le {beta : ℝ} (hbeta : 0 ≤ beta) (nu : Trial)
    (R : Overlap) (t : ℝ) :
    entropyExcess beta (truncateTrial nu R) t ≤ entropyExcess beta nu t := by
  unfold entropyExcess
  apply tsub_le_tsub_right
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.ofReal_le_ofReal
  linarith [(profile_truncate_gain_bounds hbeta nu R t).1]

theorem entropy_truncate_le {beta : ℝ} (hbeta : 0 ≤ beta) (nu : Trial) (R : Overlap) :
    entropy beta (truncateTrial nu R) ≤ entropy beta nu :=
  lintegral_mono (fun t => entropyExcess_truncate_le hbeta nu R t)

theorem entropyExcess_eq_ofReal {beta : ℝ} (hbeta : 0 < beta) (nu : Trial)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hp : 0 < profile beta nu t) :
    entropyExcess beta nu t =
      ENNReal.ofReal ((profile beta nu t)⁻¹-(beta*(1-t))⁻¹) := by
  have hbase : 0 < beta*(1-t) := mul_pos hbeta (sub_pos.mpr ht.2)
  rw [entropyExcess, ← ENNReal.ofReal_inv_of_pos hp,
    ← ENNReal.ofReal_inv_of_pos hbase, ← ENNReal.ofReal_sub _ (inv_nonneg.mpr hbase.le)]

theorem entropyExcess_real_nonneg {beta : ℝ} (hbeta : 0 < beta) (nu : Trial)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hp : 0 < profile beta nu t) :
    0 ≤ (profile beta nu t)⁻¹-(beta*(1-t))⁻¹ := by
  apply sub_nonneg.mpr
  exact inv_anti₀ hp (profile_bounds hbeta.le nu ⟨ht.1, ht.2.le⟩).2

theorem entropyExcess_truncate_add_gain_le {beta : ℝ} (hbeta : 0 < beta)
    (nu : Trial) (hfinite : entropy beta nu ≠ ∞) (R : Overlap)
    (hR0 : (1 / 2 : ℝ) < (R : ℝ)) (hR1 : (R : ℝ) < 1)
    {t : ℝ} (ht : t ∈ Icc (2*(R : ℝ)-1) (R : ℝ)) :
    entropyExcess beta (truncateTrial nu R) t+
      ENNReal.ofReal (truncationGain beta nu R/(4*beta^2*(1-(R : ℝ))^2)) ≤
        entropyExcess beta nu t := by
  have ht01 : t ∈ Ico (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.trans_lt hR1⟩
  have hp := profile_pos_of_entropy_ne_top hbeta nu hfinite ht01
  have hgain := truncationGain_nonneg hbeta.le nu R
  have heq := profile_truncate_gain_eq beta nu R ht.2
  have hpnew : 0 < profile beta (truncateTrial nu R) t := by linarith
  have hbnew := (profile_bounds hbeta.le (truncateTrial nu R) ⟨ht01.1, ht01.2.le⟩).2
  have hbound : profile beta (truncateTrial nu R) t ≤ 2*beta*(1-(R : ℝ)) := by
    have H := mul_le_mul_of_nonneg_left (show 1-t ≤ 2*(1-(R : ℝ)) by linarith [ht.1])
      hbeta.le
    nlinarith
  have hprodpos : 0 < profile beta nu t*profile beta (truncateTrial nu R) t :=
    mul_pos hp hpnew
  have hprod : profile beta nu t*profile beta (truncateTrial nu R) t ≤
      4*beta^2*(1-(R : ℝ))^2 := by
    have hpold : profile beta nu t ≤ 2*beta*(1-(R : ℝ)) := by linarith
    have H := mul_le_mul hpold hbound hpnew.le (by positivity : 0 ≤ 2*beta*(1-(R : ℝ)))
    nlinarith
  have hdiv := div_le_div_of_nonneg_left hgain hprodpos hprod
  have hinv : truncationGain beta nu R/
      (profile beta nu t*profile beta (truncateTrial nu R) t) =
      (profile beta nu t)⁻¹-(profile beta (truncateTrial nu R) t)⁻¹ := by
    field_simp [hp.ne', hpnew.ne']
    linarith
  rw [hinv] at hdiv
  have hnewnonneg := entropyExcess_real_nonneg hbeta (truncateTrial nu R) ht01 hpnew
  have htermnonneg : 0 ≤ truncationGain beta nu R/(4*beta^2*(1-(R : ℝ))^2) := by positivity
  rw [entropyExcess_eq_ofReal hbeta (truncateTrial nu R) ht01 hpnew,
    entropyExcess_eq_ofReal hbeta nu ht01 hp,
    ← ENNReal.ofReal_add hnewnonneg htermnonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem entropy_truncate_add_gain_le {beta : ℝ} (hbeta : 0 < beta)
    (nu : Trial) (hfinite : entropy beta nu ≠ ∞) (R : Overlap)
    (hR0 : (1 / 2 : ℝ) < (R : ℝ)) (hR1 : (R : ℝ) < 1) :
    entropy beta (truncateTrial nu R)+
      ENNReal.ofReal (truncationGain beta nu R/(4*beta^2*(1-(R : ℝ)))) ≤
        entropy beta nu := by
  let J := Ico (0 : ℝ) 1
  let I := Icc (2*(R : ℝ)-1) (R : ℝ)
  let A := truncationGain beta nu R/(4*beta^2*(1-(R : ℝ))^2)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (truncationGain_nonneg hbeta.le nu R) (by positivity)
  have hI : I ⊆ J := by
    intro t ht
    exact ⟨by dsimp [I] at ht; linarith [ht.1], ht.2.trans_lt hR1⟩
  have H : (∫⁻ t in J, entropyExcess beta (truncateTrial nu R) t+
      I.indicator (fun _ : ℝ => ENNReal.ofReal A) t) ≤ entropy beta nu := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    by_cases htI : t ∈ I
    · rw [indicator_of_mem htI]
      exact entropyExcess_truncate_add_gain_le hbeta nu hfinite R hR0 hR1 htI
    · rw [indicator_of_notMem htI, add_zero]
      exact entropyExcess_truncate_le hbeta.le nu R t
  rw [lintegral_add_left (entropyExcess_measurable beta (truncateTrial nu R))] at H
  have hmass : (∫⁻ t in J, I.indicator (fun _ : ℝ => ENNReal.ofReal A) t) =
      ENNReal.ofReal (truncationGain beta nu R/(4*beta^2*(1-(R : ℝ)))) := by
    rw [setLIntegral_indicator measurableSet_Icc, inter_eq_left.mpr hI,
      setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hA]
    congr 1
    dsimp [A]
    field_simp [hbeta.ne', sub_ne_zero.mpr hR1.ne']
    ring
  rw [hmass] at H
  exact H

theorem minimizer_tail_eq_zero_of_energy_bound (k : ℕ) {beta m L : ℝ}
    (hbeta : 0 < beta) (hL : 0 ≤ L) (nu : Trial)
    (hfinite : entropy beta nu ≠ ∞) (R : Overlap)
    (hR0 : (1 / 2 : ℝ) < (R : ℝ)) (hR1 : (R : ℝ) < 1)
    (hcoef : L < 1/(4*beta^2*(1-(R : ℝ))))
    (hmin : rawFunctional k beta m nu ≤ rawFunctional k beta m (truncateTrial nu R))
    (henergy : energy k beta m (truncateTrial nu R) ≤ energy k beta m nu+
      ENNReal.ofReal (truncationGain beta nu R*L)) :
    (nu : Measure Overlap) {q | (R : ℝ) < (q : ℝ)} = 0 := by
  apply (truncationGain_eq_zero_iff hbeta nu R).mp
  by_contra hne
  have hepos : 0 < truncationGain beta nu R :=
    lt_of_le_of_ne (truncationGain_nonneg hbeta.le nu R) (Ne.symm hne)
  have hrawfinite : rawFunctional k beta m nu ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨energy_ne_top k beta m nu, hfinite⟩
  have HS := entropy_truncate_add_gain_le hbeta nu hfinite R hR0 hR1
  have H : rawFunctional k beta m nu+
      ENNReal.ofReal (truncationGain beta nu R/(4*beta^2*(1-(R : ℝ)))) ≤
      rawFunctional k beta m nu+ENNReal.ofReal (truncationGain beta nu R*L) := by
    calc
      _ ≤ rawFunctional k beta m (truncateTrial nu R)+
          ENNReal.ofReal (truncationGain beta nu R/(4*beta^2*(1-(R : ℝ)))) :=
        add_le_add hmin le_rfl
      _ = energy k beta m (truncateTrial nu R)+(entropy beta (truncateTrial nu R)+
          ENNReal.ofReal (truncationGain beta nu R/(4*beta^2*(1-(R : ℝ))))) := by
        simp only [rawFunctional, add_assoc]
      _ ≤ energy k beta m (truncateTrial nu R)+entropy beta nu := add_le_add le_rfl HS
      _ ≤ (energy k beta m nu+ENNReal.ofReal (truncationGain beta nu R*L))+
          entropy beta nu := add_le_add henergy le_rfl
      _ = _ := by simp only [rawFunctional]; ac_rfl
  have HH := (ENNReal.add_le_add_iff_left hrawfinite).mp H
  have hleft : 0 ≤ truncationGain beta nu R/(4*beta^2*(1-(R : ℝ))) := by positivity
  have hright : 0 ≤ truncationGain beta nu R*L := mul_nonneg hepos.le hL
  have Hreal := ENNReal.toReal_mono (by simp) HH
  rw [ENNReal.toReal_ofReal hleft, ENNReal.toReal_ofReal hright] at Hreal
  have Hstrict := mul_lt_mul_of_pos_left hcoef hepos
  have heq : truncationGain beta nu R*(1/(4*beta^2*(1-(R : ℝ)))) =
      truncationGain beta nu R/(4*beta^2*(1-(R : ℝ))) := by ring
  rw [heq] at Hstrict
  linarith

theorem slice_covariance_deriv_bound (k : ℕ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv (Scalar.xiSlice k m) t‖ ≤ (k : ℝ)*(1-m^2) := by
  have hs := VariationalProofs.one_sub_sq_nonneg hm
  have hb0 : 0 ≤ m^2+(1-m^2)*t := add_nonneg (sq_nonneg m) (mul_nonneg hs ht.1)
  have hb1 : m^2+(1-m^2)*t ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hs]
  rw [VariationalProofs.deriv_xiSlice, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hs) (pow_nonneg hb0 _))]
  have H := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := k-1) hb0 hb1)
    (mul_nonneg (Nat.cast_nonneg k) hs)
  simpa only [mul_one] using H

theorem slice_covariance_truncate_diff_le (k : ℕ) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (R q : Overlap) :
    Scalar.xiSlice k m (q : ℝ)-Scalar.xiSlice k m (truncateOverlap R q : ℝ) ≤
      ((k : ℝ)*(1-m^2))*tailDisplacement R q := by
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc (0 : ℝ) 1) => (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt)
    (fun t ht => slice_covariance_deriv_bound k hm ht)
    (convex_Icc (0 : ℝ) 1) (truncateOverlap R q).property q.property
  have hdisp : (q : ℝ)-(truncateOverlap R q : ℝ) = tailDisplacement R q := by
    change (q : ℝ)-min (q : ℝ) (R : ℝ) = max ((q : ℝ)-(R : ℝ)) 0
    by_cases hq : (q : ℝ) ≤ (R : ℝ)
    · rw [min_eq_left hq, sub_self, max_eq_right (sub_nonpos.mpr hq)]
    · rw [min_eq_right (le_of_not_ge hq), max_eq_left (sub_nonneg.mpr (le_of_not_ge hq))]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hdisp,
    abs_of_nonneg (tailDisplacement_nonneg R q)] at H
  exact (le_abs_self _).trans H

theorem slice_covariance_integrable (k : ℕ) (m : ℝ) (nu : Trial) :
    Integrable (fun q : Overlap => Scalar.xiSlice k m (q : ℝ)) (nu : Measure Overlap) := by
  have hc : Continuous (fun q : Overlap => Scalar.xiSlice k m (q : ℝ)) := by
    unfold Scalar.xiSlice
    fun_prop
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hc.continuousOn.integrableOn_compact isCompact_univ (μ := (nu : Measure Overlap))

theorem slice_covariance_le_one (k : ℕ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (q : Overlap) : Scalar.xiSlice k m (q : ℝ) ≤ Scalar.xiSlice k m 1 := by
  have hs := VariationalProofs.one_sub_sq_nonneg hm
  have hb0 : 0 ≤ m^2+(1-m^2)*(q : ℝ) :=
    add_nonneg (sq_nonneg m) (mul_nonneg hs q.property.1)
  have hb1 : m^2+(1-m^2)*(q : ℝ) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left q.property.2 hs]
  have H := pow_le_one₀ (n := k) hb0 hb1
  have hbase : m^2+(1-m^2)*(1 : ℝ)=1 := by ring
  unfold Scalar.xiSlice
  rw [hbase, one_pow]
  linarith

theorem energy_truncate_le (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 ≤ beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) (R : Overlap) :
    energy k beta m (truncateTrial nu R) ≤ energy k beta m nu+
      ENNReal.ofReal (truncationGain beta nu R*((k : ℝ)*(1-m^2))) := by
  let xi := Scalar.xiSlice k m
  let L := (k : ℝ)*(1-m^2)
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg k) (VariationalProofs.one_sub_sq_nonneg hm)
  have hold := slice_covariance_integrable k m nu
  have hnew : Integrable (fun q => xi (truncateOverlap R q : ℝ)) (nu : Measure Overlap) :=
    (integrable_map_measure (by dsimp [xi, Scalar.xiSlice]; fun_prop)
      (continuous_truncateOverlap R).measurable.aemeasurable).mp
      (slice_covariance_integrable k m (truncateTrial nu R))
  have H := integral_mono (hold.sub hnew) ((tailDisplacement_integrable nu R).const_mul L)
    (fun q => slice_covariance_truncate_diff_le k hm R q)
  change (∫ q, xi (q : ℝ)-xi (truncateOverlap R q : ℝ) ∂(nu : Measure Overlap)) ≤
    ∫ q, L*tailDisplacement R q ∂(nu : Measure Overlap) at H
  rw [integral_sub hold hnew, integral_const_mul] at H
  have htransport : (∫ q : Overlap, xi (q : ℝ) ∂(truncateTrial nu R : Measure Overlap)) =
      ∫ q : Overlap, xi (truncateOverlap R q : ℝ) ∂(nu : Measure Overlap) := by
    unfold truncateTrial
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map (continuous_truncateOverlap R).measurable.aemeasurable (by dsimp [xi, Scalar.xiSlice]; fun_prop)
  have Hreal : beta*(xi 1-(∫ q : Overlap, xi (q : ℝ) ∂(truncateTrial nu R : Measure Overlap))) ≤
      beta*(xi 1-(∫ q : Overlap, xi (q : ℝ) ∂(nu : Measure Overlap)))+
        truncationGain beta nu R*L := by
    rw [htransport]
    unfold truncationGain
    nlinarith [mul_le_mul_of_nonneg_left H hbeta]
  have Hmax := integral_mono hold (integrable_const (xi 1)) (slice_covariance_le_one k hm)
  simp only [integral_const, probReal_univ, one_smul] at Hmax
  have ha : 0 ≤ beta*(xi 1-(∫ q : Overlap, xi (q : ℝ) ∂(nu : Measure Overlap))) :=
    mul_nonneg hbeta (sub_nonneg.mpr Hmax)
  have hb : 0 ≤ truncationGain beta nu R*L :=
    mul_nonneg (truncationGain_nonneg hbeta nu R) hL
  rw [energy_eq_ofReal k hk hbeta hm, energy_eq_ofReal k hk hbeta hm]
  exact (ENNReal.ofReal_le_ofReal Hreal).trans_eq (ENNReal.ofReal_add ha hb)

/-- A cutoff chosen from the fixed covariance and temperature works for every minimizer.
Neither support compactness below one nor a first-variation condition is assumed.
-/
theorem exists_uniform_minimizer_cutoff (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) :
    ∃ R : Overlap, (1 / 2 : ℝ) < (R : ℝ) ∧ (R : ℝ) < 1 ∧
      ∀ nu : Trial, (∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau) →
        (nu : Measure Overlap) {q | (R : ℝ) < (q : ℝ)} = 0 := by
  let L := (k : ℝ)*(1-m^2)
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg k) (VariationalProofs.one_sub_sq_nonneg hm)
  let den := 8*(beta^2+1)*(L+1)
  have hden : 0 < den := by dsimp [den]; positivity
  let s := 1/den
  have hs : 0 < s := by dsimp [s]; positivity
  have hslt : s < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ hden).mpr
    dsimp [den]
    nlinarith [sq_nonneg beta, mul_nonneg (sq_nonneg beta) hL]
  let R : Overlap := ⟨1-s, by constructor <;> linarith⟩
  have hR0 : (1 / 2 : ℝ) < (R : ℝ) := by change (1/2 : ℝ)<1-s; linarith
  have hR1 : (R : ℝ) < 1 := by change 1-s<1; linarith
  have hden2 : 0 < 4*beta^2*(1-(R : ℝ)) := by positivity
  have hcoef : L < 1/(4*beta^2*(1-(R : ℝ))) := by
    apply (lt_div_iff₀ hden2).mpr
    have heq : L*(4*beta^2*(1-(R : ℝ))) = (4*beta^2*L)/den := by
      dsimp [R, s]
      ring
    rw [heq]
    apply (div_lt_one hden).mpr
    dsimp [den]
    nlinarith [sq_nonneg beta, mul_nonneg (sq_nonneg beta) hL]
  refine ⟨R, hR0, hR1, ?_⟩
  intro nu hmin
  have hrawfinite : rawFunctional k beta m nu ≠ ∞ :=
    ne_top_of_le_ne_top (rawFunctional_dirac_zero_ne_top k beta m)
      (hmin (diracTrial ⟨0, by norm_num⟩))
  have hfinite : entropy beta nu ≠ ∞ := (ENNReal.add_ne_top.mp hrawfinite).2
  exact minimizer_tail_eq_zero_of_energy_bound k hbeta hL nu hfinite R hR0 hR1 hcoef
    (hmin (truncateTrial nu R)) (energy_truncate_le k hk hbeta.le hm nu R)

theorem exists_uniform_minimizer_ae_cutoff (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      ∀ nu : Trial, (∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau) →
        ∀ᵐ (q : Overlap) ∂(nu : Measure Overlap), (q : ℝ) ≤ R := by
  obtain ⟨R, hR0, hR1, H⟩ := exists_uniform_minimizer_cutoff k hk hbeta hm
  refine ⟨(R : ℝ), by linarith, hR1, ?_⟩
  intro nu hmin
  rw [ae_iff]
  simpa only [not_le] using H nu hmin


end
end TensorPCA.NonRSLowerProofs.FiniteCS
