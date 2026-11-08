-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTHingeMeasureProofs
public import TensorPCA.JTConstrainedStationarityProofs
public import TensorPCA.JTFloorAttainmentProofs

/-! Complementarity for finite curvature measures. All integrals
are proved integrable from finite mass and compact support. -/
@[expose] public section
namespace TensorPCA.JTCurvatureComplementarityProofs
open Set Filter MeasureTheory
open scoped Topology ENNReal
open JTCurvatureMeasureProofs JTHingeMeasureProofs JTObstacleProofs
open JTGapCalculusProofs JTOptimalityProofs JTProfileRepresentationProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem integrable_of_continuous_curvature {p f : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hf : Continuous f) :
    Integrable f (curvatureMeasure hp hr) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) r) hf.continuousOn
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    ((curvatureMeasure_ae_mem hp hr).mono (fun s hs => hC s hs))

theorem integral_firstVariation_hinge {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    firstVariation xi h p (fun t => ∫ s, hinge s t ∂curvatureMeasure hp hr) =
      ∫ s, gap xi h p s ∂curvatureMeasure hp hr := by
  let μ := curvatureMeasure hp hr
  let w := extendedWeight xi p
  have hw : Continuous w := continuous_extendedWeight hp hxi
  let F : ℝ × ℝ → ℝ := fun z => w z.1*hinge z.2 z.1
  have hm : Continuous F := by dsimp [F,hinge]; fun_prop
  obtain ⟨W,hW⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1) hw.continuousOn
  have hi : Integrable F ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
    apply (integrable_const W).mono' hm.aestronglyMeasurable
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc),
      Measure.quasiMeasurePreserving_snd.ae (curvatureMeasure_ae_mem hp hr)] with z ht hs
    have hhinge : 0 ≤ hinge z.2 z.1 := hinge_nonneg (hs.2.trans hr.2.le) ht.2
    have hhinge1 : hinge z.2 z.1 ≤ 1 := by
      dsimp [hinge]; linarith [le_max_left z.1 z.2,ht.1]
    calc
      ‖F z‖ = ‖w z.1‖*hinge z.2 z.1 := by
        change ‖w z.1*hinge z.2 z.1‖ = _
        rw [norm_mul,Real.norm_of_nonneg hhinge]
      _ ≤ ‖w z.1‖ := mul_le_of_le_one_right (norm_nonneg _) hhinge1
      _ ≤ W := hW _ ⟨ht.1.le,ht.2⟩
  have H := integral_integral_swap (f := fun t s => F (t,s))
    (by convert hi using 1; ext z; rfl)
  have hRint : Integrable (fun s => ∫ t in (0 : ℝ)..1, w t*hinge s t) μ := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,F] using hi.integral_prod_right
  have hhint : Integrable (fun s => hinge s 0) μ :=
    integrable_of_continuous_curvature hp hr (by dsimp [hinge]; fun_prop)
  have hswap : (∫ t in (0 : ℝ)..1, w t*(∫ s, hinge s t ∂μ)) =
      ∫ s, (∫ t in (0 : ℝ)..1, w t*hinge s t) ∂μ := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,F,integral_const_mul] using H
  unfold firstVariation
  have hweight : (∫ t in (0 : ℝ)..1,
      (deriv (deriv xi) t-1/(p t)^2)*(∫ s, hinge s t ∂μ)) =
      ∫ t in (0 : ℝ)..1, w t*(∫ s, hinge s t ∂μ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change (deriv (deriv xi) t-1/(p t)^2)*(∫ s, hinge s t ∂μ) = w t*(∫ s, hinge s t ∂μ)
    rw [show w t = deriv (deriv xi) t-1/(p t)^2 from
      extendedWeight_eq (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)]
  rw [hweight,hswap,← integral_const_mul,
    ← integral_add (hhint.const_mul (h^2+deriv xi 0)) hRint]
  apply integral_congr_ae
  filter_upwards [curvatureMeasure_ae_mem hp hr] with s hs
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans hr.2.le⟩
  rw [gap_eq_obstacleGap hp hxi h hs1]
  unfold obstacleGap firstVariation
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change w t*hinge s t = (deriv (deriv xi) t-1/(p t)^2)*hinge s t
  rw [show w t = deriv (deriv xi) t-1/(p t)^2 from
    extendedWeight_eq (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)]

theorem curvatureMeasure_restrict {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r s : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hs : s ∈ Ico (0 : ℝ) 1) (hrs : r ≤ s) :
    (curvatureMeasure hp hs).restrict (Iic r) = curvatureMeasure hp hr := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.restrict_apply measurableSet_Iic,Iic_inter_Iic]
  simp only [curvatureMeasure,(curvatureStieltjes hp hs).measure_Iic (curvatureStieltjes_atBot hp hs),
    (curvatureStieltjes hp hr).measure_Iic (curvatureStieltjes_atBot hp hr),sub_zero]
  congr 1
  change curvatureCDF p s (min t r) = curvatureCDF p r t
  by_cases ht : t < 0
  · simp only [curvatureCDF,ite_eq_left ht,ite_eq_left ((min_le_left t r).trans_lt ht)]
  · have hmin : 0 ≤ min t r := le_min (le_of_not_gt ht) hr.1
    simp only [curvatureCDF,ite_eq_right ht,ite_eq_right (not_lt.mpr hmin)]
    rw [min_eq_left ((min_le_right t r).trans hrs)]

theorem firstVariation_eq_extendedWeight (xi : ℝ → ℝ) (h : ℝ) (p q : ℝ → ℝ) :
    firstVariation xi h p q = (h^2+deriv xi 0)*q 0+
      ∫ t in (0 : ℝ)..1, extendedWeight xi p t*q t := by
  unfold firstVariation
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change _*q t = extendedWeight xi p t*q t
  rw [extendedWeight_eq (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)]

theorem firstVariation_hinge_tendsto {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ico (0 : ℝ) 1) (hrlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => firstVariation xi h p (fun t => ∫ s, hinge s t ∂curvatureMeasure hp (hr n)))
      atTop (𝓝 (firstVariation xi h p (fun t => p t-p 1))) := by
  let q : ℕ → ℝ → ℝ := fun n t => ∫ s, hinge s t ∂curvatureMeasure hp (hr n)
  let w := extendedWeight xi p
  have hw : Continuous w := continuous_extendedWeight hp hxi
  have hqcont (n : ℕ) : ContinuousOn (q n) (Icc (0 : ℝ) 1) :=
    continuousOn_integral_hinge_curvature hp (hr n)
  obtain ⟨W,hW⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1) hw.continuousOn
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by norm_num))
  have hqbound (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ q n t ∧ q n t ≤ p 0 := by
    have H := integral_hinge_curvature_bounds hp (hr n) ht
    exact ⟨H.1,H.2.trans (by linarith [hp.2.1 (by norm_num) ht ht.1,hp.2.2.2 1 (by norm_num)])⟩
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun t => w t*q n t)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((hw.continuousOn.mul (hqcont n)).intervalIntegrable_of_Icc zero_le_one)).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), ‖w t*q n t‖ ≤ W*p 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2⟩
    rw [norm_mul,Real.norm_of_nonneg (hqbound n t ht1).1]
    exact mul_le_mul (hW t ht1) (hqbound n t ht1).2 (hqbound n t ht1).1 hW0
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun n => w t*q n t) atTop (𝓝 (w t*(p t-p 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (integral_hinge_curvature_tendsto hp r hr hrlim ⟨ht.1.le,ht.2⟩).const_mul _
  have H := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ => W*p 0) hmeas (integrable_const _) hbound hlim
  have H' : Tendsto (fun n => ∫ t in (0 : ℝ)..1, w t*q n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, w t*(p t-p 1))) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using H
  simpa only [firstVariation_eq_extendedWeight] using
    ((integral_hinge_curvature_tendsto hp r hr hrlim (t := 0) (by norm_num)).const_mul
      (h^2+deriv xi 0)).add H'

theorem firstVariation_sub_const {xi p q : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Icc (0 : ℝ) 1)) (h c : ℝ) :
    firstVariation xi h p (fun t => q t-c) = firstVariation xi h p q-
      c*((h^2+deriv xi 0)+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2) := by
  have hw : ContinuousOn (fun t => deriv (deriv xi) t-1/(p t)^2) (Icc (0 : ℝ) 1) :=
    hxi.sub (continuousOn_const.div (hp.1.pow 2) (fun t ht => pow_ne_zero _ (hp.2.2.2 t ht).ne'))
  have heq : (fun t => (deriv (deriv xi) t-1/(p t)^2)*(q t-c)) =
      (fun t => (deriv (deriv xi) t-1/(p t)^2)*q t-(deriv (deriv xi) t-1/(p t)^2)*c) := by
    ext t; ring
  simp only [firstVariation,heq]
  have hI1 : IntervalIntegrable (fun t => (deriv (deriv xi) t-1/(p t)^2)*q t) volume (0 : ℝ) 1 :=
    (hw.mul hq).intervalIntegrable_of_Icc zero_le_one
  have hI2 : IntervalIntegrable (fun t => (deriv (deriv xi) t-1/(p t)^2)*c) volume (0 : ℝ) 1 :=
    (hw.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_sub hI1 hI2,intervalIntegral.integral_mul_const]
  ring

theorem floor_minimizer_curvature_contact {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    {eps : ℝ} (heps : 0 < eps) (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ q t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ s ∂curvatureMeasure hp hr, gap xi h p s = 0 := by
  have hG : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ gap xi h p s :=
    fun _ ht => JTConstrainedContactProofs.floor_minimizer_gap_nonneg hp hxi h eps hfloor hmin ht
  have hGcont : Continuous (gap xi h p) := continuous_iff_continuousAt.mpr
    (fun s => (hasDerivAt_gap hp hxi h s).continuousAt)
  have hGnonneg {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : 0 ≤ᵐ[curvatureMeasure hp hs] gap xi h p :=
    (curvatureMeasure_ae_mem hp hs).mono (fun t ht => hG t ⟨ht.1,ht.2.trans hs.2.le⟩)
  have hGint {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : Integrable (gap xi h p) (curvatureMeasure hp hs) :=
    integrable_of_continuous_curvature hp hs hGcont
  let E := (h^2+deriv xi 0)+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2
  have hE : 0 ≤ E := JTConstrainedStationarityProofs.floor_minimizer_constant_euler_nonneg hp hxi h eps hfloor hmin
  have hscale := JTConstrainedStationarityProofs.floor_minimizer_scaling_euler hp hxi h heps hfloor hmin
  have hlimitval : firstVariation xi h p (fun t => p t-p 1) ≤ 0 := by
    rw [firstVariation_sub_const hp hxi hp.1 h (p 1)]
    rw [firstVariation_sub_const hp hxi hp.1 h eps] at hscale
    have H := mul_nonneg (sub_nonneg.mpr (hfloor 1 (by norm_num))) hE
    change 0 ≤ (p 1-eps)*E at H
    change firstVariation xi h p p-eps*E = 0 at hscale
    change firstVariation xi h p p-p 1*E ≤ 0
    nlinarith
  let R := JTProfileCompactnessProofs.exhaustion
  have hR (n : ℕ) : R n ∈ Ico (0 : ℝ) 1 :=
    ⟨JTProfileCompactnessProofs.exhaustion_nonneg n,JTProfileCompactnessProofs.exhaustion_lt_one n⟩
  have hRlim : Tendsto R atTop (𝓝 1) := JTProfileCompactnessProofs.exhaustion_tendsto
  have Hlim : Tendsto (fun n => ∫ s, gap xi h p s ∂curvatureMeasure hp (hR n)) atTop
      (𝓝 (firstVariation xi h p (fun t => p t-p 1))) := by
    simpa only [integral_firstVariation_hinge hp hxi h] using firstVariation_hinge_tendsto hp hxi h R hR hRlim
  have hle : (∫ s, gap xi h p s ∂curvatureMeasure hp hr) ≤
      firstVariation xi h p (fun t => p t-p 1) := by
    apply ge_of_tendsto Hlim
    filter_upwards [hRlim.eventually (Ioi_mem_nhds hr.2)] with n hn
    have hmeasure : curvatureMeasure hp hr ≤ curvatureMeasure hp (hR n) := by
      rw [← curvatureMeasure_restrict hp hr (hR n) hn.le]
      exact Measure.restrict_le_self
    exact integral_mono_measure hmeasure (hGnonneg (hR n)) (hGint (hR n))
  have Hzero : (∫ s, gap xi h p s ∂curvatureMeasure hp hr) = 0 :=
    le_antisymm (hle.trans hlimitval) (integral_nonneg_of_ae (hGnonneg hr))
  exact (integral_eq_zero_iff_of_nonneg_ae (hGnonneg hr) (hGint hr)).mp Hzero


end
end TensorPCA.JTCurvatureComplementarityProofs
