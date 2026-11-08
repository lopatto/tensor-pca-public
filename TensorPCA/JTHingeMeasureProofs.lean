-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTCurvatureMeasureProofs

/-! Finite Stieltjes hinge representation. The curvature measure has
CDF equal to the right profile slope, including its atom at zero. -/
@[expose] public section
namespace TensorPCA.JTHingeMeasureProofs
open Set Filter MeasureTheory
open scoped Topology ENNReal
open JTCurvatureMeasureProofs JTProfileRepresentationProofs JTObstacleProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem integral_step_eq_hinge {s t : ℝ} (hs : s ≤ 1) (ht : t ≤ 1) :
    (∫ v, (if s ≤ v then (1 : ℝ) else 0) ∂volume.restrict (Ioc t 1)) = hinge s t := by
  have heq : (fun v : ℝ => if s ≤ v then (1 : ℝ) else 0) =ᵐ[volume.restrict (Ioc t 1)]
      (Ioi s).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [(ae_restrict_of_ae
      (show ∀ᵐ v : ℝ ∂volume, v ≠ s from by simp [ae_iff]))] with v hne
    simp only [indicator,mem_Ioi]
    split_ifs <;> first | rfl | (exfalso; grind)
  rw [integral_congr_ae heq,integral_indicator_const (1 : ℝ) measurableSet_Ioi,
    smul_eq_mul,mul_one,
    measureReal_restrict_apply measurableSet_Ioi,inter_comm,Ioc_inter_Ioi]
  rw [Real.volume_real_Ioc_of_le (max_le ht hs)]
  rfl

theorem finite_hinge_representation (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ s ∂μ, s ≤ 1) {t : ℝ} (ht : t ≤ 1) :
    (∫ s, hinge s t ∂μ) = ∫ v in t..1, μ.real (Iic v) := by
  let F : ℝ × ℝ → ℝ := fun z => if z.2 ≤ z.1 then 1 else 0
  have hm : Measurable F :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const measurable_const
  have hi : Integrable F ((volume.restrict (Ioc t 1)).prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by dsimp [F]; split_ifs <;> norm_num)
  have H := integral_integral_swap (f := fun v s => F (v,s))
    (by convert hi using 1; ext z; rfl)
  have hleft : (∫ v, ∫ s, F (v,s) ∂μ ∂volume.restrict (Ioc t 1)) =
      ∫ v in t..1, μ.real (Iic v) := by
    rw [intervalIntegral.integral_of_le ht]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by
      change (∫ s, (Iic v).indicator (fun _ => (1 : ℝ)) s ∂μ) = _
      simpa only [smul_eq_mul,mul_one] using integral_indicator_const (μ := μ) (1 : ℝ) measurableSet_Iic)
  have hright : (∫ s, ∫ v, F (v,s) ∂volume.restrict (Ioc t 1) ∂μ) = ∫ s, hinge s t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hsupp] with s hs
    exact integral_step_eq_hinge hs ht
  exact hright.symm.trans (H.symm.trans hleft)

theorem curvatureMeasure_real_Iic {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) {v : ℝ} (hv : 0 ≤ v) :
    (curvatureMeasure hp hr).real (Iic v) = profileRate p (min v r) := by
  rw [measureReal_def,curvatureMeasure,
    (curvatureStieltjes hp hr).measure_Iic (curvatureStieltjes_atBot hp hr)]
  simp only [curvatureStieltjes,curvatureCDF,ite_eq_right (not_lt.mpr hv),sub_zero]
  exact ENNReal.toReal_ofReal (profileRate_nonneg hp ((min_le_right v r).trans_lt hr.2))

theorem integral_hinge_curvature {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r t : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s, hinge s t ∂curvatureMeasure hp hr) =
      ∫ v in t..1, profileRate p (min v r) := by
  rw [finite_hinge_representation (curvatureMeasure hp hr)
    ((curvatureMeasure_ae_mem hp hr).mono (fun s hs => hs.2.trans hr.2.le)) ht.2]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le ht.2] at hv
  exact curvatureMeasure_real_Iic hp hr (ht.1.trans hv.1)

theorem truncatedRate_intervalIntegrable {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun v => profileRate p (min v r)) volume a b := by
  apply ((curvatureCDF_monotone hp hr).intervalIntegrable (a := a) (b := b)).congr
  intro v hv
  have hv0 : 0 ≤ v := (le_min ha hb).trans hv.1.le
  simp only [curvatureCDF,ite_eq_right (not_lt.mpr hv0)]

theorem integral_profileRate_terminal {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ v in t..1, profileRate p v) = p t-p 1 := by
  have h0t := (profileRate_intervalIntegrable hp).mono_set (by
    rw [uIcc_of_le ht.1,uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Icc_subset_Icc le_rfl ht.2)
  have H := intervalIntegral.integral_interval_sub_left h0t (profileRate_intervalIntegrable hp)
  rw [integral_profileRate hp,intervalIntegral.integral_symm t (1 : ℝ)] at H
  have Ht := profile_eq_initial_sub_integral_rate hp ht
  linarith

theorem integral_hinge_curvature_bounds {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r t : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (∫ s, hinge s t ∂curvatureMeasure hp hr) ∧
      (∫ s, hinge s t ∂curvatureMeasure hp hr) ≤ p t-p 1 := by
  rw [integral_hinge_curvature hp hr ht]
  refine ⟨intervalIntegral.integral_nonneg ht.2 (fun v _ =>
    profileRate_nonneg hp ((min_le_right v r).trans_lt hr.2)),?_⟩
  rw [← integral_profileRate_terminal hp ht]
  apply intervalIntegral.integral_mono_on_of_le_Ioo ht.2
    (truncatedRate_intervalIntegrable hp hr ht.1 (by norm_num))
    ((profileRate_intervalIntegrable hp).mono_set (by
      rw [uIcc_of_le ht.2,uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Icc_subset_Icc ht.1 le_rfl))
  intro v hv
  exact profileRate_monotone hp ((min_le_right v r).trans_lt hr.2) hv.2 (min_le_left v r)

theorem continuousOn_integral_hinge_curvature {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    ContinuousOn (fun t => ∫ s, hinge s t ∂curvatureMeasure hp hr) (Icc (0 : ℝ) 1) := by
  have hI : IntegrableOn (fun v => profileRate p (min v r)) (uIcc (0 : ℝ) 1) volume := by
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (truncatedRate_intervalIntegrable hp hr (by norm_num) (by norm_num))
  have hc := intervalIntegral.continuousOn_primitive_interval_left hI
  rw [uIcc_of_le zero_le_one] at hc
  exact hc.congr (fun t ht => integral_hinge_curvature hp hr ht)

theorem integral_hinge_curvature_tendsto {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ico (0 : ℝ) 1)
    (hrlim : Tendsto r atTop (𝓝 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => ∫ s, hinge s t ∂curvatureMeasure hp (hr n)) atTop (𝓝 (p t-p 1)) := by
  have hI : IntervalIntegrable (profileRate p) volume t 1 :=
    (profileRate_intervalIntegrable hp).mono_set (by
      rw [uIcc_of_le ht.2,uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Icc_subset_Icc ht.1 le_rfl)
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun v => profileRate p (min v (r n)))
      (volume.restrict (Ioc t 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).mp
      (truncatedRate_intervalIntegrable hp (hr n) ht.1 (by norm_num))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ v ∂volume.restrict (Ioc t 1),
      ‖profileRate p (min v (r n))‖ ≤ profileRate p v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (show ∀ᵐ v : ℝ ∂volume, v ≠ 1 from by simp [ae_iff]))] with v hv hne
    have hvlt : v < 1 := lt_of_le_of_ne hv.2 hne
    rw [Real.norm_of_nonneg (profileRate_nonneg hp ((min_le_right v (r n)).trans_lt (hr n).2))]
    exact profileRate_monotone hp ((min_le_right v (r n)).trans_lt (hr n).2) hvlt (min_le_left _ _)
  have hlim : ∀ᵐ v ∂volume.restrict (Ioc t 1),
      Tendsto (fun n => profileRate p (min v (r n))) atTop (𝓝 (profileRate p v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (show ∀ᵐ v : ℝ ∂volume, v ≠ 1 from by simp [ae_iff]))] with v hv hne
    have hvlt : v < 1 := lt_of_le_of_ne hv.2 hne
    apply tendsto_const_nhds.congr'
    filter_upwards [hrlim.eventually (Ioi_mem_nhds hvlt)] with n hn
    rw [min_eq_left hn.le]
  have H := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc t 1))
    (profileRate p) hmeas ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).mp hI) hbound hlim
  have H' : Tendsto (fun n => ∫ v in t..1, profileRate p (min v (r n))) atTop
      (𝓝 (∫ v in t..1, profileRate p v)) := by
    simpa only [intervalIntegral.integral_of_le ht.2] using H
  simpa only [integral_hinge_curvature hp (hr _) ht,integral_profileRate_terminal hp ht] using H'


end
end TensorPCA.JTHingeMeasureProofs
