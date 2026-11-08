-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FourParameterReductionProofs

/-! A positive boundary coefficient excludes curvature at zero. For the slice
covariance the remaining contact set has at most one point, so a plateau and
one affine tail are cofinal in the full admissible class. Only minimization
above an existing competitor's positive terminal value is used. -/
@[expose] public section
namespace TensorPCA.NonRSSphericalGroundOneStepProofs
open Set Filter MeasureTheory
open scoped Topology ENNReal
open JTCurvatureMeasureProofs JTHingeMeasureProofs JTObstacleProofs
  JTGapCalculusProofs JTCurvatureComplementarityProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gap_zero_pos_of_boundary_pos {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hboundary : 0 < h ^ 2 + deriv xi 0)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ gap xi h p t) :
    0 < gap xi h p 0 := by
  have hzero := hgap 0 (by norm_num)
  by_contra hnot
  have heq : gap xi h p 0 = 0 := le_antisymm (le_of_not_gt hnot) hzero
  have hd : HasDerivAt (gap xi h p) (-(h ^ 2 + deriv xi 0)) 0 := by
    simpa only [intervalIntegral.integral_same, sub_zero] using hasDerivAt_gap hp hxi h 0
  have hslope : ∀ᶠ c : ℝ in 𝓝[>] 0,
      c⁻¹ * (gap xi h p c - gap xi h p 0) < 0 := by
    simpa only [smul_eq_mul, zero_add] using
      hd.tendsto_slope_zero_right.eventually (Iio_mem_nhds (neg_neg_of_pos hboundary))
  have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  have hsmall : ∀ᶠ c : ℝ in 𝓝[>] 0, c < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  obtain ⟨c, hc, hc1, hcslope⟩ := (hpos.and (hsmall.and hslope)).exists
  have hnonneg := hgap c ⟨hc.le, hc1.le⟩
  rw [heq, sub_zero] at hcslope
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hc.le) hnonneg) hcslope

theorem profile_eq_plateau_of_curvature {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : ∀ {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1),
      ∀ᵐ s ∂curvatureMeasure hp hr, s = q) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      p t = Scalar.fourParameterProfile (p 1) 0 b q t := by
  let R : ℝ := (q + 1) / 2
  have hR : R ∈ Ico (0 : ℝ) 1 := by
    dsimp [R]
    constructor <;> linarith [hq.1, hq.2]
  have hqR : q ≤ R := by dsimp [R]; linarith [hq.2]
  let μ := curvatureMeasure hp hR
  have hstable {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hRr : R ≤ r) :
      curvatureMeasure hp hr = μ := by
    calc
      curvatureMeasure hp hr = (curvatureMeasure hp hr).restrict (Iic R) := by
        symm
        apply Measure.restrict_eq_self_of_ae_mem
        exact (hsupp hr).mono (fun s hs => hs ▸ hqR)
      _ = μ := curvatureMeasure_restrict hp hR hr hRr
  have hprofile (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s, hinge s t ∂μ) = p t - p 1 := by
    let r := JTProfileCompactnessProofs.exhaustion
    have hr (n : ℕ) : r n ∈ Ico (0 : ℝ) 1 :=
      ⟨JTProfileCompactnessProofs.exhaustion_nonneg n, JTProfileCompactnessProofs.exhaustion_lt_one n⟩
    have hrlim : Tendsto r atTop (𝓝 1) := JTProfileCompactnessProofs.exhaustion_tendsto
    have H := integral_hinge_curvature_tendsto hp r hr hrlim ht
    have Hconst : Tendsto (fun n => ∫ s, hinge s t ∂curvatureMeasure hp (hr n))
        atTop (𝓝 (∫ s, hinge s t ∂μ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hrlim.eventually (Ioi_mem_nhds hR.2)] with n hn
      rw [hstable (hr n) hn.le]
    exact tendsto_nhds_unique Hconst H
  refine ⟨μ.real univ, measureReal_nonneg, ?_⟩
  intro t ht
  have Hint : (∫ s, hinge s t ∂μ) = μ.real univ * hinge q t := by
    calc
      _ = ∫ _ : ℝ, hinge q t ∂μ := integral_congr_ae ((hsupp hR).mono (fun s hs => hs ▸ rfl))
      _ = _ := by rw [integral_const]; rfl
  rw [hprofile t ht] at Hint
  unfold Scalar.fourParameterProfile
  unfold hinge at Hint
  linarith

theorem floor_minimizer_eq_plateau {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hcomp : StrictConvexOn ℝ (Ioo (0 : ℝ) 1)
      (fun t => (Real.sqrt (deriv (deriv xi) t))⁻¹))
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv xi) t) (h : ℝ)
    (hboundary : 0 < h ^ 2 + deriv xi 0)
    {eps : ℝ} (heps : 0 < eps) (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ q t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q) :
    ∃ delta b q : ℝ, Scalar.FourParameterAdmissible delta 0 b q ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p t = Scalar.fourParameterProfile delta 0 b q t := by
  classical
  have hG : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ gap xi h p s :=
    fun _ ht => JTConstrainedContactProofs.floor_minimizer_gap_nonneg hp hxi h eps hfloor hmin ht
  have hG0 := gap_zero_pos_of_boundary_pos hp hxi h hboundary hG
  have huniq {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
      (hGs : gap xi h p s = 0) (hGt : gap xi h p t = 0) : s = t :=
    JTConstrainedContactProofs.gap_contacts_unique hp hxi hcomp hpos h hG hs ht hGs hGt
  obtain ⟨q, hq, hall⟩ : ∃ q ∈ Ioo (0 : ℝ) 1,
      ∀ s ∈ Ioo (0 : ℝ) 1, gap xi h p s = 0 → s = q := by
    by_cases hex : ∃ q ∈ Ioo (0 : ℝ) 1, gap xi h p q = 0
    · obtain ⟨q, hq, hGq⟩ := hex
      exact ⟨q, hq, fun s hs hGs => huniq hs hq hGs hGq⟩
    · exact ⟨1 / 2, by norm_num, fun s hs hGs => False.elim (hex ⟨s, hs, hGs⟩)⟩
  have hsupp {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
      ∀ᵐ s ∂curvatureMeasure hp hr, s = q := by
    filter_upwards [curvatureMeasure_ae_mem hp hr,
      floor_minimizer_curvature_contact hp hxi h heps hfloor hmin hr] with s hs hGs
    have hs0 : 0 < s := by
      apply lt_of_le_of_ne hs.1
      intro heq
      subst s
      exact hG0.ne' hGs
    exact hall s ⟨hs0, hs.2.trans_lt hr.2⟩ hGs
  obtain ⟨b, hb, heq⟩ := profile_eq_plateau_of_curvature hp hq (fun hr => hsupp hr)
  exact ⟨p 1, b, q, ⟨hp.2.2.2 1 (by norm_num), le_rfl, hb, ⟨hq.1.le, hq.2.le⟩⟩, heq⟩

theorem xiSlice_boundary_pos (k : ℕ) (hk : 3 ≤ k) {m : ℝ}
    (hm0 : 0 < |m|) (hm1 : |m| < 1) (h : ℝ) :
    0 < h ^ 2 + deriv (Scalar.xiSlice k m) 0 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmne : m ≠ 0 := by intro hm; simpa [hm] using hm0
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hmne
  have hbeta : 0 < 1 - m ^ 2 := by
    obtain ⟨hml, hmr⟩ := abs_lt.mp hm1
    nlinarith
  have hd : 0 < deriv (Scalar.xiSlice k m) 0 := by
    rw [VariationalProofs.deriv_xiSlice]
    simpa only [mul_zero, add_zero] using
      mul_pos (mul_pos hk0 hbeta) (pow_pos hm2 (k - 1))
  nlinarith [sq_nonneg h]

theorem xiSlice_cost_cofinal_oneStep (k : ℕ) (hk : 3 ≤ k) {m : ℝ}
    (hm0 : 0 < |m|) (hm1 : |m| < 1) (h : ℝ)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    ∃ delta b q : ℝ, Scalar.FourParameterAdmissible delta 0 b q ∧
      Scalar.parisiFunctional (Scalar.xiSlice k m) h (Scalar.fourParameterProfile delta 0 b q) ≤
        Scalar.parisiFunctional (Scalar.xiSlice k m) h p := by
  have heps : 0 < p 1 := hp.2.2.2 1 (by norm_num)
  have hfloor : ∀ t ∈ Icc (0 : ℝ) 1, p 1 ≤ p t :=
    fun t ht => hp.2.1 ht (by norm_num) ht.2
  obtain ⟨r, hr, hrfloor, hrmin⟩ :=
    JTFloorAttainmentProofs.exists_xiSlice_floor_minimizer k (by omega) hm1 h heps
  obtain ⟨delta, b, q, hAd, heq⟩ := floor_minimizer_eq_plateau hr
    (JTProfileBoundsProofs.xiSlice_secondDeriv_continuous k (by omega) m).continuousOn
    (JTModelCurvatureProofs.xiSlice_comparator_strictConvex k hk hm1)
    (fun t ht => JTProfileBoundsProofs.xiSlice_secondDeriv_pos k (by omega) hm1 ht)
    h (xiSlice_boundary_pos k hk hm0 hm1 h) heps hrfloor hrmin
  refine ⟨delta, b, q, hAd, ?_⟩
  rw [← FourParameterReductionProofs.parisiFunctional_congr_on_Icc (Scalar.xiSlice k m) h heq]
  exact hrmin p hp hfloor


end
end TensorPCA.NonRSSphericalGroundOneStepProofs
