-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTCurvatureComplementarityProofs

/-! A curvature measure supported at zero and one interior point gives exactly
the original four-parameter profile, with its positive terminal value. -/
@[expose] public section
namespace TensorPCA.JTOneKnotProfileProofs
open Set Filter MeasureTheory
open scoped Topology ENNReal
open JTCurvatureMeasureProofs JTHingeMeasureProofs JTObstacleProofs
open JTGapCalculusProofs JTOptimalityProofs JTProfileRepresentationProofs
open JTCurvatureComplementarityProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem integral_eq_two_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] {q : ℝ} (hq : q ≠ 0)
    (hsupp : ∀ᵐ s ∂μ, s = 0 ∨ s = q) (f : ℝ → ℝ) :
    (∫ s, f s ∂μ) = μ.real {0}*f 0+μ.real {q}*f q := by
  have heq : f =ᵐ[μ] (fun s => ({0} : Set ℝ).indicator (fun _ => f 0) s+
      ({q} : Set ℝ).indicator (fun _ => f q) s) := by
    filter_upwards [hsupp] with s hs
    rcases hs with rfl | rfl
    · simp only [indicator,mem_singleton_iff,ite_true,ite_eq_right (Ne.symm hq),add_zero]
    · simp only [indicator,mem_singleton_iff,ite_true,ite_eq_right hq,zero_add]
  rw [integral_congr_ae heq,integral_add
    ((integrable_const (f 0)).indicator (measurableSet_singleton 0))
    ((integrable_const (f q)).indicator (measurableSet_singleton q)),
    integral_indicator_const _ (measurableSet_singleton 0),integral_indicator_const _ (measurableSet_singleton q)]
  rfl

theorem profile_eq_one_knot_of_curvature {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : ∀ {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1),
      ∀ᵐ s ∂curvatureMeasure hp hr, s = 0 ∨ s = q) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      p t = Scalar.fourParameterProfile (p 1) a b q t := by
  let R : ℝ := (q+1)/2
  have hR : R ∈ Ico (0 : ℝ) 1 := by dsimp [R]; constructor <;> linarith [hq.1,hq.2]
  have hqR : q ≤ R := by dsimp [R]; linarith [hq.2]
  let μ := curvatureMeasure hp hR
  have hstable {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hRr : R ≤ r) : curvatureMeasure hp hr = μ := by
    calc
      curvatureMeasure hp hr = (curvatureMeasure hp hr).restrict (Iic R) := by
        symm
        apply Measure.restrict_eq_self_of_ae_mem
        filter_upwards [hsupp hr] with s hs
        rcases hs with rfl | rfl
        · exact hR.1
        · exact hqR
      _ = μ := curvatureMeasure_restrict hp hR hr hRr
  have hprofile (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (∫ s, hinge s t ∂μ) = p t-p 1 := by
    let r := JTProfileCompactnessProofs.exhaustion
    have hr (n : ℕ) : r n ∈ Ico (0 : ℝ) 1 :=
      ⟨JTProfileCompactnessProofs.exhaustion_nonneg n,JTProfileCompactnessProofs.exhaustion_lt_one n⟩
    have hrlim : Tendsto r atTop (𝓝 1) := JTProfileCompactnessProofs.exhaustion_tendsto
    have H := integral_hinge_curvature_tendsto hp r hr hrlim ht
    have Hconst : Tendsto (fun n => ∫ s, hinge s t ∂curvatureMeasure hp (hr n))
        atTop (𝓝 (∫ s, hinge s t ∂μ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hrlim.eventually (Ioi_mem_nhds hR.2)] with n hn
      rw [hstable (hr n) hn.le]
    exact tendsto_nhds_unique Hconst H
  refine ⟨μ.real {0},μ.real {q},measureReal_nonneg,measureReal_nonneg,?_⟩
  intro t ht
  have H := integral_eq_two_atoms μ hq.1.ne' (hsupp hR) (fun s => hinge s t)
  rw [hprofile t ht] at H
  simp only [hinge,max_eq_left ht.1] at H
  unfold Scalar.fourParameterProfile
  linarith

theorem floor_minimizer_eq_fourParameter {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hcomp : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (fun t => (Real.sqrt (deriv (deriv xi) t))⁻¹))
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv xi) t) (h : ℝ)
    {eps : ℝ} (heps : 0 < eps) (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ q t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q) :
    ∃ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p t = Scalar.fourParameterProfile delta a b q t := by
  classical
  have hG : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ gap xi h p s :=
    fun _ ht => JTConstrainedContactProofs.floor_minimizer_gap_nonneg hp hxi h eps hfloor hmin ht
  have huniq {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
      (hGs : gap xi h p s = 0) (hGt : gap xi h p t = 0) : s = t :=
    JTConstrainedContactProofs.gap_contacts_unique hp hxi hcomp hpos h hG hs ht hGs hGt
  obtain ⟨q,hq,hall⟩ : ∃ q ∈ Ioo (0 : ℝ) 1,
      ∀ s ∈ Ioo (0 : ℝ) 1, gap xi h p s = 0 → s = q := by
    by_cases hex : ∃ q ∈ Ioo (0 : ℝ) 1, gap xi h p q = 0
    · obtain ⟨q,hq,hGq⟩ := hex
      exact ⟨q,hq,fun s hs hGs => huniq hs hq hGs hGq⟩
    · exact ⟨1/2,by norm_num,fun s hs hGs => False.elim (hex ⟨s,hs,hGs⟩)⟩
  have hsupp {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
      ∀ᵐ s ∂curvatureMeasure hp hr, s = 0 ∨ s = q := by
    filter_upwards [curvatureMeasure_ae_mem hp hr,
      floor_minimizer_curvature_contact hp hxi h heps hfloor hmin hr] with s hs hGs
    by_cases hs0 : s = 0
    · exact Or.inl hs0
    · exact Or.inr (hall s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),hs.2.trans_lt hr.2⟩ hGs)
  obtain ⟨a,b,ha,hb,heq⟩ := profile_eq_one_knot_of_curvature hp hq (fun hr => hsupp hr)
  exact ⟨p 1,a,b,q,⟨hp.2.2.2 1 (by norm_num),ha,hb,⟨hq.1.le,hq.2.le⟩⟩,heq⟩

theorem xiSlice_floor_minimizer_eq_fourParameter (k : ℕ) (hk : 3 ≤ k) {m : ℝ}
    (hm : |m| < 1) {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) (h : ℝ)
    {eps : ℝ} (heps : 0 < eps) (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ q t) →
      Scalar.parisiFunctional (Scalar.xiSlice k m) h p ≤ Scalar.parisiFunctional (Scalar.xiSlice k m) h q) :
    ∃ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p t = Scalar.fourParameterProfile delta a b q t := by
  apply floor_minimizer_eq_fourParameter hp
    (JTProfileBoundsProofs.xiSlice_secondDeriv_continuous k (by omega) m).continuousOn
    (JTModelCurvatureProofs.xiSlice_comparator_strictConvex k hk hm)
    (fun t ht => JTProfileBoundsProofs.xiSlice_secondDeriv_pos k (by omega) hm ht) h heps hfloor hmin


end
end TensorPCA.JTOneKnotProfileProofs
