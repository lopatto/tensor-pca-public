-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTContactGeometryProofs

/-! Contact geometry for the constrained positive-floor variational problem.
Only the value of the gap at the right endpoint is needed; the Euler mass
identity may be an inequality when the floor constraint is active. -/
@[expose] public section
namespace TensorPCA.JTConstrainedContactProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem no_ordered_contacts_right_value {V D : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hV' : Differentiable ℝ (deriv V))
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ V t) (hV1 : V 1 = 0)
    (hD : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) D)
    (hzero : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv V) t = 0 ↔ D t = 0)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hVa : V a = 0) (hVb : V b = 0) (hab : a < b) : False := by
  have hda := JTContactGeometryProofs.contact_deriv_zero hnonneg ha hVa
  have hdb := JTContactGeometryProofs.contact_deriv_zero hnonneg hb hVb
  obtain ⟨u,v,hu,hv,huv,hdu,hdv⟩ :=
    JTContactGeometryProofs.two_deriv2_zeros_between hV hV' hab hVa hVb hda hdb
  obtain ⟨c,hc,hdc⟩ := exists_deriv_eq_zero hb.2 hV.continuous.continuousOn
    (hVb.trans hV1.symm)
  obtain ⟨w,hw,hdw⟩ := exists_deriv_eq_zero hc.1 hV'.continuous.continuousOn
    (hdb.trans hdc.symm)
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hu.1,hu.2.trans hb.2⟩
  have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hv.1,hv.2.trans hb.2⟩
  have hw01 : w ∈ Ioo (0 : ℝ) 1 := ⟨hb.1.trans hw.1,hw.2.trans hc.2⟩
  exact JTContactGeometryProofs.strictConvex_no_three_zeros hD hu01 hw01 huv
    (hv.2.trans hw.1) ((hzero u hu01).mp hdu) ((hzero v hv01).mp hdv)
      ((hzero w hw01).mp hdw)

theorem contacts_unique_right_value {V D : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hV' : Differentiable ℝ (deriv V))
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ V t) (hV1 : V 1 = 0)
    (hD : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) D)
    (hzero : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv V) t = 0 ↔ D t = 0)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hVa : V a = 0) (hVb : V b = 0) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (no_ordered_contacts_right_value hV hV' hnonneg hV1 hD hzero
      ha hb hVa hVb hab)
  · exact hab
  · exact False.elim (no_ordered_contacts_right_value hV hV' hnonneg hV1 hD hzero
      hb ha hVb hVa hab)

theorem gap_contacts_unique {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hcomp : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (fun t => (Real.sqrt (deriv (deriv xi) t))⁻¹))
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv xi) t) (h : ℝ)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ JTGapCalculusProofs.gap xi h p t)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hGa : JTGapCalculusProofs.gap xi h p a = 0)
    (hGb : JTGapCalculusProofs.gap xi h p b = 0) : a = b := by
  have hV : Differentiable ℝ (JTGapCalculusProofs.gap xi h p) :=
    fun t => (JTGapCalculusProofs.hasDerivAt_gap hp hxi h t).differentiableAt
  have hV' : Differentiable ℝ (deriv (JTGapCalculusProofs.gap xi h p)) :=
    fun t => (JTGapCalculusProofs.hasDerivAt_deriv_gap hp hxi h t).differentiableAt
  have hD := hcomp.sub_concaveOn (hp.2.2.1.subset Ioo_subset_Icc_self (convex_Ioo 0 1))
  apply contacts_unique_right_value hV hV' hnonneg (JTGapCalculusProofs.gap_one _ _ h) hD
    ?_ ha hb hGa hGb
  intro t ht
  rw [(JTGapCalculusProofs.hasDerivAt_deriv_gap hp hxi h t).deriv,
    JTGapCalculusProofs.extendedWeight_eq ⟨ht.1.le,ht.2.le⟩,neg_eq_zero]
  exact JTContactGeometryProofs.weight_zero_iff_comparator_zero (hpos t ht)
    (hp.2.2.2 t ⟨ht.1.le,ht.2.le⟩)

theorem floor_minimizer_hinge_nonneg {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h eps : ℝ)
    (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ r t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    0 ≤ JTOptimalityProofs.firstVariation xi h p (JTObstacleProofs.hinge q) := by
  let F := fun c : ℝ => Scalar.parisiFunctional xi h
    (fun t => p t+c*JTObstacleProofs.hinge q t)
  have hd : HasDerivAt F (JTOptimalityProofs.firstVariation xi h p (JTObstacleProofs.hinge q)) 0 :=
    JTOptimalityProofs.hasDerivAt_firstVariation hp hxi (JTObstacleProofs.hinge_continuous q).continuousOn h
  have hF0 : F 0 = Scalar.parisiFunctional xi h p := by
    change Scalar.parisiFunctional xi h (fun t => p t+0*JTObstacleProofs.hinge q t) = _
    simp only [zero_mul,add_zero]
  by_contra hnot
  have hneg := lt_of_not_ge hnot
  have hslope : ∀ᶠ c : ℝ in 𝓝[>] 0, c⁻¹*(F c-F 0) < 0 := by
    simpa only [smul_eq_mul,zero_add] using hd.tendsto_slope_zero_right.eventually (Iio_mem_nhds hneg)
  have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  obtain ⟨c,hc,hcslope⟩ := (hpos.and hslope).exists
  have hAd := JTObstacleProofs.admissibleProfile_add_hinge hp hq hc.le
  have hfloorc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      eps ≤ p t+c*JTObstacleProofs.hinge q t :=
    (hfloor t ht).trans (le_add_of_nonneg_right (mul_nonneg hc.le (JTObstacleProofs.hinge_nonneg hq.2 ht.2)))
  have hF : F 0 ≤ F c := by rw [hF0]; exact hmin _ hAd hfloorc
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hc.le) (sub_nonneg.mpr hF)) hcslope

theorem floor_minimizer_gap_nonneg {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h eps : ℝ)
    (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ r t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ JTGapCalculusProofs.gap xi h p q := by
  rw [JTGapCalculusProofs.gap_eq_obstacleGap hp hxi h hq]
  exact floor_minimizer_hinge_nonneg hp hxi h eps hfloor hmin hq


end
end TensorPCA.JTConstrainedContactProofs
