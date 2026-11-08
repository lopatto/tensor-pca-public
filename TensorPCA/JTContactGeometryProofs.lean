-- SPDX-License-Identifier: Apache-2.0
-- Narrow adaptation of the Rolle/contact geometry proof from
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/ContactGeometry.lean
-- The fixed endpoint is changed from0 to1; no source thermodynamic hypotheses
-- or finite-temperature minimizer declarations are imported.
module
public import TensorPCA.JTGapCalculusProofs
public import TensorPCA.JTModelCurvatureProofs
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle

@[expose] public section
namespace TensorPCA.JTContactGeometryProofs
open Set Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem strictConvex_no_three_zeros {D : ℝ → ℝ} {s : Set ℝ}
    (hD : StrictConvexOn ℝ s D) {x y z : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z)
    (hDx : D x = 0) (hDy : D y = 0) (hDz : D z = 0) : False := by
  have hy : y ∈ openSegment ℝ x z := by
    rw [openSegment_eq_Ioo (hxy.trans hyz)]
    exact ⟨hxy,hyz⟩
  have hlt := hD.lt_on_openSegment hx hz (hxy.trans hyz).ne hy
  rw [hDx,hDy,hDz] at hlt
  norm_num at hlt

theorem contact_deriv_zero {V : ℝ → ℝ}
    (hnonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ V r) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hVq : V q = 0) : deriv V q = 0 := by
  have hmin : IsLocalMin V q := by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
    rw [hVq]
    exact hnonneg r ⟨hr.1.le,hr.2.le⟩
  exact hmin.deriv_eq_zero

theorem two_deriv2_zeros_between {V : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hV' : Differentiable ℝ (deriv V))
    {a b : ℝ} (hab : a < b) (hVa : V a = 0) (hVb : V b = 0)
    (hda : deriv V a = 0) (hdb : deriv V b = 0) :
    ∃ u v, u ∈ Ioo a b ∧ v ∈ Ioo a b ∧ u < v ∧
      deriv (deriv V) u = 0 ∧ deriv (deriv V) v = 0 := by
  obtain ⟨c,hc,hdc⟩ := exists_deriv_eq_zero hab hV.continuous.continuousOn
    (hVa.trans hVb.symm)
  obtain ⟨u,hu,hdu⟩ := exists_deriv_eq_zero hc.1 hV'.continuous.continuousOn
    (hda.trans hdc.symm)
  obtain ⟨v,hv,hdv⟩ := exists_deriv_eq_zero hc.2 hV'.continuous.continuousOn
    (hdc.trans hdb.symm)
  exact ⟨u,v,⟨hu.1,hu.2.trans hc.2⟩,⟨hc.1.trans hv.1,hv.2⟩,
    hu.2.trans hv.1,hdu,hdv⟩

theorem no_ordered_contacts_right_boundary {V D : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hV' : Differentiable ℝ (deriv V))
    (hnonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ V r)
    (hV1 : V 1 = 0) (hd1 : deriv V 1 = 0)
    (hD : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) D)
    (hzero : ∀ r ∈ Ioo (0 : ℝ) 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hVa : V a = 0) (hVb : V b = 0) (hab : a < b) : False := by
  have hda := contact_deriv_zero hnonneg ha hVa
  have hdb := contact_deriv_zero hnonneg hb hVb
  obtain ⟨u,v,hu,hv,huv,hdu,hdv⟩ :=
    two_deriv2_zeros_between hV hV' hb.2 hVb hV1 hdb hd1
  obtain ⟨w,hw,hdw⟩ := exists_deriv_eq_zero hab hV'.continuous.continuousOn
    (hda.trans hdb.symm)
  have hw01 : w ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hw.1,hw.2.trans hb.2⟩
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hb.1.trans hu.1,hu.2⟩
  have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨hb.1.trans hv.1,hv.2⟩
  exact strictConvex_no_three_zeros hD hw01 hv01 (hw.2.trans hu.1) huv
    ((hzero w hw01).mp hdw) ((hzero u hu01).mp hdu) ((hzero v hv01).mp hdv)

theorem contacts_unique_right_boundary {V D : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hV' : Differentiable ℝ (deriv V))
    (hnonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ V r)
    (hV1 : V 1 = 0) (hd1 : deriv V 1 = 0)
    (hD : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) D)
    (hzero : ∀ r ∈ Ioo (0 : ℝ) 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hVa : V a = 0) (hVb : V b = 0) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (no_ordered_contacts_right_boundary hV hV' hnonneg hV1 hd1 hD hzero
      ha hb hVa hVb hab)
  · exact hab
  · exact False.elim (no_ordered_contacts_right_boundary hV hV' hnonneg hV1 hd1 hD hzero
      hb ha hVb hVa hab)

theorem weight_zero_iff_comparator_zero {v p : ℝ} (hv : 0 < v) (hp : 0 < p) :
    v-1/p^2 = 0 ↔ (Real.sqrt v)⁻¹-p = 0 := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsq : (Real.sqrt v)^2 = v := Real.sq_sqrt hv.le
  constructor
  · intro hzero
    have he : v*p^2 = 1 := by
      field_simp [hp.ne'] at hzero
      nlinarith
    have he2 : (p*Real.sqrt v)^2 = 1 := by rw [mul_pow,hsq]; nlinarith [he]
    have he1 : p*Real.sqrt v = 1 := by nlinarith [mul_pos hp hs]
    field_simp [hs.ne']
    nlinarith
  · intro hzero
    have he1 : p*Real.sqrt v = 1 := by
      field_simp [hs.ne'] at hzero
      nlinarith
    have he2 : v*p^2 = 1 := by
      have H := congrArg (fun x : ℝ => x^2) he1
      rw [mul_pow,hsq] at H
      nlinarith
    field_simp [hp.ne']
    nlinarith

theorem slice_minimizer_interior_contacts_unique (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm : |m| < 1) {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) (h : ℝ)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      Scalar.parisiFunctional (Scalar.xiSlice k m) h p ≤
        Scalar.parisiFunctional (Scalar.xiSlice k m) h r)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hGa : JTGapCalculusProofs.gap (Scalar.xiSlice k m) h p a = 0)
    (hGb : JTGapCalculusProofs.gap (Scalar.xiSlice k m) h p b = 0) : a = b := by
  have hxi : ContinuousOn (deriv (deriv (Scalar.xiSlice k m))) (Icc (0 : ℝ) 1) := by
    rw [JTModelCurvatureProofs.secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
    unfold JTModelCurvatureProofs.shiftedPower
    fun_prop
  have hV : Differentiable ℝ (JTGapCalculusProofs.gap (Scalar.xiSlice k m) h p) :=
    fun t => (JTGapCalculusProofs.hasDerivAt_gap hp hxi h t).differentiableAt
  have hV' : Differentiable ℝ (deriv (JTGapCalculusProofs.gap (Scalar.xiSlice k m) h p)) :=
    fun t => (JTGapCalculusProofs.hasDerivAt_deriv_gap hp hxi h t).differentiableAt
  have hD := (JTModelCurvatureProofs.xiSlice_comparator_strictConvex k hk hm).sub_concaveOn
    (hp.2.2.1.subset Ioo_subset_Icc_self (convex_Ioo 0 1))
  apply contacts_unique_right_boundary hV hV'
    (fun t ht => JTGapCalculusProofs.minimizer_gap_nonneg hp hxi h hmin ht)
    (JTGapCalculusProofs.gap_one _ _ h)
    (JTGapCalculusProofs.minimizer_deriv_gap_one hp hxi h hmin) hD ?_ ha hb hGa hGb
  intro t ht
  rw [(JTGapCalculusProofs.hasDerivAt_deriv_gap hp hxi h t).deriv,
    JTGapCalculusProofs.extendedWeight_eq ⟨ht.1.le,ht.2.le⟩,neg_eq_zero]
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  have hv : 0 < deriv (deriv (Scalar.xiSlice k m)) t := by
    rw [JTModelCurvatureProofs.secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
    unfold JTModelCurvatureProofs.shiftedPower
    exact mul_pos
      (mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos hB))
      (pow_pos (add_pos_of_nonneg_of_pos (sq_nonneg m) (mul_pos hB ht.1)) _)
  exact weight_zero_iff_comparator_zero hv (hp.2.2.2 t ⟨ht.1.le,ht.2.le⟩)


end
end TensorPCA.JTContactGeometryProofs
