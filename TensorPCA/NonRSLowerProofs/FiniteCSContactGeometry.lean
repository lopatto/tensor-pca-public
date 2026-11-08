-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSCalculus
public import TensorPCA.NonRSLowerProofs.FiniteCSFirstVariation
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Data.Set.Card

/-! Three interior maxima of the true first-variation potential force three
ordered comparator zeros. This is the positive-boundary version of the Rolle
argument: it assumes no origin contact or stationarity at zero. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

-- Same strict-convexity argument as JTContactGeometryProofs, kept here to
-- avoid importing the unrelated zero-temperature obstacle/minimizer closure.
private theorem strictConvex_no_three_zeros {D : ℝ → ℝ} {s : Set ℝ}
    (hD : StrictConvexOn ℝ s D) {x y z : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z)
    (hDx : D x = 0) (hDy : D y = 0) (hDz : D z = 0) : False := by
  have hy : y ∈ openSegment ℝ x z := by
    rw [openSegment_eq_Ioo (hxy.trans hyz)]
    exact ⟨hxy, hyz⟩
  have hlt := hD.lt_on_openSegment hx hz (hxy.trans hyz).ne hy
  rw [hDx, hDy, hDz] at hlt
  norm_num at hlt

private theorem continuousOn_Icc_of_below_one {f : ℝ → ℝ}
    (hf : ∀ r ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ f r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) : ContinuousOn f (Icc a b) := by
  intro r hr
  exact (hf r ⟨ha.trans hr.1, hr.2.trans_lt hb⟩).continuousAt.continuousWithinAt

private theorem deriv_eq_zero_at_maximum {f : ℝ → ℝ} {M r : ℝ}
    (hmax : ∀ t ∈ Ico (0 : ℝ) 1, f t ≤ M)
    (hr : r ∈ Ioo (0 : ℝ) 1) (heq : f r = M) : deriv f r = 0 := by
  have hloc : IsLocalMax f r := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    rw [heq]
    exact hmax t ⟨ht.1.le, ht.2⟩
  exact hloc.deriv_eq_zero

theorem no_three_ordered_maxima {f D : ℝ → ℝ} {M : ℝ}
    (hf : ∀ r ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ f r)
    (hf' : ∀ r ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ (deriv f) r)
    (hmax : ∀ r ∈ Ico (0 : ℝ) 1, f r ≤ M)
    (hD : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) D)
    (hzero : ∀ r ∈ Ioo (0 : ℝ) 1, deriv (deriv f) r = 0 ↔ D r = 0)
    {a b c : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) (hbc : b < c) (hfa : f a = M) (hfb : f b = M) (hfc : f c = M) : False := by
  have hb : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hab, hbc.trans hc.2⟩
  have hda := deriv_eq_zero_at_maximum hmax ha hfa
  have hdb := deriv_eq_zero_at_maximum hmax hb hfb
  have hdc := deriv_eq_zero_at_maximum hmax hc hfc
  obtain ⟨s, hs, hds⟩ := exists_deriv_eq_zero hab
    (continuousOn_Icc_of_below_one hf ha.1.le hb.2) (hfa.trans hfb.symm)
  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_zero hs.1
    (continuousOn_Icc_of_below_one hf' ha.1.le (hs.2.trans hb.2)) (hda.trans hds.symm)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hs.2
    (continuousOn_Icc_of_below_one hf' (ha.1.trans hs.1).le hb.2) (hds.trans hdb.symm)
  obtain ⟨w, hw, hdw⟩ := exists_deriv_eq_zero hbc
    (continuousOn_Icc_of_below_one hf' hb.1.le hc.2) (hdb.trans hdc.symm)
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hu.1, (hu.2.trans hs.2).trans hb.2⟩
  have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨(ha.1.trans hs.1).trans hv.1, hv.2.trans hb.2⟩
  have hw01 : w ∈ Ioo (0 : ℝ) 1 := ⟨hb.1.trans hw.1, hw.2.trans hc.2⟩
  exact strictConvex_no_three_zeros hD hu01 hw01
    (hu.2.trans hv.1) (hv.2.trans hw.1)
    ((hzero u hu01).mp hdu) ((hzero v hv01).mp hdv) ((hzero w hw01).mp hdw)

theorem maxima_encard_le_two {f D : ℝ → ℝ} {M : ℝ}
    (hf : ∀ r ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ f r)
    (hf' : ∀ r ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ (deriv f) r)
    (hmax : ∀ r ∈ Ico (0 : ℝ) 1, f r ≤ M)
    (hD : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) D)
    (hzero : ∀ r ∈ Ioo (0 : ℝ) 1, deriv (deriv f) r = 0 ↔ D r = 0) :
    {r | r ∈ Ioo (0 : ℝ) 1 ∧ f r = M}.encard ≤ 2 := by
  let Z : Set ℝ := {r | r ∈ Ioo (0 : ℝ) 1 ∧ f r = M}
  change Z.encard ≤ 2
  by_cases hsmall : Z.encard ≤ 1
  · exact hsmall.trans (by norm_num)
  obtain ⟨x, y, hx, hy, hxy⟩ := Set.one_lt_encard_iff.mp (lt_of_not_ge hsmall)
  have hsub : Z ⊆ {x, y} := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    by_cases hzy : z = y
    · simp [hzy]
    exfalso
    rcases lt_or_gt_of_ne hxy with hxy | hyx
    · rcases lt_or_gt_of_ne hzx with hzx | hxz
      · exact no_three_ordered_maxima hf hf' hmax hD hzero hz.1 hy.1 hzx hxy hz.2 hx.2 hy.2
      · rcases lt_or_gt_of_ne hzy with hzy | hyz
        · exact no_three_ordered_maxima hf hf' hmax hD hzero hx.1 hy.1 hxz hzy hx.2 hz.2 hy.2
        · exact no_three_ordered_maxima hf hf' hmax hD hzero hx.1 hz.1 hxy hyz hx.2 hy.2 hz.2
    · rcases lt_or_gt_of_ne hzy with hzy | hyz
      · exact no_three_ordered_maxima hf hf' hmax hD hzero hz.1 hx.1 hzy hyx hz.2 hy.2 hx.2
      · rcases lt_or_gt_of_ne hzx with hzx | hxz
        · exact no_three_ordered_maxima hf hf' hmax hD hzero hy.1 hx.1 hyz hzx hy.2 hz.2 hx.2
        · exact no_three_ordered_maxima hf hf' hmax hD hzero hy.1 hz.1 hyx hxz hy.2 hx.2 hz.2
  exact (Set.encard_mono hsub).trans_eq (Set.encard_pair hxy)

end
end TensorPCA.NonRSLowerProofs.FiniteCS
