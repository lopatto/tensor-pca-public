-- SPDX-License-Identifier: Apache-2.0
-- Generic right-derivative continuity proof narrowly ported from
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SourceLiteratureGroundStateExtraction.lean
-- The local application is to the original admissible profile class; no
-- thermal minimizer or source GroundProfile structure is imported.
module
public import TensorPCA.JTGapCalculusProofs
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section
namespace TensorPCA.JTProfileRepresentationProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem convex_rightDerivative_rightContinuous (g : ℝ → ℝ)
    (hg : ConvexOn ℝ (Iio 1) g) {x : ℝ} (hx : x < 1) :
    ContinuousWithinAt (fun z => derivWithin g (Ioi z) z) (Ici x) x := by
  let D : ℝ → ℝ := fun z => derivWithin g (Ioi z) z
  have hd (z : ℝ) (hz : z < 1) : HasDerivWithinAt g (D z) (Ioi z) z :=
    hg.hasDerivWithinAt_rightDeriv_of_mem_interior (by simpa using hz)
  have hm : MonotoneOn D (Iio 1) := by
    simpa only [interior_Iio] using hg.monotoneOn_rightDeriv
  have hc : ContinuousAt g x :=
    (hg.continuousOn isOpen_Iio x hx).continuousAt (Iio_mem_nhds hx)
  have hr : ContinuousWithinAt D (Ioi x) x := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [Ioo_mem_nhdsGT hx] with z hz
      exact ha.trans_le (hm hx hz.2 hz.1.le)
    · intro b hb
      have hs : Tendsto (slope g x) (𝓝[>] x) (𝓝 (D x)) :=
        (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (hd x hx)
      obtain ⟨y, hy, hsy⟩ :=
        ((show ∀ᶠ y in 𝓝[>] x, y ∈ Ioo x 1 from Ioo_mem_nhdsGT hx).and
          (hs (Iio_mem_nhds hb))).exists
      have hsc : ContinuousAt (fun z => slope g z y) x := by
        simp only [slope_def_field]
        exact (continuousAt_const.sub hc).div
          (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hy.1.ne')
      have hslope : ∀ᶠ z in 𝓝 x, slope g z y < b := hsc (Iio_mem_nhds hsy)
      filter_upwards [hslope.filter_mono nhdsWithin_le_nhds,
        Ioo_mem_nhdsGT hy.1] with z hz hzy
      exact (hg.rightDeriv_le_slope_of_mem_interior
        (by simpa using hzy.2.trans hy.2) hy.2 hzy.2).trans_lt hz
  have hset : Ici x = insert x (Ioi x) := by
    ext z
    simp only [mem_Ici, mem_insert_iff, mem_Ioi]
    grind
  rw [hset]
  exact hr.insert

theorem neg_profileExtend_convex {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    ConvexOn ℝ (Iio (1 : ℝ)) (fun t => -JTFirstVariationProofs.profileExtend p t) := by
  refine ⟨convex_Iio 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hxc : max 0 x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _,max_le (by norm_num) hx.le⟩
  have hyc : max 0 y ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _,max_le (by norm_num) hy.le⟩
  have hzlt : a*x+b*y < 1 := (convex_Iio (1 : ℝ)) hx hy ha hb hab
  have hzc : max 0 (a*x+b*y) ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _,max_le (by norm_num) hzlt.le⟩
  have huc : a*max 0 x+b*max 0 y ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hxc hyc ha hb hab
  have hmax : max 0 (a*x+b*y) ≤ a*max 0 x+b*max 0 y := by
    apply max_le
    · exact add_nonneg (mul_nonneg ha (le_max_left _ _))
        (mul_nonneg hb (le_max_left _ _))
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right 0 x) ha)
        (mul_le_mul_of_nonneg_left (le_max_right 0 y) hb)
  have hanti := hp.2.1 hzc huc hmax
  have hconc := hp.2.2.1.2 hxc hyc ha hb hab
  change a*p (max 0 x)+b*p (max 0 y) ≤ p (a*max 0 x+b*max 0 y) at hconc
  change -p (JTFirstVariationProofs.clamp (a*x+b*y)) ≤
    a*(-p (JTFirstVariationProofs.clamp x))+b*(-p (JTFirstVariationProofs.clamp y))
  simp only [JTFirstVariationProofs.clamp,min_eq_right hx.le,min_eq_right hy.le,
    min_eq_right hzlt.le]
  linarith

def profileRate (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  derivWithin (fun s => -JTFirstVariationProofs.profileExtend p s) (Ioi t) t

theorem profileRate_hasDerivWithinAt {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t < 1) :
    HasDerivWithinAt (fun s => -JTFirstVariationProofs.profileExtend p s)
      (profileRate p t) (Ioi t) t :=
  (neg_profileExtend_convex hp).hasDerivWithinAt_rightDeriv_of_mem_interior
    (by simpa using ht)

theorem profileRate_monotone {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    MonotoneOn (profileRate p) (Iio (1 : ℝ)) := by
  change MonotoneOn (fun t => derivWithin (fun s => -JTFirstVariationProofs.profileExtend p s)
    (Ioi t) t) (Iio (1 : ℝ))
  simpa only [interior_Iio] using (neg_profileExtend_convex hp).monotoneOn_rightDeriv

theorem profileRate_nonneg {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t < 1) : 0 ≤ profileRate p t := by
  have hm : Monotone (fun s => -JTFirstVariationProofs.profileExtend p s) := by
    intro x y hxy
    apply neg_le_neg
    exact hp.2.1 (JTFirstVariationProofs.clamp_mem x) (JTFirstVariationProofs.clamp_mem y)
      (max_le_max le_rfl (min_le_min le_rfl hxy))
  apply ge_of_tendsto
    ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
      (profileRate_hasDerivWithinAt hp ht))
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hm.monotoneOn univ).slope_nonneg (mem_univ t) (mem_univ y)

theorem profileRate_rightContinuous {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t < 1) : ContinuousWithinAt (profileRate p) (Ici t) t :=
  convex_rightDerivative_rightContinuous _ (neg_profileExtend_convex hp) ht

theorem profileRate_intervalIntegrable {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    IntervalIntegrable (profileRate p) volume (0 : ℝ) 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
  exact intervalIntegral.integrableOn_deriv_right_of_nonneg
    (JTFirstVariationProofs.continuous_profileExtend hp).neg.continuousOn
    (fun t ht => profileRate_hasDerivWithinAt hp ht.2)
    (fun t ht => profileRate_nonneg hp ht.2)

theorem profile_eq_initial_sub_integral_rate {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p t = p 0-∫ s in (0 : ℝ)..t, profileRate p s := by
  have hInt : IntervalIntegrable (profileRate p) volume (0 : ℝ) t :=
    (profileRate_intervalIntegrable hp).mono_set (by
      rw [uIcc_of_le ht.1,uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Icc_subset_Icc le_rfl ht.2)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (JTFirstVariationProofs.continuous_profileExtend hp).neg.continuousOn
    (fun s hs => profileRate_hasDerivWithinAt hp (hs.2.trans_le ht.2)) hInt
  change (∫ s in (0 : ℝ)..t, profileRate p s) =
    -JTFirstVariationProofs.profileExtend p t-(-JTFirstVariationProofs.profileExtend p 0) at H
  simp only [JTFirstVariationProofs.profileExtend,JTFirstVariationProofs.clamp_eq ht,
    JTFirstVariationProofs.clamp_eq (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)] at H
  linarith

theorem integral_profileRate {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    (∫ s in (0 : ℝ)..1, profileRate p s) = p 0-p 1 := by
  have H := profile_eq_initial_sub_integral_rate hp (t := 1) (by norm_num)
  linarith

theorem integral_profileRate_lt_initial {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    (∫ s in (0 : ℝ)..1, profileRate p s) < p 0 := by
  rw [integral_profileRate hp]
  linarith [hp.2.2.2 1 (by norm_num)]


end
end TensorPCA.JTProfileRepresentationProofs
