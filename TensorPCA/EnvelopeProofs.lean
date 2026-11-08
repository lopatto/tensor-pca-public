-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.LimitTools
public import Mathlib.Topology.Order.Compact

/-! A compact affine specialization of the manuscript's envelope theorem.
The maximizing slopes may agree even when the maximizer is not unique. -/

@[expose] public section
namespace TensorPCA.EnvelopeProofs
open Set Filter
open scoped Topology
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

def affineValue (H G : X → ℝ) (t : ℝ) : ℝ :=
  sSup (range (fun x ↦ H x+t*G x))

theorem affineValue_attained {H G : X → ℝ} (hH : Continuous H) (hG : Continuous G)
    (t : ℝ) : ∃ x, H x+t*G x = affineValue H G t ∧
      ∀ y, H y+t*G y ≤ H x+t*G x := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn
    (show (univ : Set X).Nonempty from Set.univ_nonempty)
    (hH.add (continuous_const.mul hG)).continuousOn
  have hmax : ∀ y, H y+t*G y ≤ H x+t*G x := fun y ↦ hx (mem_univ y)
  refine ⟨x, ?_, hmax⟩
  symm
  exact (show IsGreatest (range (fun y ↦ H y+t*G y)) (H x+t*G x) from
    ⟨mem_range_self x, by rintro _ ⟨y, rfl⟩; exact hmax y⟩).csSup_eq

theorem le_affineValue {H G : X → ℝ} (hH : Continuous H) (hG : Continuous G)
    (t : ℝ) (x : X) : H x+t*G x ≤ affineValue H G t := by
  obtain ⟨y, hy, hmax⟩ := affineValue_attained hH hG t
  rw [← hy]
  exact hmax x

theorem slope_bounded {G : X → ℝ} (hG : Continuous G) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, |G x| ≤ M := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn
    (show (univ : Set X).Nonempty from Set.univ_nonempty) hG.abs.continuousOn
  exact ⟨|G x|+1, by positivity, fun y ↦ (hx (mem_univ y)).trans (by linarith)⟩

theorem near_maximizer_slope {H G : X → ℝ} (hH : Continuous H) (hG : Continuous G)
    {t D : ℝ} (hD : ∀ x, H x+t*G x = affineValue H G t → G x = D)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ x,
      affineValue H G t-(H x+t*G x) < gap → |G x-D| < eps := by
  let B : Set X := {x | eps ≤ |G x-D|}
  have hB : IsCompact B := (isClosed_le continuous_const
    (hG.sub continuous_const).abs).isCompact
  by_cases hne : B.Nonempty
  · obtain ⟨y, hy, hymax⟩ := hB.exists_isMaxOn hne
      (hH.add (continuous_const.mul hG)).continuousOn
    have hylt : H y+t*G y < affineValue H G t := by
      refine lt_of_le_of_ne (le_affineValue hH hG t y) ?_
      intro heq
      have hs := hD y heq
      have hb : eps ≤ |G y-D| := hy
      rw [hs, sub_self, abs_zero] at hb
      linarith
    refine ⟨affineValue H G t-(H y+t*G y), sub_pos.mpr hylt, ?_⟩
    intro x hx
    by_contra hbad
    have hxB : x ∈ B := le_of_not_gt hbad
    have hm := hymax hxB
    change H x+t*G x ≤ H y+t*G y at hm
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _
    exact lt_of_not_ge (fun hx ↦ hne ⟨x, hx⟩)

theorem eventually_maximizer_slope {H G : X → ℝ}
    (hH : Continuous H) (hG : Continuous G) {t D : ℝ}
    (hD : ∀ x, H x+t*G x = affineValue H G t → G x = D)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ u in 𝓝 t, ∀ x, H x+u*G x = affineValue H G u → |G x-D| < eps := by
  obtain ⟨gap, hgap, hnear⟩ := near_maximizer_slope hH hG hD heps
  obtain ⟨M, hM, hbound⟩ := slope_bounded hG
  obtain ⟨y, hy, _⟩ := affineValue_attained hH hG t
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨gap/(2*M), div_pos hgap (by positivity), ?_⟩
  intro u hu x hx
  apply hnear
  have hpert : H y+u*G y ≤ H x+u*G x := by
    rw [hx]
    exact le_affineValue hH hG u y
  have hdef : affineValue H G t-(H x+t*G x) ≤ (u-t)*(G x-G y) := by
    rw [← hy]
    nlinarith
  have hdiff : |G x-G y| ≤ 2*M :=
    (abs_sub _ _).trans (by linarith [hbound x, hbound y])
  have habs : (u-t)*(G x-G y) ≤ |u-t| *(2*M) := calc
    _ ≤ |(u-t)*(G x-G y)| := le_abs_self _
    _ = |u-t| *|G x-G y| := abs_mul _ _
    _ ≤ |u-t| *(2*M) := mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
  have hsmall : |u-t| *(2*M) < gap := by
    have hu' : |u-t| < gap/(2*M) := by simpa only [Real.dist_eq] using hu
    exact (lt_div_iff₀ (by positivity : 0 < 2*M)).mp hu'
  exact lt_of_le_of_lt (le_trans hdef habs) hsmall

theorem affineValue_hasDerivAt {H G : X → ℝ}
    (hH : Continuous H) (hG : Continuous G) {t D : ℝ}
    (hD : ∀ x, H x+t*G x = affineValue H G t → G x = D) :
    HasDerivAt (affineValue H G) D t := by
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  filter_upwards [eventually_maximizer_slope hH hG hD heps] with u hu
  obtain ⟨y, hy, _⟩ := affineValue_attained hH hG t
  obtain ⟨x, hx, _⟩ := affineValue_attained hH hG u
  have hDy : G y = D := hD y hy
  have hnear := hu x hx
  have hlow := le_affineValue hH hG u y
  have hupp := le_affineValue hH hG t x
  have hnonneg : 0 ≤ affineValue H G u-affineValue H G t-(u-t)*D := by
    rw [hDy] at hlow
    rw [← hy, ← hx, hDy]
    rw [← hx] at hlow
    nlinarith
  have hupp' : affineValue H G u-affineValue H G t-(u-t)*D ≤ (u-t)*(G x-D) := by
    rw [← hx]
    nlinarith
  have habs : (u-t)*(G x-D) ≤ eps*|u-t| := calc
    _ ≤ |(u-t)*(G x-D)| := le_abs_self _
    _ = |u-t| *|G x-D| := abs_mul _ _
    _ ≤ |u-t| *eps := mul_le_mul_of_nonneg_left hnear.le (abs_nonneg _)
    _ = eps*|u-t| := mul_comm _ _
  simpa only [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg hnonneg] using
    hupp'.trans habs


/-- A set-based form suitable for the physical unit sphere. Only continuity on
the compact index set is needed; the value is the ordinary supremum of its image. -/
theorem hasDerivAt_sSup_affine {Y : Type*} [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) (hne : K.Nonempty) {H G : Y → ℝ}
    (hH : ContinuousOn H K) (hG : ContinuousOn G K) {t D : ℝ}
    (hD : ∀ x ∈ K,
      H x+t*G x = sSup ((fun y ↦ H y+t*G y) '' K) → G x = D) :
    HasDerivAt (fun u : ℝ ↦ sSup ((fun y ↦ H y+u*G y) '' K)) D t := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  have hval (u : ℝ) : affineValue (fun x : K ↦ H x) (fun x : K ↦ G x) u =
      sSup ((fun y ↦ H y+u*G y) '' K) := by
    unfold affineValue
    congr 1
    ext z
    simp only [mem_range, mem_image, Subtype.exists, exists_prop]
  have hcH : Continuous (fun x : K ↦ H x) := by
    exact hH.comp_continuous continuous_subtype_val (fun x ↦ x.property)
  have hcG : Continuous (fun x : K ↦ G x) := by
    exact hG.comp_continuous continuous_subtype_val (fun x ↦ x.property)
  have hd := affineValue_hasDerivAt hcH hcG
    (t := t) (D := D) (by
      intro x hx
      exact hD x x.property (by simpa only [hval] using hx))
  have hfun : affineValue (fun x : K ↦ H x) (fun x : K ↦ G x) =
      (fun u : ℝ ↦ sSup ((fun y ↦ H y+u*G y) '' K)) := funext hval
  rwa [hfun] at hd

end
end TensorPCA.EnvelopeProofs
