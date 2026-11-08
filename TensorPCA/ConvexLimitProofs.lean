-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.LimitTools
public import Mathlib.Analysis.Convex.Deriv

/-! Pointwise convergence of convex functions implies convergence of derivatives
at each point where the functions and the limit are differentiable. -/
@[expose] public section
namespace TensorPCA.ConvexLimitProofs
open Filter Set
open scoped Topology

/-- Lemma A.7: only pointwise convergence on the open interval and
differentiability at the single chosen point are required. -/
theorem tendsto_deriv_of_convexOn_Ioo {f : ℕ → ℝ → ℝ} {l : ℝ → ℝ}
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hconv : ∀ n : ℕ, ConvexOn ℝ (Ioo a b) (f n))
    (hpoint : ∀ x ∈ Ioo a b, Tendsto (fun n ↦ f n x) atTop (𝓝 (l x)))
    (hfd : ∀ n : ℕ, DifferentiableAt ℝ (f n) t)
    (hld : DifferentiableAt ℝ l t) :
    Tendsto (fun n ↦ deriv (f n) t) atTop (𝓝 (deriv l t)) := by
  let δ : ℝ := min (t-a) (b-t)
  have hδ : 0 < δ := lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
  have hδleft : δ ≤ t-a := min_le_left _ _
  have hδright : δ ≤ b-t := min_le_right _ _
  have hpos (j : ℕ) : 0 < LimitTools.secantStep δ j :=
    div_pos hδ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_two)
  have hsmall (j : ℕ) : LimitTools.secantStep δ j < δ := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact div_lt_self hδ (by linarith)
  have hleft (j : ℕ) : t-LimitTools.secantStep δ j ∈ Ioo a b := by
    constructor <;> linarith [hsmall j, hpos j, ht.1, ht.2]
  have hright (j : ℕ) : t+LimitTools.secantStep δ j ∈ Ioo a b := by
    constructor <;> linarith [hsmall j, hpos j, ht.1, ht.2]
  have hbounds (j : ℕ) : ∀ᶠ n : ℕ in atTop,
      (f n t-f n (t-LimitTools.secantStep δ j))/LimitTools.secantStep δ j ≤ deriv (f n) t ∧
      deriv (f n) t ≤ (f n (t+LimitTools.secantStep δ j)-f n t)/LimitTools.secantStep δ j := by
    apply Eventually.of_forall
    intro n
    constructor
    · have H := (hconv n).slope_le_deriv (hleft j) ht (sub_lt_self t (hpos j)) (hfd n)
      simpa only [slope_def_field, sub_sub_cancel] using H
    · have H := (hconv n).deriv_le_slope ht (hright j) (lt_add_of_pos_right t (hpos j)) (hfd n)
      simpa only [slope_def_field, add_sub_cancel_left] using H
  have hdenom : Tendsto (fun j : ℕ ↦ (j : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ ↦ le_add_of_nonneg_right (le_of_lt zero_lt_two))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (LimitTools.secantStep δ) atTop (𝓝 0) := hdenom.const_div_atTop δ
  have hgt : Tendsto (LimitTools.secantStep δ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hpos⟩
  have hlt : Tendsto (fun j ↦ -LimitTools.secantStep δ j) atTop (𝓝[<] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa only [neg_zero] using hzero.neg,
        Eventually.of_forall (fun j ↦ neg_lt_zero.mpr (hpos j))⟩
  have hrightLimit : Tendsto
      (fun j ↦ (l (t+LimitTools.secantStep δ j)-l t)/LimitTools.secantStep δ j)
      atTop (𝓝 (deriv l t)) := by
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hld.hasDerivAt.tendsto_slope_zero_right.comp hgt
  have hleftLimit : Tendsto
      (fun j ↦ (l t-l (t-LimitTools.secantStep δ j))/LimitTools.secantStep δ j)
      atTop (𝓝 (deriv l t)) := by
    convert hld.hasDerivAt.tendsto_slope_zero_left.comp hlt using 1
    funext j
    simp only [Function.comp_def, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv]
    ring
  exact LimitTools.tendsto_of_eventual_envelopes
    (fun j ↦ ((hpoint t ht).sub (hpoint _ (hleft j))).div_const (LimitTools.secantStep δ j))
    (fun j ↦ ((hpoint _ (hright j)).sub (hpoint t ht)).div_const (LimitTools.secantStep δ j))
    hbounds hleftLimit hrightLimit


/-- The same local argument applies to any open convex domain, including
unbounded intervals. Convexity of the domain is already part of `ConvexOn`. -/
theorem tendsto_deriv_of_convexOn_open {f : ℕ → ℝ → ℝ} {l : ℝ → ℝ}
    {s : Set ℝ} {t : ℝ} (hs : IsOpen s) (ht : t ∈ s)
    (hconv : ∀ n : ℕ, ConvexOn ℝ s (f n))
    (hpoint : ∀ x ∈ s, Tendsto (fun n ↦ f n x) atTop (𝓝 (l x)))
    (hfd : ∀ n : ℕ, DifferentiableAt ℝ (f n) t)
    (hld : DifferentiableAt ℝ l t) :
    Tendsto (fun n ↦ deriv (f n) t) atTop (𝓝 (deriv l t)) := by
  obtain ⟨a, b, htI, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds ht)
  exact tendsto_deriv_of_convexOn_Ioo htI
    (fun n ↦ (hconv n).subset hsub (convex_Ioo a b))
    (fun x hx ↦ hpoint x (hsub hx)) hfd hld


end TensorPCA.ConvexLimitProofs
