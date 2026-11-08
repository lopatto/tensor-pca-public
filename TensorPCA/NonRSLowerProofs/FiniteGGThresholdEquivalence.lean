-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! A closed upper threshold is an equivalence relation away from a lower
boundary band and a positive-gap ultrametricity violation.  The lower endpoint
of the excluded band is included; atoms at the threshold remain on the upper
side. No distinct-index or nonatomicity assumption is used. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGThresholdEquivalence
open Set

theorem threshold_equivalence {I : Type*} (R : I → I → ℝ)
    (hSelf : ∀ i,R i i=1) (hSym : ∀ i j,R i j=R j i)
    {u h : ℝ} (hu : u≤1) (_hh : 0<h)
    (hUM : ∀ i j k,¬R i j+h≤min (R i k) (R j k))
    (hBand : ∀ i j,R i j∉Ico (u-h) u) :
    Equivalence (fun i j ↦ u≤R i j) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hSelf]
    exact hu
  · intro i j hij
    rwa [hSym j i]
  · intro i j k hij hjk
    by_contra hik
    have hikLt : R i k<u := lt_of_not_ge hik
    have hBelow : R i k<u-h := by
      by_contra hNot
      exact hBand i k ⟨le_of_not_gt hNot,hikLt⟩
    apply hUM i k j
    apply le_min
    · linarith only [hBelow,hij]
    · rw [hSym k j]
      linarith only [hBelow,hjk]

theorem all_thresholds_equivalence {I L : Type*} (R : I → I → ℝ)
    (hSelf : ∀ i,R i i=1) (hSym : ∀ i j,R i j=R j i)
    (cuts : L → ℝ) (hCuts : ∀ l,cuts l≤1) {h : ℝ} (hh : 0<h)
    (hUM : ∀ i j k,¬R i j+h≤min (R i k) (R j k))
    (hBand : ∀ l i j,R i j∉Ico (cuts l-h) (cuts l)) :
    ∀ l,Equivalence (fun i j ↦ cuts l≤R i j) :=
  fun l ↦ threshold_equivalence R hSelf hSym (hCuts l) hh hUM (hBand l)

theorem bad_thresholds_subset {X I L : Type*} (R : X → I → I → ℝ)
    (hSelf : ∀ x i,R x i i=1) (hSym : ∀ x i j,R x i j=R x j i)
    (cuts : L → ℝ) (hCuts : ∀ l,cuts l≤1) {h : ℝ} (hh : 0<h) :
    {x | ¬∀ l,Equivalence (fun i j ↦ cuts l≤R x i j)}⊆
      {x | ∃ i j k,R x i j+h≤min (R x i k) (R x j k)}∪
      {x | ∃ l i j,R x i j∈Ico (cuts l-h) (cuts l)} := by
  intro x hx
  by_contra hNot
  apply hx
  apply all_thresholds_equivalence (R x) (hSelf x) (hSym x) cuts hCuts hh
  · intro i j k hBad
    exact hNot (Or.inl ⟨i,j,k,hBad⟩)
  · intro l i j hBad
    exact hNot (Or.inr ⟨l,i,j,hBad⟩)

end TensorPCA.NonRSLowerProofs.FiniteGGThresholdEquivalence
