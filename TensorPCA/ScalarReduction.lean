-- Copyright (c) 2026 Patrick Lopatto. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import TensorPCA.Statements
public import TensorPCA.Scalar
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! A reduction of the transition discontinuity to the scalar
root-selection laws. No jump or discontinuity conclusion is assumed. -/

namespace TensorPCA.ScalarReduction

open Scalar
open scoped Topology

/-- The threshold separation, critical branch gap, subcritical convention and
actual discontinuity follow from the scalar stationary-root characterizations. -/
theorem discontinuous_at {k : ℕ} (hk : 3 ≤ k) (hs : SelectionLaws k) :
    lambdaS k < lambdaC k ∧
      ((k : ℝ) - 2) / ((k : ℝ) - 1) < qS k (lambdaC k) ∧
      (∀ lam : ℝ, 0 ≤ lam → lam < lambdaC k → qStar k lam = 0) ∧
      ¬ ContinuousAt (qStar k) (lambdaC k) := by
  rcases hs with ⟨hls, hgap, hbdd, hstable, hmax, hz, hrange⟩
  have hcritical : ((k : ℝ) - 2) / ((k : ℝ) - 1) < qS k (lambdaC k) :=
    (hstable (lambdaC k) hgap).1.1.1
  refine ⟨hgap, hcritical, ?_, ?_⟩
  · intro lam hlam hlt
    simp only [qStar, if_pos hlt.le]
  · intro hcontinuous
    have hkreal : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have halpha : 0 < ((k : ℝ) - 2) / ((k : ℝ) - 1) :=
      div_pos (by linarith) (by linarith)
    have hqcritical : qStar k (lambdaC k) = 0 := by simp [qStar]
    obtain ⟨delta, hdelta, hclose⟩ := Metric.continuousAt_iff.mp hcontinuous
      ((((k : ℝ) - 2) / ((k : ℝ) - 1)) / 2) (half_pos halpha)
    have hsuper : lambdaC k < lambdaC k + delta / 2 := by linarith
    have hdist : dist (lambdaC k + delta / 2) (lambdaC k) < delta := by
      rw [Real.dist_eq]
      have heq : lambdaC k + delta / 2 - lambdaC k = delta / 2 := by linarith
      rw [heq, abs_of_pos (half_pos hdelta)]
      linarith
    have hbranch : ((k : ℝ) - 2) / ((k : ℝ) - 1) <
        qS k (lambdaC k + delta / 2) :=
      (hstable (lambdaC k + delta / 2) (hgap.trans hsuper)).1.1.1
    have hselected : qStar k (lambdaC k + delta / 2) =
        qS k (lambdaC k + delta / 2) :=
      (hmax (lambdaC k + delta / 2) hsuper).2.2.1
    have hqpositive : 0 < qStar k (lambdaC k + delta / 2) := by
      rw [hselected]
      exact halpha.trans hbranch
    have hsmall := hclose hdist
    rw [hqcritical, Real.dist_eq, sub_zero, abs_of_pos hqpositive] at hsmall
    rw [hselected] at hsmall
    linarith

/-- Conditional scalar reduction for the unnumbered transition conclusion.
Every open input is a root/existence law, not an assumed jump statement. -/
theorem discontinuous (hs : ∀ k : ℕ, 3 ≤ k → SelectionLaws k) :
    Statements.DiscontinuousTransition := by
  intro k hk
  exact discontinuous_at hk (hs k hk)


end TensorPCA.ScalarReduction
