-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSTwoPointRepresentation

/-! Eliminate inactive first atoms before applying the finite-temperature Gaussian
endpoint. A two-point law has both weights positive; every single-atom degeneration
is represented with mass one and coincident points.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem exists_positive_mass_two_atom_minimizer (k : ℕ) (hk : 3 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1) :
    ∃ (nu : Trial) (q0 q1 x : ℝ), 0 < q0 ∧ q0 ≤ q1 ∧ q1 < 1 ∧
      x ∈ Ioc (0 : ℝ) 1 ∧ (q0 = q1 ↔ x = 1) ∧
      realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
        ENNReal.ofReal (1 - x) • Measure.dirac q1 ∧
      rawFunctional k beta m nu = rawValue k beta m ∧
      ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau := by
  obtain ⟨nu, q0, q1, x, hq0, hq01, hq1, hx, hlaw, heq, hmin⟩ :=
    exists_ordered_two_atom_minimizer k hk hbeta hm0 hm1
  by_cases hx0 : x = 0
  · refine ⟨nu, q1, q1, 1, hq0.trans_le hq01, le_rfl, hq1, by norm_num,
      by simp, ?_, heq, hmin⟩
    simpa [hx0] using hlaw
  by_cases hx1 : x = 1
  · refine ⟨nu, q0, q0, 1, hq0, le_rfl, hq01.trans_lt hq1, by norm_num,
      by simp, ?_, heq, hmin⟩
    simpa [hx1] using hlaw
  by_cases hqeq : q0 = q1
  · subst q1
    have hsum : ENNReal.ofReal x + ENNReal.ofReal (1 - x) = 1 := by
      rw [← ENNReal.ofReal_add hx.1 (sub_nonneg.mpr hx.2)]
      norm_num
    rw [← add_smul, hsum, one_smul] at hlaw
    refine ⟨nu, q0, q0, 1, hq0, le_rfl, hq1, by norm_num, by simp, ?_, heq, hmin⟩
    simpa using hlaw
  exact ⟨nu, q0, q1, x, hq0, hq01, hq1, ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩,
    ⟨fun h => False.elim (hqeq h), fun h => False.elim (hx1 h)⟩, hlaw, heq, hmin⟩

end
end TensorPCA.NonRSLowerProofs.FiniteCS
