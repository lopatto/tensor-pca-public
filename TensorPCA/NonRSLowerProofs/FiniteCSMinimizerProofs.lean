-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSFunctionalTransport
public import TensorPCA.NonRSLowerProofs.FiniteCSCutoffTransport
public import TensorPCA.NonRSLowerProofs.FiniteCSSliceStructure

/-! Attainment and two-point reduction for the complete extended finite-temperature CS
problem. All intermediate compactness, finiteness, cutoff, first variation and
strict-comparator obligations are discharged.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
open RetainedCountProofs.CrisantiSommers
noncomputable section

theorem exists_cutoff_minimizer (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) :
    ∃ (nu : Trial) (q : ℝ), q ∈ Ico (0 : ℝ) 1 ∧
      (∀ᵐ a : Overlap ∂(nu : Measure Overlap), (a : ℝ) ≤ q) ∧
      rawFunctional k beta m nu = rawValue k beta m ∧
      ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau := by
  obtain ⟨nu, heq, _hfinite, hmin⟩ := exists_finite_minimizer k beta m
  obtain ⟨q, hq0, hq1, hcut⟩ := exists_uniform_minimizer_ae_cutoff k hk hbeta hm
  exact ⟨nu, q, ⟨hq0.le, hq1⟩, hcut nu hmin, heq, hmin⟩

theorem exists_legacy_minimizer_of_raw_minimizer (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ a : Overlap ∂(nu : Measure Overlap), (a : ℝ) ≤ q)
    (hmin : ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau) :
    ∃ zeta : Admissible, zeta.law = realLaw nu ∧ zeta.IsMinimizer beta (Scalar.xiSlice k m) := by
  let zeta : Admissible := ⟨realLaw nu, inferInstance, ⟨q, realLaw_hasCutoff nu hq hnu⟩⟩
  refine ⟨zeta, rfl, ?_⟩
  intro mu
  let tau := cutoffTrial mu.law mu.hasCutoff
  have htau : ∀ᵐ a : Overlap ∂(tau : Measure Overlap), (a : ℝ) ≤ mu.cutoff :=
    cutoffTrial_ae_le mu.law mu.hasCutoff
  have H := ENNReal.toReal_mono
    (rawFunctional_cutoff_ne_top k hk hbeta hm tau ⟨mu.hasCutoff.1, mu.hasCutoff.2.1⟩ htau)
    (hmin tau)
  rw [rawFunctional_cutoff_toReal k hk hbeta hm nu hq hnu,
    rawFunctional_cutoff_toReal k hk hbeta hm tau ⟨mu.hasCutoff.1, mu.hasCutoff.2.1⟩ htau] at H
  have hround : realLaw tau = mu.law := realLaw_cutoffTrial mu.law mu.hasCutoff
  rw [hround, div_le_div_iff₀ hbeta hbeta] at H
  rw [zeta.value_eq beta (Scalar.xiSlice k m) (realLaw_hasCutoff nu hq hnu),
    mu.value_eq beta (Scalar.xiSlice k m) mu.hasCutoff]
  dsimp [zeta]
  have HH := (mul_le_mul_iff_left₀ hbeta).mp H
  linarith

/-- Unconditional analytic two-point attainment for the full finite-T trial class. No
minimizer, support cutoff or structural conclusion is assumed.
-/
theorem exists_two_point_minimizer (k : ℕ) (hk : 3 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1) :
    ∃ (nu : Trial) (a b : ℝ), a ∈ Ioo (0 : ℝ) 1 ∧ b ∈ Ioo (0 : ℝ) 1 ∧
      rawFunctional k beta m nu = rawValue k beta m ∧
      (∀ᵐ q : Overlap ∂(nu : Measure Overlap), (q : ℝ) = a ∨ (q : ℝ) = b) ∧
      ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau := by
  have hm : m ∈ Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  obtain ⟨nu, q, hq, hnu, heq, hmin⟩ := exists_cutoff_minimizer k (by omega) hbeta hm
  obtain ⟨zeta, hlaw, hzmin⟩ := exists_legacy_minimizer_of_raw_minimizer k (by omega) hbeta hm nu hq hnu hmin
  obtain ⟨a, b, ha, hb, hpair⟩ := xiSlice_minimizer_ae_two_points k hk hbeta hm0 hm1 zeta hzmin
  rw [hlaw] at hpair
  have hpairnu : ∀ᵐ q : Overlap ∂(nu : Measure Overlap), (q : ℝ) = a ∨ (q : ℝ) = b :=
    (ae_map_iff measurable_subtype_coe.aemeasurable
      ((measurableSet_singleton a).union (measurableSet_singleton b))).mp hpair
  exact ⟨nu, a, b, ha, hb, heq, hpairnu, hmin⟩

end
end TensorPCA.NonRSLowerProofs.FiniteCS
