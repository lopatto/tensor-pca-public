-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSMinimizerProofs

/-! Literal two-atom probability representation of the finite-CS minimizer, including
zero weights and coincident endpoints.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem law_eq_weighted_diracs_of_ae_pair (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (a b : ℝ) (hae : ∀ᵐ r ∂mu, r = a ∨ r = b) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      mu = ENNReal.ofReal x • Measure.dirac a + ENNReal.ofReal (1 - x) • Measure.dirac b := by
  by_cases hab : a = b
  · subst b
    have hs : ∀ᵐ r ∂mu, r ∈ ({a} : Finset ℝ) := by simpa using hae
    have hrepr := (Measure.ae_mem_finset_iff (s := ({a} : Finset ℝ))).mp hs
    simp only [Finset.sum_singleton] at hrepr
    have hmass := congrArg (fun nu : Measure ℝ => nu univ) hrepr
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one] at hmass
    rw [← hmass, one_smul] at hrepr
    exact ⟨1, by norm_num, by simpa using hrepr⟩
  · have hrepr := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hab).mp hae
    have hsum : mu {a} + mu {b} = 1 := by
      have h := congrArg (fun nu : Measure ℝ => nu univ) hrepr
      simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul] using h.symm
    have haTop := measure_ne_top mu {a}
    have hbTop := measure_ne_top mu {b}
    have hsumReal : (mu {a}).toReal + (mu {b}).toReal = 1 := by
      have h := congrArg ENNReal.toReal hsum
      simpa [ENNReal.toReal_add haTop hbTop] using h
    have hx0 : 0 ≤ (mu {a}).toReal := ENNReal.toReal_nonneg
    have hx1 : (mu {a}).toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := mu {b})]
    have hremaining : 1 - (mu {a}).toReal = (mu {b}).toReal := by linarith
    refine ⟨(mu {a}).toReal, ⟨hx0, hx1⟩, ?_⟩
    rw [ENNReal.ofReal_toReal haTop, hremaining, ENNReal.ofReal_toReal hbTop]
    exact hrepr

theorem exists_ordered_two_atom_minimizer (k : ℕ) (hk : 3 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1) :
    ∃ (nu : Trial) (q0 q1 x : ℝ), 0 < q0 ∧ q0 ≤ q1 ∧ q1 < 1 ∧ x ∈ Icc (0 : ℝ) 1 ∧
      realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
        ENNReal.ofReal (1 - x) • Measure.dirac q1 ∧
      rawFunctional k beta m nu = rawValue k beta m ∧
      ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau := by
  obtain ⟨nu, a, b, ha, hb, heq, hae, hmin⟩ := exists_two_point_minimizer k hk hbeta hm0 hm1
  have hlaw : ∀ᵐ r ∂realLaw nu, r = a ∨ r = b :=
    (ae_map_iff measurable_subtype_coe.aemeasurable
      ((measurableSet_singleton a).union (measurableSet_singleton b))).mpr hae
  obtain ⟨x, hx, hrepr⟩ := law_eq_weighted_diracs_of_ae_pair (realLaw nu) a b hlaw
  by_cases hab : a ≤ b
  · exact ⟨nu, a, b, x, ha.1, hab, hb.2, hx, hrepr, heq, hmin⟩
  · refine ⟨nu, b, a, 1 - x, hb.1, (le_of_not_ge hab), ha.2,
      ⟨sub_nonneg.mpr hx.2, by linarith [hx.1]⟩, ?_, heq, hmin⟩
    rw [show 1 - (1 - x) = x by ring, add_comm]
    exact hrepr

/-- The literal finite-temperature two-atom profile, obtained from its probability law
rather than postulated as a trial-interface property.
-/
theorem profile_of_ordered_two_atom (beta : ℝ) (nu : Trial) {q0 q1 x : ℝ}
    (hq : q0 ≤ q1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) (t : ℝ) :
    profile beta nu t = beta * ((1 - max t q1) + x * max (q1 - max t q0) 0) := by
  rw [profile_eq_scaled_xHat_realLaw]
  unfold RetainedCountProofs.CrisantiSommers.xHat
  rw [hlaw]
  have hi0 : Integrable (fun r : ℝ => 1 - max t r)
      (ENNReal.ofReal x • Measure.dirac q0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hi1 : Integrable (fun r : ℝ => 1 - max t r)
      (ENNReal.ofReal (1 - x) • Measure.dirac q1) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure hi0 hi1, integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac, ENNReal.toReal_ofReal hx.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hx.2), smul_eq_mul]
  congr 1
  by_cases ht0 : t ≤ q0
  · rw [max_eq_right ht0, max_eq_right (ht0.trans hq),
      max_eq_left (sub_nonneg.mpr hq)]
    ring
  · have h0t := le_of_not_ge ht0
    rw [max_eq_left h0t]
    by_cases ht1 : t ≤ q1
    · rw [max_eq_right ht1, max_eq_left (sub_nonneg.mpr ht1)]
      ring
    · rw [max_eq_left (le_of_not_ge ht1), max_eq_right (by linarith : q1 - t ≤ 0)]
      ring

end
end TensorPCA.NonRSLowerProofs.FiniteCS
