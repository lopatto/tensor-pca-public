-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed analytic-certificate port from immutable source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/CSTwoAtom.lean
Only the literal two-atom measure and its probability/cutoff/integral/hatted
profile lemmas are retained. The unrelated admissible-minimizer interface and
its variation imports are omitted. Retained definitions/types/bodies change
only by local namespace/import prefixes.
See the repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.CrisantiSommers
@[expose] public section
namespace TensorPCA.RetainedCountProofs.CrisantiSommers
open MeasureTheory Set
noncomputable section
/-- The literal one-step probability law x δ₀+(1-x) δQ. -/
noncomputable def twoAtom (x Q : ℝ) : Measure ℝ :=
  ENNReal.ofReal x • Measure.dirac 0 + ENNReal.ofReal (1-x) • Measure.dirac Q

theorem twoAtom_probability {x Q : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    IsProbabilityMeasure (twoAtom x Q) := by
  constructor
  simp only [twoAtom, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add hx.1 (sub_nonneg.mpr hx.2)]
  norm_num

theorem twoAtom_hasCutoff {x Q : ℝ} (hQ : Q ∈ Ico (0:ℝ) 1) :
    HasCutoff (twoAtom x Q) Q := by
  refine ⟨hQ.1,hQ.2,?_⟩
  rw [twoAtom, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨le_refl 0,hQ.1⟩
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨hQ.1,le_refl Q⟩

theorem integral_twoAtom {x Q : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (f : ℝ → ℝ) :
    (∫ s, f s ∂twoAtom x Q) = x*f 0+(1-x)*f Q := by
  have h0 : Integrable f (ENNReal.ofReal x • Measure.dirac (0:ℝ)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hQ : Integrable f (ENNReal.ofReal (1-x) • Measure.dirac Q) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [twoAtom, integral_add_measure h0 hQ, integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal hx.1,ENNReal.toReal_ofReal (sub_nonneg.mpr hx.2)]

/-- The piecewise one-step hatted profile is derived from the actual law. -/
theorem xHat_twoAtom {x Q : ℝ} (hx : x ∈ Icc (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    xHat (twoAtom x Q) r =
      if r ≤ Q then (1-Q+x*Q)-x*r else 1-r := by
  unfold xHat
  rw [integral_twoAtom hx]
  simp only [max_eq_left hr]
  split_ifs with h
  · rw [max_eq_right h]
    ring
  · rw [max_eq_left (le_of_not_ge h)]
    ring

end
end TensorPCA.RetainedCountProofs.CrisantiSommers
