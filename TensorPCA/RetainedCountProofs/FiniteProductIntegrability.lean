-- SPDX-License-Identifier: Apache-2.0
/- Narrow generic source port:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GOEPrincipalMinors.lean
Only the exact finite-product all-moments integrability proof is retained;
no Gaussian matrix/spectral statement is imported or assumed. See LICENSE. -/
module
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEPrincipalMinors
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
/-- Finite products of actual all-moment scalar observables are genuinely
integrable; no real-valued integral defaults are used. -/
lemma integrable_product_of_all_moments {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (S : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ S, ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp (f i) p μ) :
    Integrable (fun x => ∏ i ∈ S, f i x) μ := by
  by_cases hS : S.Nonempty
  · have hc : (S.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    have ht : (S.card : ℝ≥0∞) ≠ ⊤ := by simp
    have h := MemLp.fun_prod (p := fun _ : ι => (S.card : ℝ≥0∞))
      (fun i hi => hf i hi _ ht)
    have hexp : (∑ _i ∈ S, (S.card : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel hc ht, inv_one]
    rw [hexp] at h
    exact h.integrable le_rfl
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, Finset.prod_empty]
    exact integrable_const _


end
end TensorPCA.RetainedCountProofs.GOEPrincipalMinors
