-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteEntropyProofs
public import TensorPCA.PosteriorPairProofs
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! KL and finite entropy, with zero atoms handled explicitly. -/
@[expose] public section
namespace TensorPCA.FiniteInformationProofs
open MeasureTheory ProbabilityTheory InformationTheory Set Real
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rnDeriv_mul_singleton {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
    (μ ν : Measure T) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (x : T) :
    μ.rnDeriv ν x*ν {x} = μ {x} := by
  simpa only [lintegral_singleton] using Measure.setLIntegral_rnDeriv hμν {x}

theorem rnDeriv_eq_atom_ratio {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
    (μ ν : Measure T) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (x : T)
    (hx : ν {x} ≠ 0) : μ.rnDeriv ν x = μ {x}/ν {x} := by
  calc
    _ = μ.rnDeriv ν x*(ν {x}*(ν {x})⁻¹) := by
      rw [ENNReal.mul_inv_cancel hx (measure_ne_top _ _), mul_one]
    _ = μ {x}/ν {x} := by rw [← mul_assoc, rnDeriv_mul_singleton μ ν hμν x, div_eq_mul_inv]

theorem finite_klDiv_toReal_eq_sum {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (μ ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ x : T, μ.real {x}*Real.log (μ.real {x}/ν.real {x}) := by
  simp only [toReal_klDiv hμν Integrable.of_finite, probReal_univ, add_sub_cancel_right]
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ {x} = 0
  · simp [measureReal_def, hx]
  have hv : ν {x} ≠ 0 := fun h ↦ hx (hμν h)
  simp only [smul_eq_mul, llr, rnDeriv_eq_atom_ratio μ ν hμν x hv,
    ENNReal.toReal_div, measureReal_def]

theorem finite_klDiv_eq_entropy_crossEntropy {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (μ ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = -FiniteEntropyProofs.entropy μ-
      ∫ x, Real.log (ν.real {x}) ∂μ := by
  rw [finite_klDiv_toReal_eq_sum μ ν hμν, FiniteEntropyProofs.entropy,
    integral_fintype Integrable.of_finite, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ {x} = 0
  · simp [measureReal_def, hx]
  have hv : ν {x} ≠ 0 := fun h ↦ hx (hμν h)
  have hμr : μ.real {x} ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hx, measure_ne_top _ _⟩
  have hνr : ν.real {x} ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hv, measure_ne_top _ _⟩
  rw [Real.log_div hμr hνr]
  simp only [Real.negMulLog, smul_eq_mul]
  ring

theorem integral_log_atom_self {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ] :
    (∫ x, Real.log (μ.real {x}) ∂μ) = -FiniteEntropyProofs.entropy μ := by
  rw [integral_fintype Integrable.of_finite, FiniteEntropyProofs.entropy, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Real.negMulLog, smul_eq_mul]
  ring

theorem integral_log_atom_map {T U : Type*} [MeasurableSpace T] [Fintype U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure T) [IsProbabilityMeasure μ] (r : T → U) (hr : Measurable r) :
    (∫ x, Real.log ((μ.map r).real {r x}) ∂μ) = -FiniteEntropyProofs.entropy (μ.map r) := by
  exact (integral_map hr.aemeasurable
    (Integrable.of_finite (f := fun u ↦ Real.log ((μ.map r).real {u}))).aestronglyMeasurable).symm.trans
      (integral_log_atom_self (μ.map r))

theorem prod_real_singleton {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure T) (ν : Measure U) [SFinite ν] (p : T × U) :
    (μ.prod ν).real {p} = μ.real {p.1}*ν.real {p.2} := by
  rcases p with ⟨t,u⟩
  rw [measureReal_def, ← singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

/-- Actual pair relative entropy equals the finite entropy mutual-information
formula; in particular its nonnegativity is not supplied as an extra premise. -/
theorem pairInformation_eq_entropies {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q] (i j : Fin N) :
    (PosteriorPairProofs.pairInformation q i j).toReal =
      FiniteEntropyProofs.entropy (PosteriorPairProofs.coordinateLaw q i)+
        FiniteEntropyProofs.entropy (PosteriorPairProofs.coordinateLaw q j)-
          FiniteEntropyProofs.entropy (PosteriorPairProofs.pairLaw q i j) := by
  let μ := PosteriorPairProofs.pairLaw q i j
  let ν := (PosteriorPairProofs.coordinateLaw q i).prod (PosteriorPairProofs.coordinateLaw q j)
  have hμν : μ ≪ ν := PosteriorPairProofs.pairLaw_absolutelyContinuous_product q i j
  have hs : (∫ p, Real.log (ν.real {p}) ∂μ) =
      ∫ p, Real.log ((PosteriorPairProofs.coordinateLaw q i).real {p.1})+
        Real.log ((PosteriorPairProofs.coordinateLaw q j).real {p.2}) ∂μ := by
    rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
    apply Finset.sum_congr rfl
    intro p _
    simp only [smul_eq_mul]
    by_cases hp : μ {p} = 0
    · simp [measureReal_def, hp]
    have hv : ν {p} ≠ 0 := fun h ↦ hp (hμν h)
    have hvr : ν.real {p} ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hv, measure_ne_top _ _⟩
    have hprod := prod_real_singleton (PosteriorPairProofs.coordinateLaw q i)
      (PosteriorPairProofs.coordinateLaw q j) p
    change ν.real {p} = _ at hprod
    rw [hprod] at hvr
    rw [hprod, Real.log_mul (mul_ne_zero_iff.mp hvr).1 (mul_ne_zero_iff.mp hvr).2]
  rw [integral_add Integrable.of_finite Integrable.of_finite] at hs
  have hi := integral_log_atom_map μ Prod.fst measurable_fst
  have hj := integral_log_atom_map μ Prod.snd measurable_snd
  change (∫ p, Real.log (((PosteriorPairProofs.pairLaw q i j).map Prod.fst).real {p.1}) ∂μ) = _ at hi
  change (∫ p, Real.log (((PosteriorPairProofs.pairLaw q i j).map Prod.snd).real {p.2}) ∂μ) = _ at hj
  rw [PosteriorPairProofs.pairLaw_map_fst] at hi
  rw [PosteriorPairProofs.pairLaw_map_snd] at hj
  have h := finite_klDiv_eq_entropy_crossEntropy μ ν hμν
  rw [hs, hi, hj] at h
  change (klDiv μ ν).toReal = _
  linarith

end
end TensorPCA.FiniteInformationProofs
