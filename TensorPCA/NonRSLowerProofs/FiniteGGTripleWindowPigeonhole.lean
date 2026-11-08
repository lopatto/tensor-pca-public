-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGTripleWindowCover
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Real

/-! A finite-window mass pigeonhole. The family is chosen before the probability law,
and positive bad-event mass supplies a useful member without any prior nonemptiness
assumption on the covering family.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGTripleWindowPigeonhole
open MeasureTheory Set
open FiniteGGTripleWindowCover
open scoped BigOperators
noncomputable section

theorem ordered_triple_window_mass_pigeonhole (gap eps : ℝ)
    (T : Finset {A : Matrix (Fin 3) (Fin 3) ℝ // A∈orderedBadUnitGram gap})
    (hCover : ∀ B∈orderedBadUnitGram gap,∃ A∈T,B∈tripleWindow eps A.val)
    (rho : Measure (Matrix (Fin 3) (Fin 3) ℝ)) [IsProbabilityMeasure rho]
    {p : ℝ} (hp : 0<p) (hMass : p≤rho.real (orderedBadUnitGram gap)) :
    ∃ A∈T,p/((T.card : ℝ)+1)≤rho.real (tripleWindow eps A.val) := by
  classical
  let q := p/((T.card : ℝ)+1)
  have hq : 0<q := div_pos hp (by positivity)
  have hEq : q*((T.card : ℝ)+1)=p := div_mul_cancel₀ p (by positivity)
  have hSub : orderedBadUnitGram gap⊆⋃ A∈T,tripleWindow eps A.val := by
    intro B hB
    obtain ⟨A,hAT,hWin⟩ := hCover B hB
    exact Set.mem_iUnion.mpr ⟨A,Set.mem_iUnion.mpr ⟨hAT,hWin⟩⟩
  have hSum : p≤∑ A∈T,rho.real (tripleWindow eps A.val) :=
    hMass.trans ((measureReal_mono hSub (measure_ne_top rho _)).trans (measureReal_biUnion_finset_le (μ := rho) T _))
  by_contra hNo
  have hEach (A) (hAT : A∈T) : rho.real (tripleWindow eps A.val)≤q :=
    (lt_of_not_ge (fun h ↦ hNo ⟨A,hAT,h⟩)).le
  have H := Finset.sum_le_sum (fun A hAT ↦ hEach A hAT)
  have H' : (∑ A∈T,rho.real (tripleWindow eps A.val))≤(T.card : ℝ)*q := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using H
  nlinarith only [hSum,H',hEq,hq]

theorem exists_prechosen_ordered_triple_mass_cover (gap : ℝ) {eps : ℝ} (heps : 0<eps) :
    ∃ T : Finset {A : Matrix (Fin 3) (Fin 3) ℝ // A∈orderedBadUnitGram gap},
      (∀ B∈orderedBadUnitGram gap,∃ A∈T,B∈tripleWindow eps A.val) ∧
      ∀ rho : Measure (Matrix (Fin 3) (Fin 3) ℝ),IsProbabilityMeasure rho→
        ∀ p : ℝ,0<p→p≤rho.real (orderedBadUnitGram gap)→
          ∃ A∈T,p/((T.card : ℝ)+1)≤rho.real (tripleWindow eps A.val) := by
  obtain ⟨T,hT⟩ := exists_prechosen_ordered_triple_cover gap heps
  refine ⟨T,hT,?_⟩
  intro rho hRho p hp hMass
  letI := hRho
  exact ordered_triple_window_mass_pigeonhole gap eps T hT rho hp hMass

end
end TensorPCA.NonRSLowerProofs.FiniteGGTripleWindowPigeonhole
