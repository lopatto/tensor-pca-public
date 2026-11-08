-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGInitialBlockWindow
public import TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaPermutation

/-! The full bad-triple event is covered by the ordered event and its first-two-replica
swap. Joint exchangeability preserves amplitude and Gaussian disorder, giving the
factor two in event mass.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTripleUnordering
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteUnitGramMap FiniteGGTripleWindowCover SphericalGGInitialBlockWindow
open SphericalGGWeightObservable GGFiniteJointReplicaPermutation
noncomputable section

theorem bad_triple_mem_ordered_or_swap {N : ℕ} (old : Fin 3 → UnitSpin N) (gap : ℝ)
    (hBad : unitOverlap (old 0) (old 1)+gap≤
      min (unitOverlap (old 0) (old 2)) (unitOverlap (old 1) (old 2))) :
    sampleGram old∈orderedBadUnitGram gap ∨
      sampleGram (fun i ↦ old (Equiv.swap (0 : Fin 3) 1 i))∈orderedBadUnitGram gap := by
  have H := le_min_iff.mp hBad
  by_cases hOrder : unitOverlap (old 0) (old 2)≤unitOverlap (old 1) (old 2)
  · exact Or.inl ((ordered_bad_sampleGram_iff old gap).mpr ⟨H.1,hOrder⟩)
  · apply Or.inr
    rw [ordered_bad_sampleGram_iff]
    have hSwap2 : Equiv.swap (0 : Fin 3) 1 2=2 := by decide
    simp only [Equiv.swap_apply_left,Equiv.swap_apply_right,hSwap2]
    have hSym : unitOverlap (old 1) (old 0)=unitOverlap (old 0) (old 1) :=
      real_inner_comm (old 0).val (old 1).val
    rw [hSym]
    exact ⟨H.2,(le_of_not_ge hOrder)⟩

theorem bad_triple_mass_le_twice_ordered {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (gap : ℝ) :
    (jointLaw (K := K) nu v 2).real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
      min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))}≤
      2*(jointLaw (K := K) nu v 2).real {q | sampleGram q.2∈orderedBadUnitGram gap} := by
  letI := jointLaw_probability (K := K) nu hv 2
  let mu := jointLaw (K := K) nu v 2
  let e := Equiv.swap (0 : Fin 3) 1
  let P := jointReindex (Omega := (Fin K → ℝ)×PerturbationDisorder N K) (V := UnitSpin N) 3 e
  let O := {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) |
    sampleGram q.2∈orderedBadUnitGram gap}
  have hO : MeasurableSet O :=
    ((sampleGram_measurable N 3).comp measurable_snd) (orderedBadUnitGram_isCompact gap).isClosed.measurableSet
  have hLaw := jointLaw_permutation_hasLaw (K := K) nu hv 2 e
  have hMap : mu.map P=mu := hLaw.map_eq
  have hPM : Measurable P := jointReindex_measurable 3 e
  have hPre : mu.real (P ⁻¹' O)=mu.real O := by
    have H := map_measureReal_apply (μ := mu) hPM hO
    rw [hMap] at H
    exact H.symm
  have hSub : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) |
      unitOverlap (q.2 0) (q.2 1)+gap≤min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))}⊆
      O∪P ⁻¹' O := by
    intro q hq
    exact bad_triple_mem_ordered_or_swap q.2 gap hq
  have H := (measureReal_mono hSub (measure_ne_top mu _)).trans
    (measureReal_union_le (μ := mu) O (P ⁻¹' O))
  rw [hPre] at H
  change mu.real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
      min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))}≤2*mu.real O
  linarith only [H]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTripleUnordering
