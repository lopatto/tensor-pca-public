-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGTripleWindowPigeonhole
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramMap
public import TensorPCA.NonRSLowerProofs.SphericalGGBlockWindowWeights

/-! Prechosen ordered triple windows give initial block-event mass under the full
amplitude/disorder/replica law, using the canonical blockWeight observable.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGInitialBlockWindow
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteUnitGramMap FiniteGGTripleWindowCover FiniteGGTripleWindowPigeonhole
open FiniteGGBlockWindows FiniteGGBlockWindowArray
open SphericalGGWeightObservable SphericalGGBlockWindowWeights
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ordered_bad_sampleGram_iff {N : ℕ} (old : Fin 3 → UnitSpin N) (gap : ℝ) :
    sampleGram old∈orderedBadUnitGram gap ↔
      unitOverlap (old 0) (old 1)+gap≤unitOverlap (old 0) (old 2) ∧
      unitOverlap (old 0) (old 2)≤unitOverlap (old 1) (old 2) := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨sampleGram_mem_unitGramSet old,h⟩

theorem initial_blockWeight_eq_one_of_window {N : ℕ}
    (old : Fin 3 → UnitSpin N) (A : Matrix (Fin 3) (Fin 3) ℝ) (eps cap : ℝ)
    (hWin : sampleGram old∈tripleWindow eps A) :
    blockWeight 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap old=1 := by
  have h : arrayBlockWindows 1 1 (fun i ↦ (old i).val) (A 0 1) (A 0 2) (A 1 2) eps cap := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact hWin.1.le
    · intro j
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      exact hWin.2.1.le
    · intro i j
      have hi : i=0 := Subsingleton.elim _ _
      have hj : j=0 := Subsingleton.elim _ _
      subst i; subst j
      exact hWin.2.2.le
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim _ _))
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim _ _))
  unfold blockWeight
  exact if_pos h

theorem tripleWindow_mass_le_initial_block_mean {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (eps cap : ℝ) :
    ((jointLaw (K := K) nu v 2).map (fun q ↦ sampleGram q.2)).real (tripleWindow eps A)≤
      ∫ q,blockWeight 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap q.2 ∂jointLaw (K := K) nu v 2 := by
  letI := jointLaw_probability (K := K) nu hv 2
  let F := fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) ↦ sampleGram q.2
  let S := F ⁻¹' tripleWindow eps A
  have hF : Measurable F := (sampleGram_measurable N 3).comp measurable_snd
  have hS : MeasurableSet S := hF (tripleWindow_isOpen eps A).measurableSet
  have hI : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (jointLaw (K := K) nu v 2) :=
    (integrable_const _).indicator hS
  have hBM : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) ↦
      blockWeight 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap q.2) :=
    (blockWeight_measurable N 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap).comp measurable_snd
  have hBI : Integrable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) ↦
      blockWeight 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap q.2) (jointLaw nu v 2) := by
    apply Integrable.of_bound hBM.aestronglyMeasurable 1
    exact .of_forall (fun q ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (blockWeight_mem 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap q.2).1]
      exact (blockWeight_mem 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap q.2).2)
  have H := integral_mono hI hBI (fun q ↦ by
    by_cases hq : q∈S
    · rw [Set.indicator_of_mem hq,initial_blockWeight_eq_one_of_window q.2 A eps cap hq]
    · rw [Set.indicator_of_notMem hq]
      exact (blockWeight_mem 1 1 (A 0 1) (A 0 2) (A 1 2) eps cap q.2).1)
  rw [integral_indicator_const (1 : ℝ) hS,smul_eq_mul,mul_one] at H
  rw [map_measureReal_apply hF (tripleWindow_isOpen eps A).measurableSet]
  exact H

theorem exists_initial_block_window_positive_mass (gap eps : ℝ)
    (T : Finset {A : Matrix (Fin 3) (Fin 3) ℝ // A∈orderedBadUnitGram gap})
    (hCover : ∀ B∈orderedBadUnitGram gap,∃ A∈T,B∈tripleWindow eps A.val)
    {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    {p : ℝ} (hp : 0<p)
    (hMass : p≤(jointLaw (K := K) nu v 2).real {q | sampleGram q.2∈orderedBadUnitGram gap}) :
    ∃ A∈T,p/((T.card : ℝ)+1)≤
      ∫ q,blockWeight 1 1 (A.val 0 1) (A.val 0 2) (A.val 1 2) eps (A.val 1 2+eps) q.2
        ∂jointLaw (K := K) nu v 2 := by
  letI := jointLaw_probability (K := K) nu hv 2
  let F := fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) ↦ sampleGram q.2
  have hF : Measurable F := (sampleGram_measurable N 3).comp measurable_snd
  let rho := (jointLaw (K := K) nu v 2).map F
  letI : IsProbabilityMeasure rho := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  have hBad : MeasurableSet (orderedBadUnitGram gap) := (orderedBadUnitGram_isCompact gap).isClosed.measurableSet
  have hMassR : p≤rho.real (orderedBadUnitGram gap) := by
    rw [map_measureReal_apply hF hBad]
    exact hMass
  obtain ⟨A,hAT,hA⟩ := ordered_triple_window_mass_pigeonhole gap eps T hCover rho hp hMassR
  exact ⟨A,hAT,hA.trans (tripleWindow_mass_le_initial_block_mean nu hv A.val eps (A.val 1 2+eps))⟩

end
end TensorPCA.NonRSLowerProofs.SphericalGGInitialBlockWindow
