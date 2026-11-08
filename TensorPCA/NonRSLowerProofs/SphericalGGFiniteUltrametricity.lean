-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGUniformWindowRadius
public import TensorPCA.NonRSLowerProofs.SphericalGGInitialBlockWindow
public import TensorPCA.NonRSLowerProofs.SphericalGGTripleUnordering

/-! Uniform finite-Gibbs ultrametricity, with the radius and finite cover chosen before
the physical law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteUltrametricity
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteUnitGramMap FiniteUnitGramRealization FiniteGGTripleWindowCover
open SphericalGGWeightObservable SphericalGGBlockWindowWeights SphericalGGUniformWindowRadius
open SphericalGGInitialBlockWindow SphericalGGTripleUnordering
open scoped BigOperators
noncomputable section

theorem exists_uniform_ordered_bad_triple_threshold {gap p : ℝ}
    (hgap : 0<gap) (hp : p∈Ioc (0 : ℝ) 1) :
    ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        (jointLaw (K := K) nu v 2).real {q | sampleGram q.2∈orderedBadUnitGram gap}<p := by
  classical
  obtain ⟨eps,heps,hWindow⟩ := exists_uniform_window_radius hgap
  obtain ⟨T,hCover⟩ := exists_prechosen_ordered_triple_cover gap heps
  let q := p/((T.card : ℝ)+1)
  have hDen : 1≤(T.card : ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) T.card]
  have hq : q∈Ioc (0 : ℝ) 1 := ⟨div_pos hp.1 (by positivity),(div_le_self hp.1.le hDen).trans hp.2⟩
  have hEach (A : {A : Matrix (Fin 3) (Fin 3) ℝ // A∈orderedBadUnitGram gap}) :
      ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
        ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
          (∫ z,blockWeight 1 1 (A.val 0 1) (A.val 0 2) (A.val 1 2) eps (A.val 1 2+eps) z.2
            ∂jointLaw (K := K) nu v 2)<q := by
    have hc : -1≤A.val 1 2 := (abs_le.mp (entry_abs_le_one A.val A.property.1.1 A.property.1.2 1 2)).1
    have hg : gap≤A.val 0 2-A.val 0 1 := by linarith only [A.property.2.1]
    exact hWindow q hq _ _ _ hc hg A.property.2.2 (orderedBadUnitGram_center_margin hgap A.val A.property)
  choose QA HA using hEach
  let Q := T.sup QA
  refine ⟨Q,?_⟩
  intro K hK
  have hKA (A : T) : QA A.val≤K := (Finset.le_sup (f := QA) A.property).trans hK
  have hEx (A : T) := HA A.val K (hKA A)
  choose VV HV using hEx
  let V := 1+∑ A : T,VV A
  have hNon (A : T) : 0≤VV A := (by norm_num : (0 : ℝ)≤1).trans (HV A).1
  have hV : 1≤V := by dsimp only [V]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun A _ ↦ hNon A))
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  by_contra hNot
  have hMass : p≤(jointLaw (K := K) nu v 2).real {z | sampleGram z.2∈orderedBadUnitGram gap} := le_of_not_gt hNot
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  obtain ⟨A,hAT,hA⟩ := exists_initial_block_window_positive_mass gap eps T hCover nu hv0 hp.1 hMass
  let i : T := ⟨A,hAT⟩
  have hSingle : VV i≤∑ A : T,VV A := Finset.single_le_sum (fun A _ ↦ hNon A) (Finset.mem_univ i)
  have hVi : VV i≤v := by dsimp only [V] at hv; linarith only [hSingle,hv]
  have hSmall := (HV i).2 nu v hVi
  exact (not_le_of_gt hSmall) hA

theorem exists_uniform_bad_triple_threshold {gap delta : ℝ} (hgap : 0<gap) (hdelta : 0<delta) :
    ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        (jointLaw (K := K) nu v 2).real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
          min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))}<delta := by
  let p := min (delta/2) (1/2 : ℝ)
  have hp : p∈Ioc (0 : ℝ) 1 := ⟨lt_min (half_pos hdelta) (by norm_num),(min_le_right _ _).trans (by norm_num)⟩
  obtain ⟨Q,hMain⟩ := exists_uniform_ordered_bad_triple_threshold hgap hp
  refine ⟨Q,?_⟩
  intro K hK
  obtain ⟨V,hV,HV⟩ := hMain K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  calc
    _ ≤ 2*(jointLaw (K := K) nu v 2).real {q | sampleGram q.2∈orderedBadUnitGram gap} := bad_triple_mass_le_twice_ordered nu hv0 gap
    _ < 2*p := mul_lt_mul_of_pos_left (HV nu v hv) (by norm_num)
    _ ≤ delta := by have H : p≤delta/2 := min_le_left _ _; linarith only [H]

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteUltrametricity
