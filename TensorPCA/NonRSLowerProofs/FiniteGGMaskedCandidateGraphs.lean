-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGConditionalLowMass

/-! One measurable graph combines finitely many candidate graphs on disjoint parameter
cells. Candidate and bad-pair masses use the same kernel; there is no additional
selector law or per-cell loss.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGMaskedCandidateGraphs
open MeasureTheory ProbabilityTheory Set
open FiniteGGConditionalLowMass
noncomputable section
variable {P V : Type*} [MeasurableSpace P] [MeasurableSpace V]

/-- Finite masked union; the mask depends only on the original parameter. -/
def maskedUnion {J : ℕ} (S : Fin J→Set P) (B : Fin J→Set (P×(V×V))) : Set (P×(V×V)) :=
  ⋃i,(Prod.fst ⁻¹' S i)∩B i

theorem maskedUnion_measurable {J : ℕ} (S : Fin J→Set P) (B : Fin J→Set (P×(V×V)))
    (hS : ∀i,MeasurableSet (S i)) (hB : ∀i,MeasurableSet (B i)) :
    MeasurableSet (maskedUnion S B) := by
  exact MeasurableSet.iUnion (fun i ↦ ((hS i).preimage measurable_fst).inter (hB i))

theorem mem_maskedUnion_iff {J : ℕ} (S : Fin J→Set P) (B : Fin J→Set (P×(V×V)))
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j))) {i : Fin J} {p : P}
    (hp : p∈S i) (r : V×V) : (p,r)∈maskedUnion S B ↔ (p,r)∈B i := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
    have hji : j=i := by
      by_contra hne
      exact (Set.disjoint_left.mp (hdis hne)) hj.1 hp
    simpa only [hji] using hj.2
  · intro h
    exact Set.mem_iUnion.mpr ⟨i,⟨hp,h⟩⟩

theorem candidateMass_maskedUnion_on_cell {J : ℕ} (G : Kernel P V)
    (S : Fin J→Set P) (B : Fin J→Set (P×(V×V)))
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j))) {i : Fin J} {p : P}
    (hp : p∈S i) (u : V) :
    candidateMass G (maskedUnion S B) (p,u)=candidateMass G (B i) (p,u) := by
  unfold candidateMass
  congr 1
  ext v
  exact mem_maskedUnion_iff S B hdis hp (u,v)

theorem badPairMass_maskedUnion_on_cell {J : ℕ} (G : Kernel P V) (Omega : Set (P×V))
    (S : Fin J→Set P) (B : Fin J→Set (P×(V×V)))
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j))) {i : Fin J} {p : P}
    (hp : p∈S i) :
    badPairMass G Omega (maskedUnion S B) p=badPairMass G Omega (B i) p := by
  unfold badPairMass
  congr 1
  ext r
  simp only [Set.mem_setOf_eq,mem_maskedUnion_iff S B hdis hp r]

end
end TensorPCA.NonRSLowerProofs.FiniteGGMaskedCandidateGraphs
