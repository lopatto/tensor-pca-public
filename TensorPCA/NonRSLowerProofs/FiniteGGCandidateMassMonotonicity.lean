-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGMaskedCandidateGraphs

/-! Set monotonicity for the conditional bad-pair masses and finite masked candidate
graphs. No selector or additional law is introduced.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGCandidateMassMonotonicity
open MeasureTheory ProbabilityTheory Set
open FiniteGGConditionalLowMass FiniteGGMaskedCandidateGraphs
variable {P V : Type*} [MeasurableSpace P] [MeasurableSpace V]

theorem badPairMass_mono_Omega (G : Kernel P V) [IsMarkovKernel G]
    {Omega Omega' : Set (P×V)} (hOmega : Omega⊆Omega')
    (B : Set (P×(V×V))) (p : P) :
    badPairMass G Omega B p≤badPairMass G Omega' B p := by
  exact measureReal_mono (fun r hr ↦ ⟨hOmega hr.1,hOmega hr.2.1,hr.2.2⟩)

theorem badPairMass_antitone_graph (G : Kernel P V) [IsMarkovKernel G]
    (Omega : Set (P×V)) {B B' : Set (P×(V×V))} (hB : B⊆B') (p : P) :
    badPairMass G Omega B' p≤badPairMass G Omega B p := by
  exact measureReal_mono (fun r hr ↦ ⟨hr.1,hr.2.1,fun h ↦ hr.2.2 (hB h)⟩)

theorem common_graph_subset_maskedUnion {J : ℕ}
    (S : Fin J → Set P) (B : Fin J → Set (P×(V×V))) (C : Set (P×(V×V)))
    (hCover : (⋃ i,S i)=univ) (hC : ∀ i,C⊆B i) : C⊆maskedUnion S B := by
  intro q hq
  obtain ⟨i,hi⟩ : ∃ i : Fin J,q.1∈S i := by
    have h : q.1∈⋃ i,S i := by rw [hCover]; trivial
    exact Set.mem_iUnion.mp h
  exact Set.mem_iUnion.mpr ⟨i,⟨hi,hC i hq⟩⟩

end TensorPCA.NonRSLowerProofs.FiniteGGCandidateMassMonotonicity
