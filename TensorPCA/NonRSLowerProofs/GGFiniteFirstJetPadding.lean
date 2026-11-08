-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteFirstJet

/-! Exact zero-padding identities for the existing finite GG scores.
These are pointwise algebra, not differentiated invariance statements. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteFirstJetPadding
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type*}

theorem score_snoc_zero (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (old : Fin (n+2) → V) (v : V) :
    score (n+1) overlap (Fin.snoc psi (fun _ ↦ 0)) old v=
      score n overlap psi (initial old) v := by
  unfold score
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,add_zero,initial]

theorem correctedScore_snoc_zero_castSucc (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ)
    (old : Fin (n+2) → V) (l : Fin (n+1)) :
    correctedScore (n+1) overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0) old l.castSucc=
      correctedScore n overlap psi means (initial old) l := by
  unfold correctedScore
  rw [score_snoc_zero]
  simp only [Fin.snoc_castSucc,initial]

theorem correctedScore_snoc_zero_last (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ) (old : Fin (n+2) → V) :
    correctedScore (n+1) overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0) old (Fin.last (n+1))=
      score n overlap psi (initial old) (old (Fin.last (n+1))) := by
  unfold correctedScore
  rw [score_snoc_zero]
  simp only [Fin.snoc_last,sub_zero,add_zero]

theorem sum_correctedScore_snoc_zero (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ) (old : Fin (n+2) → V) :
    (∑ l : Fin (n+2), correctedScore (n+1) overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0) old l)=
      (∑ l : Fin (n+1), correctedScore n overlap psi means (initial old) l)+
        score n overlap psi (initial old) (old (Fin.last (n+1))) := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [correctedScore_snoc_zero_castSucc,correctedScore_snoc_zero_last]

end
end TensorPCA.NonRSLowerProofs.GGFiniteFirstJetPadding
