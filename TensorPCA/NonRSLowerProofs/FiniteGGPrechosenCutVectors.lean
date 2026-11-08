-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGPrechosenPolynomialFamily
public import TensorPCA.NonRSLowerProofs.FiniteGGMonotoneBoundaryCuts

/-! One common finite family size and degree cutoff for all cut intervals,
chosen before every probability law. Scores use the existing canonical
projected extension, which is globally bounded; raw polynomials need not be. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGPrechosenCutVectors
open Set FiniteGGBoundaryBands FiniteGGPrechosenPolynomialFamily
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

theorem exists_prechosen_cut_polynomials (depth : ℕ) (a b : Fin depth → ℝ)
    {eta : ℝ} (hEta : 0<eta) (hEta1 : eta≤1) :
    ∃ J : ℕ,0<J ∧ 1/(J : ℝ)≤eta/2 ∧
      ∃ P : Fin depth → Fin J → Polynomial ℝ,∃ Q : ℕ,
        (∀ l j,(P l j).natDegree≤Q) ∧
        (∀ l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta/2) ∧
        ∀ l j r,|extendTest ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2 := by
  classical
  obtain ⟨M,hM⟩ := exists_nat_one_div_lt (show 0<eta/2 by positivity)
  let J := M+1
  have hJ : 0<J := Nat.succ_pos M
  have hBudget : 1/(J : ℝ)≤eta/2 := by
    simpa only [J,Nat.cast_add,Nat.cast_one] using hM.le
  have hPolys (l : Fin depth) (j : Fin J) :=
    exists_polynomial_near_continuousMap (-1) 1 (rampTest (a l) (b l) J j) (eta/2) (by positivity)
  choose P hP using hPolys
  let Q := Finset.univ.sup (fun l : Fin depth ↦ Finset.univ.sup (fun j : Fin J ↦ (P l j).natDegree))
  have hQ (l : Fin depth) (j : Fin J) : (P l j).natDegree≤Q :=
    (Finset.le_sup (f := fun j : Fin J ↦ (P l j).natDegree) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun l : Fin depth ↦ Finset.univ.sup (fun j : Fin J ↦ (P l j).natDegree))
        (Finset.mem_univ l))
  refine ⟨J,hJ,hBudget,P,Q,hQ,(fun l j ↦ (hP l j).le),?_⟩
  intro l j r
  exact (projected_polynomial_bound j (P l j) (hP l j).le r).trans (by linarith only [hEta1])

end
end TensorPCA.NonRSLowerProofs.FiniteGGPrechosenCutVectors
