-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianBMinimization
public import Mathlib.Data.Fin.VecNotation

/-! Three-atom specialization of the scalar precision minimum.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomPrecision
open FiniteCSGaussianBMinimization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def threeAtomCost (x z y0 Δ0 Δ1 Δ2 B : ℝ) : ℝ :=
  cost (x*Δ0+z*Δ1+Δ2) y0 ![1/x,1/z,1]
    ![x*Δ0+z*Δ1+Δ2,z*Δ1+Δ2,Δ2] ![z*Δ1+Δ2,Δ2,0] B

theorem threeAtomCost_eq {x z y0 Δ0 Δ1 Δ2 B : ℝ}
    (hx : 0 < x) (hz : 0 < z) (h0 : 0 ≤ Δ0) (h1 : 0 ≤ Δ1) (h2 : 0 ≤ Δ2)
    (hB : x*Δ0+z*Δ1+Δ2 < B) :
    threeAtomCost x z y0 Δ0 Δ1 Δ2 B = B-1-Real.log B+
      y0/(B-(x*Δ0+z*Δ1+Δ2))+
      Real.log ((B-(z*Δ1+Δ2))/(B-(x*Δ0+z*Δ1+Δ2)))/x+
      Real.log ((B-Δ2)/(B-(z*Δ1+Δ2)))/z+Real.log (B/(B-Δ2)) := by
  have hD0 : 0 < B-(x*Δ0+z*Δ1+Δ2) := sub_pos.mpr hB
  have hD1 : 0 < B-(z*Δ1+Δ2) := by nlinarith [mul_nonneg hx.le h0]
  have hD2 : 0 < B-Δ2 := by nlinarith [mul_nonneg hz.le h1]
  have hBp : 0 < B := by linarith
  unfold threeAtomCost cost
  simp only [Fin.sum_univ_three]
  change B-1-Real.log B+y0/(B-(x*Δ0+z*Δ1+Δ2))+
    (1/x*(Real.log (B-(z*Δ1+Δ2))-Real.log (B-(x*Δ0+z*Δ1+Δ2)))+
      1/z*(Real.log (B-Δ2)-Real.log (B-(z*Δ1+Δ2)))+
      1*(Real.log (B-0)-Real.log (B-Δ2))) = _
  simp only [sub_zero, one_mul]
  rw [Real.log_div hD1.ne' hD0.ne', Real.log_div hD2.ne' hD1.ne',
    Real.log_div hBp.ne' hD2.ne']
  ring

theorem exists_threeAtom_minimizing_root {x z y0 Δ0 Δ1 Δ2 : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hy : 0 < y0)
    (h0 : 0 ≤ Δ0) (h1 : 0 ≤ Δ1) (h2 : 0 ≤ Δ2) :
    ∃ B : ℝ, x*Δ0+z*Δ1+Δ2 < B ∧
      y0/(B-(x*Δ0+z*Δ1+Δ2))^2+
        Δ0/((B-(x*Δ0+z*Δ1+Δ2))*(B-(z*Δ1+Δ2)))+
        Δ1/((B-(z*Δ1+Δ2))*(B-Δ2))+Δ2/((B-Δ2)*B) = 1-1/B ∧
      ∀ C : ℝ, x*Δ0+z*Δ1+Δ2 < C →
        threeAtomCost x z y0 Δ0 Δ1 Δ2 B ≤ threeAtomCost x z y0 Δ0 Δ1 Δ2 C := by
  have hd : 0 ≤ x*Δ0+z*Δ1+Δ2 := by positivity
  have ha : ∀ i : Fin 3, 0 ≤ (![1/x,1/z,1] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp <;> positivity
  have hst : ∀ i : Fin 3,
      (![z*Δ1+Δ2,Δ2,0] : Fin 3 → ℝ) i ≤ (![x*Δ0+z*Δ1+Δ2,z*Δ1+Δ2,Δ2] : Fin 3 → ℝ) i ∧
      (![x*Δ0+z*Δ1+Δ2,z*Δ1+Δ2,Δ2] : Fin 3 → ℝ) i ≤ x*Δ0+z*Δ1+Δ2 := by
    intro i
    fin_cases i <;> simp <;> (try constructor) <;> nlinarith [mul_nonneg hx.le h0, mul_nonneg hz.le h1]
  obtain ⟨B,hB,hroot,hmin⟩ := exists_minimizing_root ![1/x,1/z,1]
    ![x*Δ0+z*Δ1+Δ2,z*Δ1+Δ2,Δ2] ![z*Δ1+Δ2,Δ2,0] hd hy ha hst
  refine ⟨B,hB,?_,hmin⟩
  simp only [FiniteCSGaussianBMinimization.slope, Fin.sum_univ_three] at hroot
  change 1-1/B-y0/(B-(x*Δ0+z*Δ1+Δ2))^2-
    ((1/x)*(x*Δ0+z*Δ1+Δ2-(z*Δ1+Δ2))/((B-(x*Δ0+z*Δ1+Δ2))*(B-(z*Δ1+Δ2)))+
      (1/z)*(z*Δ1+Δ2-Δ2)/((B-(z*Δ1+Δ2))*(B-Δ2))+
      1*(Δ2-0)/((B-Δ2)*(B-0))) = 0 at hroot
  simp only [sub_zero, one_mul] at hroot
  have he0 : (1/x)*(x*Δ0+z*Δ1+Δ2-(z*Δ1+Δ2)) = Δ0 := by field_simp [hx.ne']; ring
  have he1 : (1/z)*(z*Δ1+Δ2-Δ2) = Δ1 := by field_simp [hz.ne']; ring
  rw [he0,he1] at hroot
  linarith

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomPrecision
