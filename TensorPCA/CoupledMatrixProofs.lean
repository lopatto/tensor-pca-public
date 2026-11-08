-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.Coupled
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! Explicit 2x2 overlap and Gaussian-recursion matrices in Theorem4.1. -/
@[expose] public section
namespace TensorPCA.CoupledMatrixProofs
open Set Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def symmetric2 (d o : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then d else o

theorem symmetric2_isHermitian (d o : ℝ) : (symmetric2 d o).IsHermitian := by
  ext i j
  simp [conjTranspose_apply,symmetric2,eq_comm]

theorem symmetric2_quad (d o : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (symmetric2 d o *ᵥ x) =
      ((d+o)/2)*(x 0+x 1)^2+((d-o)/2)*(x 0-x 1)^2 := by
  simp only [dotProduct,mulVec,Fin.sum_univ_two,symmetric2]
  simp
  ring

theorem symmetric2_posSemidef {d o : ℝ} (hp : 0 ≤ d+o) (hm : 0 ≤ d-o) :
    (symmetric2 d o).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨symmetric2_isHermitian d o,?_⟩
  intro x
  rw [symmetric2_quad]
  exact add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
    (mul_nonneg (by linarith) (sq_nonneg _))

theorem symmetric2_posDef {d o : ℝ} (hp : 0 < d+o) (hm : 0 < d-o) :
    (symmetric2 d o).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨symmetric2_isHermitian d o,?_⟩
  intro x hx
  have hnotboth : x 0+x 1 ≠ 0 ∨ x 0-x 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    have h0 : x 0 = 0 := by linarith [hn.1,hn.2]
    have h1 : x 1 = 0 := by linarith [hn.1,hn.2]
    apply hx
    funext i
    by_cases hi : i = 0
    · subst i
      exact h0
    · rw [Fin.eq_one_of_ne_zero i hi]
      exact h1
  rw [symmetric2_quad]
  obtain hsum | hdiff := hnotboth
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) (sq_pos_of_ne_zero hsum))
      (mul_nonneg (by linarith) (sq_nonneg _))
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_pos (by linarith) (sq_pos_of_ne_zero hdiff))

theorem symmetric2_det (d o : ℝ) : (symmetric2 d o).det = d^2-o^2 := by
  rw [det_fin_two]
  simp [symmetric2]
  ring

def Q3 (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := symmetric2 u u
def Q4 (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := symmetric2 1 u

def A3 (a L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := symmetric2 (1+a) (-L)
def A2 (a m L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A3 a L - (m/2*a) • symmetric2 1 1
def A4 (a d L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A3 a L + (d-a) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem A2_eq (a m L : ℝ) :
    A2 a m L = symmetric2 (1+a-m*a/2) (-L-m*a/2) := by
  ext i j
  by_cases hij : i = j <;> simp [A2,A3,symmetric2,hij] <;> ring

theorem A4_eq (a d L : ℝ) : A4 a d L = symmetric2 (1+d) (-L) := by
  ext i j
  by_cases hij : i = j <;> simp [A4,A3,symmetric2,hij]

/-- The diagonal in the radial remainder is taken from A4. -/
theorem A4_diagonal (a d L : ℝ) (i : Fin 2) : A4 a d L i i = 1+d := by
  rw [A4_eq]
  simp [symmetric2]

theorem Q4_sub_Q3 (u : ℝ) : Q4 u-Q3 u = symmetric2 (1-u) 0 := by
  ext i j
  by_cases hij : i = j <;> simp [Q4,Q3,symmetric2,hij]

theorem Q3_posSemidef {u : ℝ} (hu : 0 ≤ u) : (Q3 u).PosSemidef := by
  apply symmetric2_posSemidef <;> linarith

theorem overlap_increment_posSemidef {u : ℝ} (hu : u ≤ 1) : (Q4 u-Q3 u).PosSemidef := by
  rw [Q4_sub_Q3]
  apply symmetric2_posSemidef <;> linarith

theorem A3_posDef {a m L : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hmargin : 0 < 1+(1-m)*a-L) : (A3 a L).PosDef := by
  have hma : 0 ≤ m*a := mul_nonneg (by linarith) ha
  apply symmetric2_posDef <;> nlinarith

theorem A2_posDef {a m L : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hmargin : 0 < 1+(1-m)*a-L) : (A2 a m L).PosDef := by
  rw [A2_eq]
  apply symmetric2_posDef <;> nlinarith

theorem A4_posDef {a d m L : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hda : a ≤ d) (hmargin : 0 < 1+(1-m)*a-L) : (A4 a d L).PosDef := by
  have hma : 0 ≤ m*a := mul_nonneg (by linarith) ha
  rw [A4_eq]
  apply symmetric2_posDef <;> nlinarith

theorem A3_det (a L : ℝ) : (A3 a L).det = (1+a-L)*(1+a+L) := by
  rw [A3,symmetric2_det]
  ring

theorem A2_det (a m L : ℝ) : (A2 a m L).det = (1+(1-m)*a-L)*(1+a+L) := by
  rw [A2_eq,symmetric2_det]
  ring

theorem determinant_ratio {a m L : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (_hmargin : 0 < 1+(1-m)*a-L) :
    (A3 a L).det/(A2 a m L).det = (1+a-L)/(1+(1-m)*a-L) := by
  have hB : 0 < 1+a+L := by linarith
  rw [A3_det,A2_det]
  field_simp [hB.ne']

theorem recursion_parameter_order {m : ℝ} (hm : m ∈ Icc (1 : ℝ) 2) :
    (0 : ℝ) ≤ 1/2 ∧ (1/2 : ℝ) ≤ m/2 ∧ m/2 ≤ 1 := by
  constructor
  · norm_num
  · constructor <;> linarith [hm.1,hm.2]

/-- All actual source matrices have the needed positivity under precisely the
reviewed scalar admissibility conditions. -/
theorem admissible_matrix_facts (k : ℕ) (barLam : ℝ) {p : Fin 4 → ℝ}
    (hp : Coupled.Admissible k barLam p) :
    (Q3 (p 3)).PosSemidef ∧ (Q4 (p 3)-Q3 (p 3)).PosSemidef ∧
      (A2 (Coupled.xiPrime k (p 0) (p 3)) (p 1) (p 2)).PosDef ∧
      (A3 (Coupled.xiPrime k (p 0) (p 3)) (p 2)).PosDef ∧
      (A4 (Coupled.xiPrime k (p 0) (p 3)) (Coupled.xiPrime k (p 0) 1) (p 2)).PosDef := by
  have ha : 0 ≤ Coupled.xiPrime k (p 0) (p 3) := by
    unfold Coupled.xiPrime
    have hu := hp.2.2.2.1.1
    positivity
  have hda : Coupled.xiPrime k (p 0) (p 3) ≤ Coupled.xiPrime k (p 0) 1 := by
    have hpow : (p 3)^(k-1) ≤ 1 := pow_le_one₀ hp.2.2.2.1.1 hp.2.2.2.1.2
    unfold Coupled.xiPrime
    simpa only [one_pow,mul_one] using
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg (p 0)))
  exact ⟨Q3_posSemidef hp.2.2.2.1.1,overlap_increment_posSemidef hp.2.2.2.1.2,
    A2_posDef ha hp.2.2.1.1 hp.2.2.2.2,
    A3_posDef ha hp.2.1.1 hp.2.2.1.1 hp.2.2.2.2,
    A4_posDef ha hp.2.1.1 hp.2.2.1.1 hda hp.2.2.2.2⟩

/-- The corrected radial parameter is b=1+xi'(1), uniformly bounded on the
reviewed temperature interval. The endpoint b=1 is included. -/
theorem admissible_radial_parameter (k : ℕ) (barLam : ℝ) {p : Fin 4 → ℝ}
    (hp : Coupled.Admissible k barLam p) (i : Fin 2) :
    A4 (Coupled.xiPrime k (p 0) (p 3)) (Coupled.xiPrime k (p 0) 1) (p 2) i i ∈
      Icc (1 : ℝ) (1+(k : ℝ)*barLam^2) := by
  rw [A4_diagonal]
  simp only [Coupled.xiPrime,one_pow,mul_one]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hbar : 0 ≤ barLam := hp.1.1.trans hp.1.2
  have hsq := (sq_le_sq₀ hp.1.1 hbar).mpr hp.1.2
  exact ⟨by nlinarith [sq_nonneg (p 0)],by nlinarith [mul_le_mul_of_nonneg_left hsq hk0]⟩

/-- Exact determinant and trace reconstruction of the frozen scalar trial;
this is algebra only, with the interpolation inequality still separate. -/
theorem trial_matrix_representation (k : ℕ) (lam : ℝ) {m L u : ℝ}
    (hu : 0 ≤ u) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hmargin : 0 < 1+(1-m)*Coupled.xiPrime k lam u-L) :
    Coupled.trial k lam m L u =
      Coupled.xiPrime k lam 1-L*u-Coupled.theta k lam 1+(1-m)*Coupled.theta k lam u+
        (1/m)*Real.log ((A3 (Coupled.xiPrime k lam u) L).det/(A2 (Coupled.xiPrime k lam u) m L).det)-
          (1/2 : ℝ)*Real.log ((A3 (Coupled.xiPrime k lam u) L).det) := by
  have ha : 0 ≤ Coupled.xiPrime k lam u := by unfold Coupled.xiPrime; positivity
  have hma : 0 ≤ m*Coupled.xiPrime k lam u := mul_nonneg (by linarith) ha
  have hA : 0 < 1+Coupled.xiPrime k lam u-L := by nlinarith
  have hB : 0 < 1+Coupled.xiPrime k lam u+L := by linarith
  rw [determinant_ratio ha hL hmargin,A3_det,Real.log_mul hA.ne' hB.ne']
  have hbase : Coupled.xiPrime k lam 1-Coupled.theta k lam 1 = lam^2 := by
    simp only [Coupled.xiPrime,Coupled.theta,one_pow,mul_one]
    ring
  unfold Coupled.trial
  nlinarith

end
end TensorPCA.CoupledMatrixProofs
