-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A finite coordinate Borel lift of ordered rank-one unit tensors. A diagonal
coordinate selects a canonical representative; no abstract selection axiom is used. -/

@[expose] public section
namespace TensorPCA.TensorLiftProofs
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def mixedIndex {N : ℕ} (k : ℕ) (i j : Fin N) : Fin (k+1) → Fin N :=
  Fin.cases i (fun _ ↦ j)

def diagonal {N : ℕ} (k : ℕ) (T : Model.Tensor N (k+1)) (j : Fin N) : ℝ :=
  T (fun _ ↦ j)

def coordinateLift {N : ℕ} (k : ℕ) (j : Fin N) (T : Model.Tensor N (k+1)) : Model.Vector N :=
  WithLp.toLp 2 (fun i ↦ T (mixedIndex k i j) /
    (|diagonal k T j| ^ ((k : ℝ)/((k+1 : ℕ) : ℝ))))

theorem diagonal_feature {N : ℕ} (k : ℕ) (x : Model.Vector N) (j : Fin N) :
    diagonal k (Model.feature (k+1) x) j = (x j)^(k+1) := by
  simp [diagonal, Geometry.feature_apply]

theorem mixedIndex_feature {N : ℕ} (k : ℕ) (x : Model.Vector N) (i j : Fin N) :
    Model.feature (k+1) x (mixedIndex k i j) = x i*(x j)^k := by
  rw [Geometry.feature_apply, Fin.prod_univ_succ]
  simp [mixedIndex]

theorem diagonal_denominator (k : ℕ) (a : ℝ) :
    |a^(k+1)| ^ ((k : ℝ)/((k+1 : ℕ) : ℝ)) = |a|^k := by
  rw [abs_pow, ← Real.rpow_natCast_mul (abs_nonneg a) (k+1)]
  have heq : ((k+1 : ℕ) : ℝ)*((k : ℝ)/((k+1 : ℕ) : ℝ)) = (k : ℝ) := by
    field_simp
  rw [heq, Real.rpow_natCast]

theorem coordinateLift_feature {N : ℕ} (k : ℕ) (x : Model.Vector N) (j : Fin N) :
    coordinateLift k j (Model.feature (k+1) x) = ((x j/|x j|)^k) • x := by
  ext i
  change Model.feature (k+1) x (mixedIndex k i j) /
    (|diagonal k (Model.feature (k+1) x) j| ^ ((k : ℝ)/((k+1 : ℕ) : ℝ))) =
      (x j/|x j|)^k*x i
  rw [mixedIndex_feature, diagonal_feature, diagonal_denominator, div_pow]
  ring

theorem ratio_abs_eq_one {a : ℝ} (ha : a ≠ 0) : |a/(|a|)| = 1 := by
  rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr ha)]

theorem coordinateLift_unit {N : ℕ} (k : ℕ) {x : Model.Vector N}
    (hx : x ∈ Model.unitSphere N) {j : Fin N} (hj : x j ≠ 0) :
    coordinateLift k j (Model.feature (k+1) x) ∈ Model.unitSphere N := by
  change ‖coordinateLift k j (Model.feature (k+1) x)‖ = 1
  rw [coordinateLift_feature, norm_smul, Real.norm_eq_abs, abs_pow,
    ratio_abs_eq_one hj, one_pow, one_mul, show ‖x‖ = 1 from hx]

theorem feature_coordinateLift {N : ℕ} (k : ℕ) (x : Model.Vector N)
    {j : Fin N} (hj : x j ≠ 0) :
    Model.feature (k+1) (coordinateLift k j (Model.feature (k+1) x)) =
      Model.feature (k+1) x := by
  rw [coordinateLift_feature, Geometry.feature_smul, ← pow_mul]
  have hsign : x j/|x j| = 1 ∨ x j/|x j| = -1 := by
    by_cases hpos : 0 < x j
    · left
      rw [abs_of_pos hpos, div_self hj]
    · right
      rw [abs_of_neg (lt_of_le_of_ne (le_of_not_gt hpos) hj), div_neg, div_self hj]
  rcases hsign with h | h
  · rw [h, one_pow, one_smul]
  · rw [h, (Nat.even_mul_succ_self k).neg_one_pow, one_smul]

theorem coordinateLift_measurable {N : ℕ} (k : ℕ) (j : Fin N) :
    Measurable (coordinateLift k j) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply measurable_pi_lambda
  intro i
  have hnum : Measurable (fun T : Model.Tensor N (k+1) ↦ T (mixedIndex k i j)) :=
    (PiLp.continuous_apply 2 (fun _ : (Fin (k+1) → Fin N) ↦ ℝ) _).measurable
  have hdiag : Continuous (fun T : Model.Tensor N (k+1) ↦ |diagonal k T j|) := by
    simpa only [diagonal] using
      (PiLp.continuous_apply 2 (fun _ : (Fin (k+1) → Fin N) ↦ ℝ) (fun _ ↦ j)).abs
  exact hnum.div ((Real.continuous_rpow_const (by positivity :
    0 ≤ (k : ℝ)/((k+1 : ℕ) : ℝ))).comp hdiag).measurable


/-- Every tensor has a terminating search because N is a sentinel; on the
nonzero rank-one image the search stops earlier at the least nonzero diagonal. -/
def searchPredicate {N : ℕ} (k j : ℕ) (T : Model.Tensor N (k+1)) : Prop :=
  if h : j < N then diagonal k T ⟨j, h⟩ ≠ 0 else True

theorem search_exists {N : ℕ} (k : ℕ) (T : Model.Tensor N (k+1)) :
    ∃ j : ℕ, searchPredicate k j T := ⟨N, by simp [searchPredicate]⟩

def liftCandidate {N : ℕ} (k j : ℕ) (T : Model.Tensor N (k+1)) : Model.Vector N :=
  if h : j < N then coordinateLift k ⟨j, h⟩ T else 0

def finiteLift {N : ℕ} (k : ℕ) (T : Model.Tensor N (k+1)) : Model.Vector N := by
  classical
  exact liftCandidate k (Nat.find (search_exists k T)) T

theorem liftCandidate_measurable {N : ℕ} (k j : ℕ) :
    Measurable (liftCandidate (N := N) k j) := by
  by_cases hj : j < N
  · have heq : liftCandidate (N := N) k j = coordinateLift k ⟨j, hj⟩ := by
      funext T
      simp only [liftCandidate, dif_pos hj]
    rw [heq]
    exact coordinateLift_measurable k ⟨j, hj⟩
  · have heq : liftCandidate (N := N) k j = (fun _ ↦ (0 : Model.Vector N)) := by
      funext T
      simp only [liftCandidate, dif_neg hj]
    rw [heq]
    exact measurable_const

theorem searchPredicate_measurable {N : ℕ} (k j : ℕ) :
    MeasurableSet {T : Model.Tensor N (k+1) | searchPredicate k j T} := by
  by_cases hj : j < N
  · have hd : Continuous (fun T : Model.Tensor N (k+1) ↦ diagonal k T ⟨j, hj⟩) := by
      exact PiLp.continuous_apply 2 (fun _ : (Fin (k+1) → Fin N) ↦ ℝ) _
    have hset : {T : Model.Tensor N (k+1) | searchPredicate k j T} =
        {T | diagonal k T ⟨j, hj⟩ = 0}ᶜ := by
      ext T
      simp only [searchPredicate, dif_pos hj, mem_compl_iff, mem_setOf_eq]
    rw [hset]
    exact (isClosed_eq hd continuous_const).measurableSet.compl
  · simp only [searchPredicate, dif_neg hj, setOf_true, MeasurableSet.univ]

theorem finiteLift_measurable (N k : ℕ) : Measurable (finiteLift (N := N) k) := by
  classical
  exact Measurable.find (liftCandidate_measurable k) (searchPredicate_measurable k)
    (search_exists k)

theorem finiteLift_feature_spec {N : ℕ} (k : ℕ) {x : Model.Vector N}
    (hx : x ∈ Model.unitSphere N) :
    finiteLift k (Model.feature (k+1) x) ∈ Model.unitSphere N ∧
      Model.feature (k+1) (finiteLift k (Model.feature (k+1) x)) = Model.feature (k+1) x := by
  classical
  have hxne : x ≠ 0 := by
    intro hz
    have hnorm : ‖x‖ = 1 := hx
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  have hcoord : ∃ j : Fin N, x j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hxne
    ext j
    exact h j
  obtain ⟨j, hj⟩ := hcoord
  have hjtest : searchPredicate k j.val (Model.feature (k+1) x) := by
    simp only [searchPredicate, dif_pos j.isLt, diagonal_feature]
    exact pow_ne_zero _ hj
  let m : ℕ := Nat.find (search_exists k (Model.feature (k+1) x))
  have hm : m < N := (Nat.find_min' (search_exists k (Model.feature (k+1) x)) hjtest).trans_lt j.isLt
  have hmtest := Nat.find_spec (search_exists k (Model.feature (k+1) x))
  change searchPredicate k m (Model.feature (k+1) x) at hmtest
  have hdiag : diagonal k (Model.feature (k+1) x) ⟨m, hm⟩ ≠ 0 := by
    simpa only [searchPredicate, dif_pos hm] using hmtest
  have hmcoord : x ⟨m, hm⟩ ≠ 0 := by
    intro hz
    rw [diagonal_feature, hz, zero_pow (Nat.succ_ne_zero k)] at hdiag
    exact hdiag rfl
  have hlift : finiteLift k (Model.feature (k+1) x) =
      coordinateLift k ⟨m, hm⟩ (Model.feature (k+1) x) := by
    change liftCandidate k m (Model.feature (k+1) x) = _
    simp only [liftCandidate, dif_pos hm]
  rw [hlift]
  exact ⟨coordinateLift_unit k hx hmcoord, feature_coordinateLift k x hmcoord⟩

end
end TensorPCA.TensorLiftProofs
