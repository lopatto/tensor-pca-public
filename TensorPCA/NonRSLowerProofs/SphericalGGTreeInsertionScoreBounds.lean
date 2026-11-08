-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionBalls

/-! Insertion-score measurability and uniform bad-array loss. Gaussian GG residual
integration is treated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionScoreBounds
open MeasureTheory Set
open FiniteNestedPartition SphericalGGTreeCylinder SphericalGGTreeExtraction
open SphericalGGTreeInsertionScore SphericalGGTreeInsertionBalls
open NonRSUpperProofs.SphericalPositivePerturbation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

private theorem sum_ball_bounds {A : Type*} (L : List A) (ball : A→ℝ)
    (hball : ∀a,0≤ball a ∧ ball a≤1) :
    0≤(L.map ball).sum ∧ (L.map ball).sum≤(L.length : ℝ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact ⟨add_nonneg (hball a).1 ih.1,by linarith [(hball a).2,ih.2]⟩

theorem insertionScore_abs_le {N : ℕ} (depth n : ℕ) (cuts : Fin depth→ℝ)
    (t : NestedPartition depth n) (o : Insertion depth n t)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N) :
    |insertionScore depth n cuts t o old fresh 1|≤(n : ℝ)+1 := by
  let S := insertionBalls depth n t o
  let ball := fun b : Fin depth×Fin n ↦
    if cuts b.1≤unitOverlap fresh (old b.2) then (1 : ℝ) else 0
  have hb (b : Fin depth×Fin n) : 0≤ball b ∧ ball b≤1 := by
    dsimp only [ball]
    split <;> norm_num
  have hSum := sum_ball_bounds S.2 ball hb
  have hParent : 0≤S.1.elim 1 ball ∧ S.1.elim 1 ball≤1 := by
    cases HS : S.1 with
    | none => simp
    | some b => simpa only [Option.elim_some] using hb b
  have hLen : (S.2.length : ℝ)≤n := by
    exact_mod_cast insertionBalls_negatives_length_le depth n t o
  rw [insertionScore_eq_supportValue]
  change |S.1.elim 1 ball-(S.2.map ball).sum|≤(n : ℝ)+1
  apply abs_le.mpr
  constructor <;> linarith [hParent.1,hParent.2,hSum.1,hSum.2,Nat.cast_nonneg (α := ℝ) n]

private theorem ball_measurable {N depth n : ℕ} (cuts : Fin depth→ℝ) (b : Fin depth×Fin n) :
    Measurable (fun p : (Fin n→UnitSpin N)×UnitSpin N ↦
      if cuts b.1≤unitOverlap p.2 (p.1 b.2) then (1 : ℝ) else 0) := by
  have hR : Measurable (fun p : (Fin n→UnitSpin N)×UnitSpin N ↦ unitOverlap p.2 (p.1 b.2)) :=
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp
      (measurable_snd.prodMk ((measurable_pi_apply b.2).comp measurable_fst))
  exact Measurable.ite (measurableSet_le measurable_const hR) measurable_const measurable_const

private theorem ball_list_sum_measurable {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (L : List (Fin depth×Fin n)) :
    Measurable (fun p : (Fin n→UnitSpin N)×UnitSpin N ↦
      (L.map (fun b ↦ if cuts b.1≤unitOverlap p.2 (p.1 b.2) then (1 : ℝ) else 0)).sum) := by
  induction L with
  | nil => simpa only [List.map_nil,List.sum_nil] using (measurable_const : Measurable (fun _ : (Fin n→UnitSpin N)×UnitSpin N ↦ (0 : ℝ)))
  | cons b L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (ball_measurable cuts b).add ih

theorem insertionScore_joint_measurable {N : ℕ} (depth n : ℕ) (cuts : Fin depth→ℝ)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    Measurable (fun p : (Fin n→UnitSpin N)×UnitSpin N ↦
      insertionScore depth n cuts t o p.1 p.2 1) := by
  let S := insertionBalls depth n t o
  have hParent : Measurable (fun p : (Fin n→UnitSpin N)×UnitSpin N ↦
      S.1.elim 1 (fun b ↦ if cuts b.1≤unitOverlap p.2 (p.1 b.2) then (1 : ℝ) else 0)) := by
    cases HS : S.1 with
    | none => simpa only [Option.elim_none] using (measurable_const : Measurable (fun _ : (Fin n→UnitSpin N)×UnitSpin N ↦ (1 : ℝ)))
    | some b => simpa only [Option.elim_some] using ball_measurable cuts b
  simp_rw [insertionScore_eq_supportValue]
  exact hParent.sub (ball_list_sum_measurable cuts S.2)

theorem insertion_indicator_error_le_bad {N : ℕ} (depth n : ℕ) (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N) :
    |(if treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) (Fin.cons fresh old) then (1 : ℝ) else 0)-
      (if treeCylinder cuts t old then (1 : ℝ) else 0)*insertionScore depth n cuts t o old fresh 1|≤
      ((n : ℝ)+2)*(if ¬thresholdGood cuts (Fin.cons fresh old) then (1 : ℝ) else 0) := by
  by_cases hg : thresholdGood cuts (Fin.cons fresh old)
  · rw [insertion_indicator_eq depth n cuts hcuts hcuts1 t o old fresh hg]
    simp only [sub_self,abs_zero,if_neg (not_not_intro hg),mul_zero,le_refl]
  · rw [if_pos hg]
    have hNew : |if treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) (Fin.cons fresh old)
        then (1 : ℝ) else 0|≤1 := by split <;> norm_num
    have hOld : |if treeCylinder cuts t old then (1 : ℝ) else 0|≤1 := by split <;> norm_num
    have hScore := insertionScore_abs_le depth n cuts t o old fresh
    calc
      _≤|if treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) (Fin.cons fresh old) then (1 : ℝ) else 0|+
          |(if treeCylinder cuts t old then (1 : ℝ) else 0)*insertionScore depth n cuts t o old fresh 1| := abs_sub _ _
      _≤1+((n : ℝ)+1) := by
        apply add_le_add hNew
        rw [abs_mul]
        exact (mul_le_mul hOld hScore (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _=((n : ℝ)+2)*1 := by ring

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionScoreBounds
