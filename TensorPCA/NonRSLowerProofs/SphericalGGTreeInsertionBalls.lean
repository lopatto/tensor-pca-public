-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionScore
public import TensorPCA.NonRSLowerProofs.FiniteNestedInsertionNumerators

/-! Concrete global ball anchors of a literal nested insertion choice.
Only one optional parent and a finite list of child balls are recorded;
all anchors are original old labels, not conditional laws. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionBalls
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open FiniteNestedPartitionInsertionBlocks FiniteOrderedPartitionSetoid
open SphericalGGTreeCylinder SphericalGGTreeInsertionSupport SphericalGGTreeInsertionScore
open FiniteNestedInsertionNumerators FiniteDiscountedPartitionProofs
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

theorem ballSize_succ_emb {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (l : Fin depth) (b : Fin c.length) (a : Fin (c.partSize b)) :
    ballSize (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) l.succ (c.emb b a)=
      ballSize (f b) l a := by
  classical
  have H : (∑j : Fin n,
      if (l.succ : ℕ)<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) j then (1 : ℕ) else 0)=
      ballSize (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) l.succ (c.emb b a) :=
    Finset.sum_boole _ _
  rw [← H]
  rw [← Fintype.sum_equiv c.equivSigma
    (fun s ↦ if (l.succ : ℕ)<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) (c.emb s.1 s.2)
      then (1 : ℕ) else 0)
    (fun j ↦ if (l.succ : ℕ)<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) j
      then (1 : ℕ) else 0) (fun _ ↦ rfl),Fintype.sum_sigma]
  have hBlock (d : Fin c.length) : (∑j : Fin (c.partSize d),
      if (l.succ : ℕ)<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) (c.emb d j)
        then (1 : ℕ) else 0)=if d=b then ballSize (f b) l a else 0 := by
    by_cases hdb : d=b
    · subst d
      simp only [coalescence_emb_same,Fin.val_succ,Nat.add_lt_add_iff_right,if_pos rfl]
      exact Finset.sum_boole _ _
    · have HC (j : Fin (c.partSize d)) :
          coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) (c.emb d j)=0 :=
        coalescence_cross c f (fun h ↦ hdb h.symm) a j
      simp only [HC,Nat.not_lt_zero,if_false,Finset.sum_const_zero,if_neg hdb]
  simp_rw [hBlock]
  simp

def liftBall {depth n : ℕ} (c : OrderedFinpartition n) (k : Fin c.length)
    (b : Fin depth×Fin (c.partSize k)) : Fin (depth+1)×Fin n :=
  (b.1.succ,c.emb k b.2)

def insertionBalls : (depth n : ℕ)→(t : NestedPartition depth n)→Insertion depth n t→
    Option (Fin depth×Fin n)×List (Fin depth×Fin n)
  | 0,_,_,_ => (none,[])
  | depth+1,_,⟨c,f⟩,none =>
      (none,List.ofFn (fun b : Fin c.length ↦ (0,c.emb b ⟨0,c.partSize_pos b⟩)))
  | depth+1,_,⟨c,f⟩,some ⟨k,o⟩ =>
      let child := insertionBalls depth (c.partSize k) (f k) o
      (some (child.1.elim (0,c.emb k ⟨0,c.partSize_pos k⟩) (liftBall c k)),
        child.2.map (liftBall c k))

def supportValue {depth n : ℕ} (s : Option (Fin depth×Fin n)×List (Fin depth×Fin n))
    (ball : Fin depth×Fin n→ℝ) (parent : ℝ) : ℝ :=
  s.1.elim parent ball-(s.2.map ball).sum

theorem supportValue_selected {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (k : Fin c.length) (o : Insertion depth (c.partSize k) (f k))
    (ball : Fin (depth+1)×Fin n→ℝ) (parent : ℝ) :
    supportValue (insertionBalls (depth+1) n ⟨c,f⟩ (some ⟨k,o⟩)) ball parent=
      supportValue (insertionBalls depth (c.partSize k) (f k) o)
        (fun b ↦ ball (liftBall c k b)) (ball (0,c.emb k ⟨0,c.partSize_pos k⟩)) := by
  simp only [insertionBalls,supportValue,Option.elim_some,List.map_map]
  cases (insertionBalls depth (c.partSize k) (f k) o).1 <;> rfl

theorem insertionBalls_negatives_length_le (depth n : ℕ) (t : NestedPartition depth n)
    (o : Insertion depth n t) : (insertionBalls depth n t o).2.length≤n := by
  induction depth generalizing n with
  | zero => simp [insertionBalls]
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none => simpa only [insertionBalls,List.length_ofFn] using c.length_le
    | some a =>
      obtain ⟨k,o⟩ := a
      simpa only [insertionBalls,List.length_map] using
        (ih (c.partSize k) (f k) o).trans (c.partSize_le k)

theorem insertionScore_eq_supportValue {N : ℕ} (depth n : ℕ) (cuts : Fin depth→ℝ)
    (t : NestedPartition depth n) (o : Insertion depth n t)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N) (parent : ℝ) :
    insertionScore depth n cuts t o old fresh parent=
      supportValue (insertionBalls depth n t o)
        (fun b ↦ if cuts b.1≤unitOverlap fresh (old b.2) then 1 else 0) parent := by
  induction depth generalizing n parent with
  | zero => simp [insertionScore,insertionBalls,supportValue]
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none => simp [insertionScore,insertionBalls,supportValue,List.map_ofFn,List.sum_ofFn]
    | some a =>
      obtain ⟨k,o⟩ := a
      rw [supportValue_selected]
      simpa only [insertionScore,liftBall] using
        ih (c.partSize k) (fun l ↦ cuts l.succ) (f k) o (fun a ↦ old (c.emb k a))
          (if cuts 0≤unitOverlap fresh (old (c.emb k ⟨0,c.partSize_pos k⟩)) then 1 else 0)

/-- Full-size parent normalization. At the physical root parent=0, the
positive parent coefficient is exactly the FULL old replica count n. -/
theorem supportValue_ballSize_sub_eq_numerator (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    supportValue (insertionBalls depth n t o)
      (fun b ↦ (ballSize t b.1 b.2 : ℝ)-x b.1) ((n : ℝ)-p)=
      numerator depth n x p t o := by
  induction depth generalizing n p with
  | zero => simp [insertionBalls,supportValue,numerator]
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none =>
      simp only [insertionBalls,supportValue,Option.elim_none,List.map_ofFn,List.sum_ofFn,Function.comp_apply,numerator,
        ballSize_zero_emb c f]
      have hSizes : (∑b : Fin c.length,(c.partSize b : ℝ))=(n : ℝ) := by
        exact_mod_cast sum_partSize c
      rw [Finset.sum_sub_distrib,hSizes]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    | some a =>
      obtain ⟨k,o⟩ := a
      rw [supportValue_selected]
      simp only [numerator]
      simpa only [liftBall,ballSize_succ_emb c f,ballSize_zero_emb c f] using
        ih (c.partSize k) (fun l ↦ x l.succ) (x 0) (f k) o


end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionBalls
