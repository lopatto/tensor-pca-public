-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Model

/-! A collision union bound for the literal ordered tensor coordinates. -/
@[expose] public section
namespace TensorPCA.TensorTupleCountProofs
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def repeatedTuples (N k : ℕ) : Finset (Fin k → Fin N) :=
  Finset.univ.filter (fun f ↦ ¬ Function.Injective f)

def collisionTuples (N k : ℕ) (i j : Fin k) : Finset (Fin k → Fin N) :=
  Finset.univ.filter (fun f ↦ i ≠ j ∧ f i = f j)

theorem collisionTuples_card_le (N k : ℕ) (i j : Fin k) :
    (collisionTuples N k i j).card ≤ N^(k-1) := by
  classical
  by_cases hij : i = j
  · simp [collisionTuples, hij]
  let S : Finset (Fin k) := Finset.univ.erase j
  let restrict : collisionTuples N k i j → (S → Fin N) := fun f a ↦ f.1 a.1
  have hr : Function.Injective restrict := by
    intro f g h
    apply Subtype.ext
    funext a
    have hf := (Finset.mem_filter.mp f.2).2.2
    have hg := (Finset.mem_filter.mp g.2).2.2
    by_cases ha : a = j
    · subst a
      calc
        f.1 j = f.1 i := hf.symm
        _ = g.1 i := congrFun h ⟨i, by simp [S, hij]⟩
        _ = g.1 j := hg
    · exact congrFun h ⟨a, by simp [S, ha]⟩
  have hc := Fintype.card_le_of_injective restrict hr
  simpa only [Fintype.card_coe, Fintype.card_fun, S, Finset.card_erase_of_mem
    (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin] using hc

theorem repeatedTuples_eq_collision_union (N k : ℕ) :
    repeatedTuples N k = (Finset.univ : Finset (Fin k × Fin k)).biUnion
      (fun p ↦ collisionTuples N k p.1 p.2) := by
  classical
  ext f
  simp only [repeatedTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, collisionTuples]
  constructor
  · intro hf
    obtain ⟨i, j, he, hij⟩ := Function.not_injective_iff.mp hf
    exact ⟨(i,j), hij, he⟩
  · rintro ⟨⟨i,j⟩, hij, he⟩ hf
    exact hij (hf he)

/-- At most k squared times N to the k-minus-one ordered tensor coordinates
contain a repeated index. The degree-zero and degree-one cases are included. -/
theorem repeatedTuples_card_le (N k : ℕ) :
    (repeatedTuples N k).card ≤ k^2*N^(k-1) := by
  classical
  rw [repeatedTuples_eq_collision_union]
  have h := Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset (Fin k × Fin k))
    (fun p ↦ collisionTuples N k p.1 p.2) (N^(k-1))
    (fun p _ ↦ collisionTuples_card_le N k p.1 p.2)
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two] using h

theorem repeatedTuples_zero (N : ℕ) : repeatedTuples N 0 = ∅ := by
  classical
  ext f
  simp [repeatedTuples, Function.Injective]

theorem repeatedTuples_one (N : ℕ) : repeatedTuples N 1 = ∅ := by
  classical
  ext f
  simp [repeatedTuples, Function.Injective]

end
end TensorPCA.TensorTupleCountProofs
