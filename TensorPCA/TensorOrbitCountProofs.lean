-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Model
public import Mathlib.Data.Fintype.Perm

/-! Exact permutation fibers of the literal injective ordered tensor tuples. -/
@[expose] public section
namespace TensorPCA.TensorOrbitCountProofs
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev DistinctTuple (N k : ℕ) := {i : Fin k → Fin N // Function.Injective i}

abbrev KSubset (N k : ℕ) := {S : Finset (Fin N) // S.card = k}

def tupleRange {N k : ℕ} (i : DistinctTuple N k) : KSubset N k :=
  ⟨Finset.univ.image i.1, by
    rw [Finset.card_image_of_injective _ i.2, Finset.card_univ, Fintype.card_fin]⟩

def tupleOfEquiv {N k : ℕ} {S : KSubset N k} (e : Fin k ≃ S.1) : DistinctTuple N k :=
  ⟨fun j ↦ (e j).1, fun _ _ h ↦ e.injective (Subtype.ext h)⟩

theorem tupleRange_tupleOfEquiv {N k : ℕ} {S : KSubset N k} (e : Fin k ≃ S.1) :
    tupleRange (tupleOfEquiv e) = S := by
  apply Subtype.ext
  ext n
  change n ∈ Finset.univ.image (fun j ↦ (e j).1) ↔ n ∈ S.1
  constructor
  · rintro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    exact (e j).2
  · intro hn
    obtain ⟨j, hj⟩ := e.surjective ⟨n,hn⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩

/-- Every tuple in a fixed range fiber is an actual enumeration of that set. -/
def rangeFiberEnumeration {N k : ℕ} (S : KSubset N k)
    (i : {i : DistinctTuple N k // tupleRange i = S}) : Fin k ≃ S.1 := by
  have hset : Finset.univ.image i.1.1 = S.1 := congrArg Subtype.val i.2
  let f : Fin k → S.1 := fun j ↦ ⟨i.1.1 j, by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    exact i.1.2 (congrArg Subtype.val hab)
  · intro n
    have hn : n.1 ∈ Finset.univ.image i.1.1 := by
      rw [hset]
      exact n.2
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hn
    exact ⟨j, Subtype.ext hj⟩

def rangeFiberEquiv {N k : ℕ} (S : KSubset N k) :
    {i : DistinctTuple N k // tupleRange i = S} ≃ (Fin k ≃ S.1) where
  toFun := rangeFiberEnumeration S
  invFun e := ⟨tupleOfEquiv e, tupleRange_tupleOfEquiv e⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    rfl

/-- Exactly k factorial injective ordered tuples have any prescribed k-set as
their range. The empty set/degree-zero fiber has its usual cardinal one. -/
theorem tupleRange_fiber_card {N k : ℕ} (S : KSubset N k) :
    Fintype.card {i : DistinctTuple N k // tupleRange i = S} = Nat.factorial k := by
  rw [Fintype.card_congr (rangeFiberEquiv S)]
  simpa only [Fintype.card_fin] using
    Fintype.card_equiv (S.1.equivFinOfCardEq S.2).symm

/-- A tensor monomial is constant on each permutation fiber. -/
theorem prod_tuple_eq_prod_range {M : Type*} [CommMonoid M] {N k : ℕ}
    (g : Fin N → M) (i : DistinctTuple N k) :
    (∏ j : Fin k, g (i.1 j)) = ∏ n ∈ (tupleRange i).1, g n := by
  symm
  exact Finset.prod_image (fun a _ b _ h ↦ i.2 h)

end
end TensorPCA.TensorOrbitCountProofs
