-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.TensorOrbitCountProofs

/-! Exact old-coordinate and last-coordinate decomposition of tensor k-sets. -/
@[expose] public section
namespace TensorPCA.TensorCavitySubsetProofs
open TensorOrbitCountProofs
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def oldPart {N : ℕ} (S : Finset (Fin (N+1))) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ i.castSucc ∈ S)

theorem last_not_mem_image_castSucc {N : ℕ} (S : Finset (Fin N)) :
    Fin.last N ∉ S.image Fin.castSucc := by
  rintro h
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  exact i.castSucc_ne_last hi

theorem image_oldPart {N : ℕ} (S : Finset (Fin (N+1))) :
    (oldPart S).image Fin.castSucc = S.erase (Fin.last N) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Finset.mem_image, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      iff_false]
    rintro ⟨j,_,hj⟩
    exact j.castSucc_ne_last hj
  · simp [oldPart, Finset.mem_image, Fin.castSucc_inj, Fin.castSucc_ne_last]

theorem oldPart_image {N : ℕ} (S : Finset (Fin N)) :
    oldPart (S.image Fin.castSucc) = S := by
  ext i
  simp [oldPart, Finset.mem_image, Fin.castSucc_inj]

theorem oldPart_insert_last {N : ℕ} (S : Finset (Fin (N+1))) :
    oldPart (insert (Fin.last N) S) = oldPart S := by
  ext i
  simp [oldPart, Fin.castSucc_ne_last]

def oldSubset {N k : ℕ} (S : KSubset N k) : KSubset (N+1) k :=
  ⟨S.1.image Fin.castSucc, by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective N), S.2]⟩

def lastSubset {N k : ℕ} (hk : 0 < k) (S : KSubset N (k-1)) : KSubset (N+1) k :=
  ⟨insert (Fin.last N) (S.1.image Fin.castSucc), by
    rw [Finset.card_insert_of_notMem (last_not_mem_image_castSucc S.1),
      Finset.card_image_of_injective _ (Fin.castSucc_injective N), S.2]
    omega⟩

def joinSubset {N k : ℕ} (hk : 0 < k) :
    KSubset N k ⊕ KSubset N (k-1) → KSubset (N+1) k :=
  Sum.elim oldSubset (lastSubset hk)

theorem joinSubset_injective {N k : ℕ} (hk : 0 < k) :
    Function.Injective (joinSubset (N := N) hk) := by
  intro a b hab
  cases a with
  | inl S =>
    cases b with
    | inl T =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact Finset.image_injective (Fin.castSucc_injective N) (congrArg Subtype.val hab)
    | inr T =>
      have hlast : Fin.last N ∈ (oldSubset S).1 := by
        rw [show oldSubset S = lastSubset hk T from hab]
        exact Finset.mem_insert_self _ _
      exact False.elim (last_not_mem_image_castSucc S.1 hlast)
  | inr S =>
    cases b with
    | inl T =>
      have hlast : Fin.last N ∈ (oldSubset T).1 := by
        rw [← show lastSubset hk S = oldSubset T from hab]
        exact Finset.mem_insert_self _ _
      exact False.elim (last_not_mem_image_castSucc T.1 hlast)
    | inr T =>
      apply congrArg Sum.inr
      apply Subtype.ext
      have h := congrArg (fun U : KSubset (N+1) k ↦ oldPart U.1) hab
      simpa only [joinSubset, Sum.elim_inr, lastSubset, oldPart_insert_last, oldPart_image] using h

theorem joinSubset_surjective {N k : ℕ} (hk : 0 < k) :
    Function.Surjective (joinSubset (N := N) hk) := by
  intro S
  have hc : (oldPart S.1).card = (S.1.erase (Fin.last N)).card := by
    rw [← image_oldPart, Finset.card_image_of_injective _ (Fin.castSucc_injective N)]
  by_cases hlast : Fin.last N ∈ S.1
  · have hcard : (oldPart S.1).card = k-1 := by rw [hc, Finset.card_erase_of_mem hlast, S.2]
    refine ⟨Sum.inr ⟨oldPart S.1,hcard⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (insert (Fin.last N)) (image_oldPart S.1)).trans (Finset.insert_erase hlast)
  · have hcard : (oldPart S.1).card = k := by rw [hc, Finset.erase_eq_of_notMem hlast, S.2]
    refine ⟨Sum.inl ⟨oldPart S.1,hcard⟩, ?_⟩
    apply Subtype.ext
    exact (image_oldPart S.1).trans (Finset.erase_eq_of_notMem hlast)

/-- All k-sets of N+1 coordinates split into the disjoint old-coordinate
k-sets and the k-sets containing the last coordinate. This also covers N=0. -/
def subsetSplitEquiv {N k : ℕ} (hk : 0 < k) :
    KSubset (N+1) k ≃ KSubset N k ⊕ KSubset N (k-1) :=
  (Equiv.ofBijective (joinSubset hk) ⟨joinSubset_injective hk,joinSubset_surjective hk⟩).symm

theorem subsetSplitEquiv_symm_inl {N k : ℕ} (hk : 0 < k) (S : KSubset N k) :
    (subsetSplitEquiv hk).symm (Sum.inl S) = oldSubset S := rfl

theorem subsetSplitEquiv_symm_inr {N k : ℕ} (hk : 0 < k) (S : KSubset N (k-1)) :
    (subsetSplitEquiv hk).symm (Sum.inr S) = lastSubset hk S := rfl

theorem prod_oldSubset {M : Type*} [CommMonoid M] {N k : ℕ}
    (g : Fin (N+1) → M) (S : KSubset N k) :
    (∏ i ∈ (oldSubset S).1, g i) = ∏ j ∈ S.1, g j.castSucc := by
  exact Finset.prod_image (fun a _ b _ h ↦ Fin.castSucc_inj.mp h)

theorem prod_lastSubset {M : Type*} [CommMonoid M] {N k : ℕ} (hk : 0 < k)
    (g : Fin (N+1) → M) (S : KSubset N (k-1)) :
    (∏ i ∈ (lastSubset hk S).1, g i) = g (Fin.last N)*(∏ j ∈ S.1, g j.castSucc) := by
  change (∏ i ∈ insert (Fin.last N) (S.1.image Fin.castSucc), g i) = _
  rw [Finset.prod_insert (last_not_mem_image_castSucc S.1)]
  congr 1
  exact Finset.prod_image (fun a _ b _ h ↦ Fin.castSucc_inj.mp h)

end
end TensorPCA.TensorCavitySubsetProofs
