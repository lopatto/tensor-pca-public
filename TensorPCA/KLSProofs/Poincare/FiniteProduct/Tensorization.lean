-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Poincare.FiniteProduct.Geometry
public import TensorPCA.KLSProofs.Poincare.Product.Tensorization
public import TensorPCA.KLSProofs.Poincare.SmoothTest.Transport

/-!
# Finite Poincaré tensorization and optimal-constant equality

Node: `lem:poincare-finite-tensorization`. All conclusions concern the unchanged
globally smooth L² finite-canonical-gradient-energy test class. Finite constants are
`NNReal`, cast to `ℝ` for `Holds`. Infinite values occur only in the `ENNReal` layer.

Source: the Poincaré product identity in the historical manuscript's
[Theorem 3.4](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L59-L68).
The source states that the product optimal constant is the maximum of the factor constants,
and cites BGL. Its LSI and conditional-decomposition assertions are outside this module.
For the upper bound we iterate
[BGL Proposition 4.3.1, pp. 185–187](https://doi.org/10.1007/978-3-319-00227-9)
through the local theorem `Holds.prod`; coordinate tests supply the reverse direction.

The dependent `PiLp 2` carrier, arbitrary Borel Hilbert factors, explicit finite-energy tests,
empty index type, zero-dimensional spaces, and `ENNReal` boundary cases are local
specifications. They are not additional hypotheses or separate assertions quoted from the
manuscript. No identification with its spectral-gap interpretation is made here.
-/

@[expose] public section

noncomputable section

open MeasureTheory

/- The unused ambient instances are retained in the candidate signatures. -/

namespace TensorPCA.KLSProofs.Poincare.SmoothTest

universe uι uE

/-- The fixed-constant statement, quantified over all data so that
`Fintype.induction_empty_option` can recurse on the index type alone. -/
private def PiStatement (ι : Type uι) [Fintype ι] : Prop :=
  ∀ (E : ι → Type uE) [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)] (C : ι → NNReal),
    (∀ i, Holds (μ i) (C i : ℝ)) →
    Holds (piMeasure μ) ((Finset.univ.sup C : NNReal) : ℝ)

/- Transport the local `Fintype` instance along the index equivalence. -/
private theorem piStatement (ι : Type uι) [Fintype ι] : PiStatement.{uι, uE} ι := by
  refine Fintype.induction_empty_option
    (P := fun α inst ↦ @PiStatement.{uι, uE} α inst) ?_ ?_ ?_ ι
  · -- transport along an index equivalence via dependent reindexing
    intro α β hβ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    intro E _ _ _ _ _ _ μ _ C h
    have h' := ih (fun j ↦ E (e j)) (fun j ↦ μ (e j)) (fun j ↦ C (e j)) (fun j ↦ h (e j))
    have h2 := (holds_map_linearIsometryEquiv_iff (piCongrLeft E e)
      (piMeasure fun j ↦ μ (e j))).mpr h'
    rw [map_piMeasure_piCongrLeft E e μ] at h2
    have hsup : Finset.univ.sup (fun j ↦ C (e j)) = Finset.univ.sup C := by
      have hmap := Finset.sup_map (Finset.univ : Finset α) e.toEmbedding C
      rw [Finset.map_univ_equiv] at hmap
      exact hmap.symm
    rwa [hsup] at h2
  · -- the empty product is a probability law on a subsingleton Hilbert space
    intro E _ _ _ _ _ _ μ _ C h
    have : Subsingleton (PiLp 2 E) :=
      (WithLp.linearEquiv 2 ℝ (∀ i, E i)).toEquiv.subsingleton
    have hsup : Finset.univ.sup C = 0 := by simp [Finset.univ_eq_empty]
    rw [hsup]
    simpa using holds_zero_of_subsingleton (piMeasure μ)
  · -- split off the head coordinate and use the binary upper bound
    intro α hα ih E _ _ _ _ _ _ μ _ C h
    have htail := ih (fun i ↦ E (some i)) (fun i ↦ μ (some i)) (fun i ↦ C (some i))
      (fun i ↦ h (some i))
    have hprod := (h none).prod htail
    rw [← map_piMeasure_piOptionEquivProd E μ] at hprod
    have h2 := (holds_map_linearIsometryEquiv_iff (piOptionEquivProd E)
      (piMeasure μ)).mp hprod
    have hsup : Finset.univ.sup C
        = max (C none) (Finset.univ.sup fun i ↦ C (some i)) := by
      apply le_antisymm
      · refine Finset.sup_le fun o _ ↦ ?_
        cases o with
        | none => exact le_sup_left
        | some i =>
            exact le_sup_of_le_right
              (Finset.le_sup (f := fun i ↦ C (some i)) (Finset.mem_univ i))
      · exact sup_le (Finset.le_sup (Finset.mem_univ none))
          (Finset.sup_le fun i _ ↦ Finset.le_sup (Finset.mem_univ (some i)))
    have hconst : ((Finset.univ.sup C : NNReal) : ℝ)
        = max ((C none : NNReal) : ℝ)
            ((Finset.univ.sup (fun i ↦ C (some i)) : NNReal) : ℝ) := by
      rw [hsup, NNReal.coe_max]
    rw [hconst]
    exact h2

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
  {μ : ∀ i, Measure (E i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- Source: finite iteration of `Holds.prod` (BGL Proposition 4.3.1), using local isometry
transport. This is the fixed-constant upper bound used for the manuscript's Theorem 3.4.
The `NNReal` finite supremum and its empty value zero are explicit local specifications. -/
theorem Holds.pi {C : ι → NNReal} (h : ∀ i, Holds (μ i) (C i : ℝ)) :
    Holds (piMeasure μ) ((Finset.univ.sup C : NNReal) : ℝ) :=
  piStatement ι E μ C h

/-- Recover any factor at the product's finite real constant by lifting its tests.
Source: local coordinate-test deduction using `Admissible.comp_projection` and
`measurePreserving_pi_proj`; all factor probabilities are present. -/
theorem Holds.of_pi {C : ℝ} (h : Holds (piMeasure μ) C) (i : ι) :
    Holds (μ i) C := by
  refine ⟨inferInstance, h.constant_nonneg, fun f hf ↦ ?_⟩
  have hlift : Admissible (piMeasure μ) (f ∘ (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i)) :=
    Admissible.comp_projection _ (isometry_adjoint_pi_proj i)
      (measurePreserving_pi_proj μ i) hf
  have hv := h.variance_le hlift
  rwa [variance_comp_projection _ (measurePreserving_pi_proj μ i) hf.memLp_two,
    energy_comp_projection _ (isometry_adjoint_pi_proj i)
      (measurePreserving_pi_proj μ i) hf] at hv

/-- Source: local infimum consequence of `Holds.of_pi`, providing the coordinate lower
bound for the manuscript's Theorem 3.4. -/
theorem constant_le_pi (i : ι) : constant (μ i) ≤ constant (piMeasure μ) :=
  le_constant fun _ hC ↦ constant_le (hC.of_pi i)

/-- Source: local `ENNReal` infimum consequence of `Holds.pi`, giving the upper direction
of the manuscript's Theorem 3.4. The proof uses finite valid approximants without an
attainment assumption; it makes no claim that a finite optimal constant fails to be valid. -/
theorem constant_pi_le : constant (piMeasure μ) ≤ ⨆ i, constant (μ i) := by
  by_contra hcon
  rw [not_le] at hcon
  have hbot : (⊥ : ENNReal) < constant (piMeasure μ) := bot_le.trans_lt hcon
  have hex : ∀ i, ∃ c : {c : NNReal // Holds (μ i) (c : ℝ)},
      (c.1 : ENNReal) < constant (piMeasure μ) := by
    intro i
    have hi : constant (μ i) < constant (piMeasure μ) :=
      lt_of_le_of_lt (le_iSup (fun i ↦ constant (μ i)) i) hcon
    rw [constant] at hi
    exact iInf_lt_iff.mp hi
  choose c hc using hex
  have hpi : Holds (piMeasure μ) ((Finset.univ.sup fun i ↦ (c i).1 : NNReal) : ℝ) :=
    Holds.pi fun i ↦ (c i).2
  have hle := constant_le hpi
  have hcoe : (((Finset.univ.sup fun i ↦ (c i).1 : NNReal)) : ENNReal)
      = Finset.univ.sup fun i ↦ ((c i).1 : ENNReal) := by
    exact Finset.apply_sup_eq_sup_comp ((↑) : NNReal → ENNReal)
      (fun x y ↦ ENNReal.coe_mono.map_sup x y) (by simp)
  rw [hcoe] at hle
  have hlt : (Finset.univ.sup fun i ↦ ((c i).1 : ENNReal)) < constant (piMeasure μ) :=
    (Finset.sup_lt_iff hbot).mpr fun i _ ↦ hc i
  exact absurd (hle.trans_lt hlt) (lt_irrefl _)

/-- Source: the Poincaré product identity of manuscript Theorem 3.4, linked above.
Here its finite maximum is expressed as an `ENNReal` indexed supremum, allowing the empty
family and infinite values. The exact test class and Hilbert encoding are local to this API. -/
theorem constant_pi_eq : constant (piMeasure μ) = ⨆ i, constant (μ i) :=
  le_antisymm constant_pi_le (iSup_le fun i ↦ constant_le_pi i)

section EmptyProducts

omit [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)]
/-- Source: local empty-family consequence of `holds_zero_of_subsingleton`.
The manuscript does not separately state an empty-product fixed constant. -/
theorem holds_pi_empty [IsEmpty ι] : Holds (piMeasure μ) 0 := by
  have : Subsingleton (PiLp 2 E) :=
    (WithLp.linearEquiv 2 ℝ (∀ i, E i)).toEquiv.subsingleton
  exact holds_zero_of_subsingleton (piMeasure μ)

/-- Source: local empty-family consequence of `constant_eq_zero_of_subsingleton`.
This makes the empty-product boundary of the indexed-supremum formula explicit. -/
theorem constant_pi_empty [IsEmpty ι] : constant (piMeasure μ) = 0 := by
  have : Subsingleton (PiLp 2 E) :=
    (WithLp.linearEquiv 2 ℝ (∀ i, E i)).toEquiv.subsingleton
  exact constant_eq_zero_of_subsingleton (piMeasure μ)

end EmptyProducts

/-- A one-coordinate dependent family needs no chosen identification of its ambient space.
Source: local specialization of `constant_pi_eq` using `iSup_unique`. -/
theorem constant_pi_unique [Unique ι] : constant (piMeasure μ) = constant (μ default) := by
  rw [constant_pi_eq]
  exact iSup_unique fun i ↦ constant (μ i)

omit [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)] in
/-- Any family of zero-dimensional factors, including the empty family.
Source: local boundary consequence of `constant_eq_zero_of_subsingleton`, not a separate
manuscript theorem. -/
theorem constant_pi_of_subsingleton [∀ i, Subsingleton (E i)] :
    constant (piMeasure μ) = 0 := by
  have : Subsingleton (PiLp 2 E) :=
    (WithLp.linearEquiv 2 ℝ (∀ i, E i)).toEquiv.subsingleton
  exact constant_eq_zero_of_subsingleton (piMeasure μ)

/-- An infinite factor constant forces an infinite product constant, without `toReal`.
Source: local extended-real consequence of `constant_le_pi`; the manuscript does not spell
out this infinite-value boundary separately. -/
theorem constant_pi_eq_top_of_factor (i : ι) (hi : constant (μ i) = ⊤) :
    constant (piMeasure μ) = ⊤ :=
  top_unique (hi ▸ constant_le_pi i)

end TensorPCA.KLSProofs.Poincare.SmoothTest
