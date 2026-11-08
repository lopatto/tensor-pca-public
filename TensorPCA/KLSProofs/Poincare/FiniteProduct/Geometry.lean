-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/FiniteProduct/Geometry.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Poincare.Product.Geometry
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Dependent finite Hilbert products

`PiLp 2 E` has the sum-of-squares Hilbert norm. The ordinary dependent function space
is used only to construct its probability law and linear equivalences.

Source: local encodings and compatibility helpers; `piMeasure`, dependent reindexing, and the
`none`-then-tail split are not separate constructions stated in the tensorization reference.
Historical API references in the upstream source use Mathlib v4.33.0. This port is
checked with the toolchain and Mathlib revision pinned in this repository:
[finite Hilbert inner product](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/PiL2.lean),
[finite L² norm](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Normed/Lp/PiLp.lean),
[linear product equivalences](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Pi.lean),
[dependent product measures](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Constructions/Pi.lean),
and [transported measurable structures](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean).
-/

@[expose] public section

noncomputable section

open MeasureTheory


namespace TensorPCA.KLSProofs.Poincare.SmoothTest

/-- The dependent finite product law on the Hilbert product, including the empty family.
Source: local encoding of Mathlib's `Measure.pi` transported through `WithLp.toLp 2`. -/
def piMeasure {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) : Measure (PiLp 2 E) :=
  (Measure.pi μ).map (WithLp.toLp 2)

/-- Source: local helper from Mathlib's probability instance for `Measure.pi`,
`WithLp.measurable_toLp`, and `Measure.isProbabilityMeasure_map`. -/
instance piMeasure_isProbabilityMeasure {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (piMeasure μ) := by
  rw [piMeasure]
  exact (Measure.isProbabilityMeasure_map_iff (WithLp.measurable_toLp 2 (∀ i, E i)).aemeasurable).2 inferInstance

section Coordinates

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

omit [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)] in
omit [(i : ι) → MeasurableSpace (E i)] in
/-- The adjoint inserts a vector in one coordinate and zero in all other coordinates.
Source: local helper from Mathlib's `ContinuousLinearMap.adjoint_inner_left`,
`PiLp.inner_apply`, and `PiLp.single`. -/
theorem adjoint_pi_proj [DecidableEq ι] (i : ι) (v : E i) :
    (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i).adjoint v = PiLp.single 2 i v := by
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [PiLp.single_eq_of_ne _ hj]
    exact inner_zero_left _
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)] in
omit [(i : ι) → MeasurableSpace (E i)] in
/-- Source: local consequence of `adjoint_pi_proj` and Mathlib's `PiLp.norm_single`. -/
theorem isometry_adjoint_pi_proj (i : ι) :
    Isometry (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i).adjoint := by
  classical
  refine AddMonoidHomClass.isometry_of_norm _ fun v ↦ ?_
  rw [adjoint_pi_proj i v]
  exact PiLp.norm_single 2 E i v

omit [∀ (i : ι), CompleteSpace (E i)] in
/-- Source: local transport of Mathlib's `measurePreserving_eval` through `WithLp.toLp 2`;
every factor retains its probability normalization. -/
theorem measurePreserving_pi_proj (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i) (piMeasure μ) (μ i) := by
  refine ⟨(PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i).continuous.measurable, ?_⟩
  rw [piMeasure, Measure.map_map
    (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i).continuous.measurable
    (WithLp.measurable_toLp 2 (∀ i, E i))]
  exact (measurePreserving_eval μ i).map_eq

end Coordinates

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

/-- Dependent reindexing; Mathlib's `LinearIsometryEquiv.piLpCongrLeft` is homogeneous.
Source: local encoding using `LinearEquiv.piCongrLeft`, `WithLp.linearEquiv`, and
`PiLp.norm_sq_eq_of_L2`; this construction is not separately stated in BGL. -/
def piCongrLeft (e : κ ≃ ι) : (PiLp 2 fun j ↦ E (e j)) ≃ₗᵢ[ℝ] PiLp 2 E where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ _).trans
    ((LinearEquiv.piCongrLeft ℝ E e).trans (WithLp.linearEquiv 2 ℝ _).symm)
  norm_map' := by
    intro x
    show ‖(WithLp.toLp 2 ((Equiv.piCongrLeft E e) (WithLp.ofLp x)) : PiLp 2 E)‖ = ‖x‖
    have hsq : ‖(WithLp.toLp 2 ((Equiv.piCongrLeft E e) (WithLp.ofLp x)) : PiLp 2 E)‖ ^ 2
        = ‖x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, ← e.sum_comp fun i ↦
        ‖(WithLp.toLp 2 ((Equiv.piCongrLeft E e) (WithLp.ofLp x)) : PiLp 2 E) i‖ ^ 2]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      show ‖(Equiv.piCongrLeft E e) (WithLp.ofLp x) (e j)‖ ^ 2 = ‖(WithLp.ofLp x) j‖ ^ 2
      rw [Equiv.piCongrLeft_apply_apply]
    have hn := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hn

/-- Source: local application rule for `piCongrLeft`, inherited from Mathlib's
`Equiv.piCongrLeft_apply_apply`. -/
theorem piCongrLeft_apply (e : κ ≃ ι) (x : PiLp 2 fun j ↦ E (e j)) (j : κ) :
    piCongrLeft E e x (e j) = x j :=
  Equiv.piCongrLeft_apply_apply E e (WithLp.ofLp x) j

variable [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

omit [∀ (i : ι), CompleteSpace (E i)] in
/-- Source: local compatibility helper from Mathlib's `Measure.pi_map_piCongrLeft` and
`Measure.map_map`, for the dependent Hilbert-product encoding. -/
theorem map_piMeasure_piCongrLeft (e : κ ≃ ι) (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (piMeasure (fun j ↦ μ (e j))).map (piCongrLeft E e) = piMeasure μ := by
  rw [piMeasure, piMeasure,
    Measure.map_map (piCongrLeft E e).continuous.measurable
      (WithLp.measurable_toLp 2 (∀ j, E (e j)))]
  have hfun : (⇑(piCongrLeft E e) ∘
        (WithLp.toLp 2 : (∀ j, E (e j)) → PiLp 2 fun j ↦ E (e j)))
      = ((WithLp.toLp 2 : (∀ i, E i) → PiLp 2 E)
          ∘ ⇑(MeasurableEquiv.piCongrLeft E e)) := rfl
  rw [hfun, ← Measure.map_map (WithLp.measurable_toLp 2 (∀ i, E i))
    (MeasurableEquiv.piCongrLeft E e).measurable,
    Measure.pi_map_piCongrLeft e μ]

end Reindex

section OptionSplit

variable {ι : Type*} [Fintype ι] (E : Option ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

/-- Split off `none`, with the remaining coordinates as a Hilbert product.
Source: local encoding using Mathlib's `LinearEquiv.piOptionEquivProd` and the L² squared-norm
identities. Its `none`-then-tail order differs from Mathlib's measurable Option equivalence;
this ordering choice is not a construction specified in the tensorization reference. -/
def piOptionEquivProd : PiLp 2 E ≃ₗᵢ[ℝ]
    WithLp 2 (E none × PiLp 2 (fun i ↦ E (some i))) where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ _).trans
    ((LinearEquiv.piOptionEquivProd ℝ).trans
      (((LinearEquiv.refl ℝ (E none)).prodCongr (WithLp.linearEquiv 2 ℝ _).symm).trans
        (WithLp.linearEquiv 2 ℝ _).symm))
  norm_map' := by
    intro x
    show ‖(WithLp.toLp 2 ((WithLp.ofLp x) none,
        (WithLp.toLp 2 fun i ↦ (WithLp.ofLp x) (some i) : PiLp 2 fun i ↦ E (some i))) :
        WithLp 2 (E none × PiLp 2 fun i ↦ E (some i)))‖ = ‖x‖
    have hsq : ‖(WithLp.toLp 2 ((WithLp.ofLp x) none,
        (WithLp.toLp 2 fun i ↦ (WithLp.ofLp x) (some i) : PiLp 2 fun i ↦ E (some i))) :
        WithLp 2 (E none × PiLp 2 fun i ↦ E (some i)))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
        Fintype.sum_option fun o ↦ ‖x o‖ ^ 2]
      rfl
    have hn := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hn

/-- Source: local application rule obtained directly from the `piOptionEquivProd` definition. -/
theorem piOptionEquivProd_apply (x : PiLp 2 E) :
    piOptionEquivProd E x = WithLp.toLp 2 (x none, WithLp.toLp 2 (fun i ↦ x (some i))) :=
  rfl

variable [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

omit [∀ (i : Option ι), CompleteSpace (E i)] in
/-- Compatibility with the binary `prodMeasure`, including an empty tail.
Source: local helper using Mathlib's `Measure.pi_map_piOptionEquivProd`, `Measure.prod_swap`,
and pushforward composition to obtain the chosen `none`-then-tail order. -/
theorem map_piMeasure_piOptionEquivProd (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (piMeasure μ).map (piOptionEquivProd E) =
      prodMeasure (μ none) (piMeasure (fun i ↦ μ (some i))) := by
  have hmE := (MeasurableEquiv.piOptionEquivProd E).measurable
  have hswap : Measurable (Prod.swap :
      ((∀ i, E (some i)) × E none) → (E none × ∀ i, E (some i))) := measurable_swap
  have hpm : Measurable (Prod.map (id : E none → E none)
      (WithLp.toLp 2 : (∀ i, E (some i)) → PiLp 2 fun i ↦ E (some i))) :=
    measurable_id.prodMap (WithLp.measurable_toLp 2 (∀ i, E (some i)))
  have htoLp : Measurable (WithLp.toLp 2 :
      (E none × PiLp 2 fun i ↦ E (some i)) → WithLp 2 (E none × PiLp 2 fun i ↦ E (some i))) :=
    WithLp.measurable_toLp 2 _
  -- The plain-measure Option split first has Mathlib's (tail, none) order.
  have h0 : (Measure.pi μ).map (MeasurableEquiv.piOptionEquivProd E)
      = (Measure.pi fun i ↦ μ (some i)).prod (μ none) := by
    rw [← Measure.pi_map_piOptionEquivProd μ,
      Measure.map_map hmE (MeasurableEquiv.piOptionEquivProd E).symm.measurable]
    have hid : (⇑(MeasurableEquiv.piOptionEquivProd E) ∘
        ⇑(MeasurableEquiv.piOptionEquivProd E).symm) = id :=
      funext fun y ↦ (MeasurableEquiv.piOptionEquivProd E).apply_symm_apply y
    rw [hid, Measure.map_id]
  -- assemble the right-hand side as one pushforward of `Measure.pi μ`
  rw [prodMeasure, piMeasure, piMeasure,
    show μ none = (μ none).map id from (Measure.map_id).symm,
    Measure.map_prod_map _ _ measurable_id (WithLp.measurable_toLp 2 (∀ i, E (some i))),
    show ((μ none).prod (Measure.pi fun i ↦ μ (some i)))
        = ((Measure.pi fun i ↦ μ (some i)).prod (μ none)).map Prod.swap
      from Measure.prod_swap.symm,
    ← h0,
    Measure.map_map hswap hmE, Measure.map_map hpm (hswap.comp hmE),
    Measure.map_map htoLp (hpm.comp (hswap.comp hmE)),
    Measure.map_map (piOptionEquivProd E).continuous.measurable
      (WithLp.measurable_toLp 2 (∀ i, E i))]
  rfl

end OptionSplit

end TensorPCA.KLSProofs.Poincare.SmoothTest
