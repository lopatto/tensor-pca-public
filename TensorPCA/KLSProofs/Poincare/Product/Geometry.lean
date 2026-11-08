-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/Product/Geometry.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Poincare.SmoothTest.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Geometry and admissible sections of a Hilbert product

The product norm is the L2 norm on `WithLp 2 (E × F)`. Integrability of sections is asserted
almost everywhere, as required by Fubini.
The coordinate inclusions preserve smoothness, and their gradients are the corresponding
components of the full Hilbert-product gradient.

Source: local Hilbert-product encoding and calculus helpers. The sum of coordinate energies
corresponds to the product energy in BGL Proposition 4.3.1, proof on
[printed pp. 186–187](https://doi.org/10.1007/978-3-319-00227-9).
BGL does not state these `WithLp` interfaces or identify the present arbitrary-Borel smooth
test domain with its Dirichlet domain. The following historical API references use
the upstream source's Mathlib v4.33.0 revision. This port is checked with the toolchain
and Mathlib revision pinned in this repository:
[the Hilbert product](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/ProdL2.lean),
[the L² product norm and linear equivalence](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Normed/Lp/ProdLp.lean),
[the transported measurable structure](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean),
and [gradient calculus](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Gradient/Basic.lean).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace TensorPCA.KLSProofs.Poincare.SmoothTest

/-- The product law transported to the Hilbert product.
Source: local encoding of Mathlib's `Measure.prod` through `WithLp.toLp 2`. -/
def prodMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) : Measure (WithLp 2 (E × F)) :=
  (μ.prod ν).map (WithLp.toLp 2)

/-- Source: local helper from Mathlib's product probability instance,
`WithLp.measurable_toLp`, and `Measure.isProbabilityMeasure_map`. -/
instance prodMeasure_isProbabilityMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (prodMeasure μ ν) := by
  rw [prodMeasure]
  exact (Measure.isProbabilityMeasure_map_iff (WithLp.measurable_toLp 2 (E × F)).aemeasurable).2 inferInstance

section Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

section ProductSections

omit [CompleteSpace E] [CompleteSpace F]
/-- Every left section is `C∞`. Source: local helper from Mathlib's `ContDiff.comp`,
`WithLp.prodContinuousLinearEquiv`, and `contDiff_prodMk_left`; no section L² claim is made. -/
theorem contDiff_section_left {f : WithLp 2 (E × F) → ℝ}
    (hf : ContDiff ℝ ∞ f) (y : F) :
    ContDiff ℝ ∞ (fun x ↦ f (WithLp.toLp 2 (x, y))) :=
  hf.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.comp (contDiff_prodMk_left y))

/-- Every right section is `C∞`. Source: local helper from Mathlib's `ContDiff.comp`,
`WithLp.prodContinuousLinearEquiv`, and `contDiff_prodMk_right`; no section L² claim is made. -/
theorem contDiff_section_right {f : WithLp 2 (E × F) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : E) :
    ContDiff ℝ ∞ (fun y ↦ f (WithLp.toLp 2 (x, y))) :=
  hf.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.comp (contDiff_prodMk_right x))

end ProductSections

/-- Source: local chain-rule helper using Mathlib's `HasFDerivAt.comp`, `toDual_gradient`,
and `WithLp.prod_inner_apply` to identify the left partial gradient. -/
theorem gradient_section_left {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x =
      (gradient f (WithLp.toLp 2 (x, y))).fst := by
  set p : WithLp 2 (E × F) := WithLp.toLp 2 (x, y) with hp
  set incl : E →L[ℝ] WithLp 2 (E × F) :=
    (((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm :
        (E × F) →L[ℝ] WithLp 2 (E × F)).comp (ContinuousLinearMap.inl ℝ E F)) with hincl_def
  have hincl_apply : ∀ h : E, incl h = WithLp.toLp 2 (h, 0) := fun h ↦ rfl
  have hsec : HasFDerivAt (fun x : E ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F))) incl x := by
    have heq : (fun x : E ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F)))
        = fun x : E ↦ incl x + WithLp.toLp 2 ((0 : E), y) := by
      funext x'
      rw [hincl_apply, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [heq]
    exact incl.hasFDerivAt.add_const _
  have hcomp : HasFDerivAt (fun x : E ↦ f (WithLp.toLp 2 (x, y)))
      ((fderiv ℝ f p).comp incl) x := hf.hasFDerivAt.comp x hsec
  have hkey : (fderiv ℝ f p).comp incl
      = InnerProductSpace.toDual ℝ E ((gradient f p).fst) := by
    have hfd : fderiv ℝ f p
        = InnerProductSpace.toDual ℝ (WithLp 2 (E × F)) (gradient f p) := by
      rw [toDual_gradient]
    ext h
    rw [ContinuousLinearMap.comp_apply, hincl_apply, hfd, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply]
    simp
  have hgrad : HasGradientAt (fun x : E ↦ f (WithLp.toLp 2 (x, y)))
      ((gradient f p).fst) x := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hkey]
    exact hcomp
  exact hgrad.gradient

/-- Source: local chain-rule helper using Mathlib's `HasFDerivAt.comp`, `toDual_gradient`,
and `WithLp.prod_inner_apply` to identify the right partial gradient. -/
theorem gradient_section_right {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y =
      (gradient f (WithLp.toLp 2 (x, y))).snd := by
  set p : WithLp 2 (E × F) := WithLp.toLp 2 (x, y) with hp
  set incl : F →L[ℝ] WithLp 2 (E × F) :=
    (((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm :
        (E × F) →L[ℝ] WithLp 2 (E × F)).comp (ContinuousLinearMap.inr ℝ E F)) with hincl_def
  have hincl_apply : ∀ h : F, incl h = WithLp.toLp 2 (0, h) := fun h ↦ rfl
  have hsec : HasFDerivAt (fun y : F ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F))) incl y := by
    have heq : (fun y : F ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F)))
        = fun y : F ↦ incl y + WithLp.toLp 2 (x, (0 : F)) := by
      funext y'
      rw [hincl_apply, ← WithLp.toLp_add, Prod.mk_add_mk, zero_add, add_zero]
    rw [heq]
    exact incl.hasFDerivAt.add_const _
  have hcomp : HasFDerivAt (fun y : F ↦ f (WithLp.toLp 2 (x, y)))
      ((fderiv ℝ f p).comp incl) y := hf.hasFDerivAt.comp y hsec
  have hkey : (fderiv ℝ f p).comp incl
      = InnerProductSpace.toDual ℝ F ((gradient f p).snd) := by
    have hfd : fderiv ℝ f p
        = InnerProductSpace.toDual ℝ (WithLp 2 (E × F)) (gradient f p) := by
      rw [toDual_gradient]
    ext h
    rw [ContinuousLinearMap.comp_apply, hincl_apply, hfd, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply]
    simp
  have hgrad : HasGradientAt (fun y : F ↦ f (WithLp.toLp 2 (x, y)))
      ((gradient f p).snd) y := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hkey]
    exact hcomp
  exact hgrad.gradient

/-- The exact sum of squared partial gradients for the Hilbert product norm.
Source: local consequence of `gradient_section_left`, `gradient_section_right`, and Mathlib's
`WithLp.prod_norm_sq_eq_of_L2`, realizing the product-energy sum described above. -/
theorem norm_gradient_sq_prod {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    ‖gradient f (WithLp.toLp 2 (x, y))‖ ^ 2 =
      ‖gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x‖ ^ 2 +
      ‖gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y‖ ^ 2 := by
  rw [gradient_section_left hf, gradient_section_right hf]
  exact WithLp.prod_norm_sq_eq_of_L2 _

end Geometry

end TensorPCA.KLSProofs.Poincare.SmoothTest
