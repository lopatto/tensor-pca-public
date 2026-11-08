-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/Product/Admissible.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Poincare.Product.Geometry
public import TensorPCA.KLSProofs.Probability.Variance.Product

/-!
# Almost-everywhere admissibility of Hilbert-product sections

The smooth L2 finite-energy test class restricts to admissible sections almost everywhere.
The squared component gradients are integrable and sum to the full product energy.

Source: local Fubini and gradient-energy helpers for the repository's `Admissible` class.
BGL Lemma 4.3.2, used in Proposition 4.3.1 on
[printed pp. 186–187](https://doi.org/10.1007/978-3-319-00227-9),
has a Dirichlet-domain hypothesis on every section. Here smoothness holds for every section,
whereas L² and finite-energy membership follow only almost everywhere. These are different
statements; no equality of their test domains is claimed for arbitrary Borel measures.
The following historical API references use the upstream source's Mathlib v4.33.0
revision. This port is checked with the toolchain and Mathlib revision pinned in
this repository:
[product integrals and a.e. sections](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Prod.lean),
[L² transport](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean),
and [integrability under equivalences](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TensorPCA.KLSProofs.Poincare.SmoothTest

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : WithLp 2 (E × F) → ℝ}

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- Source: local transport helper from Mathlib's `memLp_map_measure_iff` and
`MeasurableEquiv.toLp`, applied to `Admissible.memLp_two`. -/
theorem Admissible.memLp_uncurry (hf : Admissible (prodMeasure μ ν) f) :
    MemLp (fun p : E × F ↦ f (WithLp.toLp 2 p)) 2 (μ.prod ν) := by
  have h := hf.memLp_two
  rw [prodMeasure, ← MeasurableEquiv.coe_toLp] at h
  exact (memLp_map_measure_iff h.aestronglyMeasurable
    (MeasurableEquiv.toLp 2 (E × F)).measurable.aemeasurable).mp h

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem Admissible.integrable_gradient_norm_sq (hf : Admissible (prodMeasure μ ν) f) :
    Integrable (fun p : E × F ↦ ‖gradient f (WithLp.toLp 2 p)‖ ^ 2) (μ.prod ν) := by
  have h := hf.energy_integrable
  rw [prodMeasure, ← MeasurableEquiv.coe_toLp] at h
  exact (integrable_map_equiv (MeasurableEquiv.toLp 2 (E × F)) _).mp h

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem Admissible.continuous_gradient (hf : Admissible (prodMeasure μ ν) f) :
    Continuous (fun q : WithLp 2 (E × F) ↦ gradient f q) := by
  have hfd : Continuous (fderiv ℝ f) := hf.smooth'.continuous_fderiv (by simp)
  have heq : (fun q : WithLp 2 (E × F) ↦ gradient f q)
      = fun q ↦ (InnerProductSpace.toDual ℝ (WithLp 2 (E × F))).symm (fderiv ℝ f q) := by
    funext q
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  rw [heq]
  exact (InnerProductSpace.toDual ℝ (WithLp 2 (E × F))).symm.continuous.comp hfd

section ProductGradientIntegrability

omit [SecondCountableTopology E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
/-- Source: local finite-energy helper using Mathlib's `Integrable.mono'` and
`WithLp.prod_norm_sq_eq_of_L2` to dominate the left component by the full squared gradient. -/
theorem Admissible.integrable_gradient_fst (hf : Admissible (prodMeasure μ ν) f) :
    Integrable (fun p : E × F ↦ ‖(gradient f (WithLp.toLp 2 p)).fst‖ ^ 2) (μ.prod ν) := by
  have hcont : Continuous (fun p : E × F ↦ ‖(gradient f (WithLp.toLp 2 p)).fst‖ ^ 2) := by
    have htoLp : Continuous (fun p : E × F ↦ (WithLp.toLp 2 p : WithLp 2 (E × F))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous
    have hfst : Continuous (fun q : WithLp 2 (E × F) ↦ q.fst) :=
      continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous
    exact ((hfst.comp (hf.continuous_gradient.comp htoLp)).norm.pow 2)
  refine hf.integrable_gradient_norm_sq.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hsum := WithLp.prod_norm_sq_eq_of_L2 (gradient f (WithLp.toLp 2 p))
  have hsq := sq_nonneg ‖(gradient f (WithLp.toLp 2 p)).snd‖
  linarith

/-- Source: local finite-energy helper using Mathlib's `Integrable.mono'` and
`WithLp.prod_norm_sq_eq_of_L2` to dominate the right component by the full squared gradient. -/
theorem Admissible.integrable_gradient_snd (hf : Admissible (prodMeasure μ ν) f) :
    Integrable (fun p : E × F ↦ ‖(gradient f (WithLp.toLp 2 p)).snd‖ ^ 2) (μ.prod ν) := by
  have hcont : Continuous (fun p : E × F ↦ ‖(gradient f (WithLp.toLp 2 p)).snd‖ ^ 2) := by
    have htoLp : Continuous (fun p : E × F ↦ (WithLp.toLp 2 p : WithLp 2 (E × F))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous
    have hsnd : Continuous (fun q : WithLp 2 (E × F) ↦ q.snd) :=
      continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous
    exact ((hsnd.comp (hf.continuous_gradient.comp htoLp)).norm.pow 2)
  refine hf.integrable_gradient_norm_sq.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hsum := WithLp.prod_norm_sq_eq_of_L2 (gradient f (WithLp.toLp 2 p))
  have hsq := sq_nonneg ‖(gradient f (WithLp.toLp 2 p)).fst‖
  linarith

end ProductGradientIntegrability

/-- Source: local a.e. consequence of `ProductVariance.memLp_left_ae`,
`Integrable.prod_left_ae`, and the left-section calculus helpers. Only an a.e. claim is made;
BGL Lemma 4.3.2 instead assumes every section belongs to its Dirichlet domain. -/
theorem Admissible.section_left_ae (hf : Admissible (prodMeasure μ ν) f) :
    ∀ᵐ y ∂ν, Admissible μ (fun x ↦ f (WithLp.toLp 2 (x, y))) := by
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  filter_upwards [ProductVariance.memLp_left_ae hf.memLp_uncurry,
    hf.integrable_gradient_fst.prod_left_ae] with y hL2 hEn
  refine ⟨contDiff_section_left hf.smooth' y, hL2, ?_⟩
  refine hEn.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  show ‖(gradient f (WithLp.toLp 2 (x, y))).fst‖ ^ 2
      = ‖gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x‖ ^ 2
  rw [gradient_section_left (hdiff _)]

/-- Source: local a.e. consequence of `ProductVariance.memLp_right_ae`,
`Integrable.prod_right_ae`, and the right-section calculus helpers. Only an a.e. claim is made;
BGL Lemma 4.3.2 instead assumes every section belongs to its Dirichlet domain. -/
theorem Admissible.section_right_ae (hf : Admissible (prodMeasure μ ν) f) :
    ∀ᵐ x ∂μ, Admissible ν (fun y ↦ f (WithLp.toLp 2 (x, y))) := by
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  filter_upwards [ProductVariance.memLp_right_ae hf.memLp_uncurry,
    hf.integrable_gradient_snd.prod_right_ae] with x hL2 hEn
  refine ⟨contDiff_section_right hf.smooth' x, hL2, ?_⟩
  refine hEn.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  show ‖(gradient f (WithLp.toLp 2 (x, y))).snd‖ ^ 2
      = ‖gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y‖ ^ 2
  rw [gradient_section_right (hdiff _)]

omit [SecondCountableTopology E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- Source: local realization of the binary product-energy sum using
`Admissible.integrable_gradient_fst`, `Admissible.integrable_gradient_snd`, Mathlib's
`integral_map_equiv`, and `WithLp.prod_norm_sq_eq_of_L2`; both real integrals are integrable. -/
theorem energy_prod_eq (hf : Admissible (prodMeasure μ ν) f) :
    energy (prodMeasure μ ν) f =
      (∫ p : E × F, ‖(gradient f (WithLp.toLp 2 p)).fst‖ ^ 2 ∂μ.prod ν) +
      (∫ p : E × F, ‖(gradient f (WithLp.toLp 2 p)).snd‖ ^ 2 ∂μ.prod ν) := by
  have htrans : energy (prodMeasure μ ν) f
      = ∫ p : E × F, ‖gradient f (WithLp.toLp 2 p)‖ ^ 2 ∂μ.prod ν := by
    rw [energy, prodMeasure, ← MeasurableEquiv.coe_toLp, integral_map_equiv]
  rw [htrans, ← integral_add hf.integrable_gradient_fst hf.integrable_gradient_snd]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun p ↦ WithLp.prod_norm_sq_eq_of_L2 _)

end TensorPCA.KLSProofs.Poincare.SmoothTest
