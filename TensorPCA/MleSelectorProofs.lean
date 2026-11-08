-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianMaximumProofs

/-! Explicit Borel selection through the measurable derivative of the compact
support value, followed by a finite coordinate lift of rank-one tensors. -/

@[expose] public section
namespace TensorPCA.MleSelectorProofs
open Set Filter MeasureTheory ProbabilityTheory GaussianMaximumProofs
open scoped Topology RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def supportGradient (K : Set E) (b : E → ℝ) (w : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (supportValue K b) w)

theorem supportGradient_measurable (K : Set E) (b : E → ℝ) :
    Measurable (supportGradient K b) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
    (measurable_fderiv ℝ (supportValue K b))

omit [MeasurableSpace E] [BorelSpace E] in
theorem supportGradient_eq_of_maximizer {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) {w x : E} (hx : x ∈ K)
    (hxmax : inner ℝ x w+b x = supportValue K b w)
    (hd : DifferentiableAt ℝ (supportValue K b) w) : supportGradient K b w = x := by
  have hderiv := derivative_eq_of_maximizer hK hne hb hx hxmax hd.hasFDerivAt
  apply ext_inner_right ℝ
  intro v
  rw [supportGradient, InnerProductSpace.toDual_symm_apply, hderiv, innerSL_apply_apply]

/-- A Borel selector with a specified fallback, taking values in the compact set
even at exceptional nondifferentiability points. -/
def compactSelector (K : Set E) (b : E → ℝ) (fallback : E) (w : E) : E :=
  by
    classical
    exact if supportGradient K b w ∈ K then supportGradient K b w else fallback

theorem compactSelector_measurable {K : Set E} (hK : IsCompact K)
    (b : E → ℝ) (fallback : E) : Measurable (compactSelector K b fallback) := by
  classical
  have hgrad := supportGradient_measurable K b
  exact hgrad.ite (hK.isClosed.measurableSet.preimage hgrad) measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
theorem compactSelector_mem {K : Set E} {b : E → ℝ} {fallback : E}
    (hf : fallback ∈ K) (w : E) : compactSelector K b fallback w ∈ K := by
  classical
  unfold compactSelector
  split_ifs with h
  · exact h
  · exact hf

theorem compactSelector_ae_maximizes {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) {fallback : E}
    {μ : Measure E} (hμ : μ ≪ (volume : Measure E)) :
    ∀ᵐ w ∂μ, inner ℝ (compactSelector K b fallback w) w+
      b (compactSelector K b fallback w) = supportValue K b w := by
  classical
  obtain ⟨M, hLip⟩ := supportValue_lipschitz hK hne hb
  have hd : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ (supportValue K b) w :=
    hLip.ae_differentiableAt
  filter_upwards [hμ.ae_le hd] with w hw
  obtain ⟨x, hx, hxmax, _⟩ := supportValue_attained hK hne hb w
  have hgrad := supportGradient_eq_of_maximizer hK hne hb hx hxmax hw
  have hsel : compactSelector K b fallback w = x := by
    simp only [compactSelector, hgrad, ite_eq_left hx]
  simpa only [hsel] using hxmax


def tensorImage (N k : ℕ) : Set (Model.Tensor N k) :=
  Model.feature k '' Model.unitSphere N

def unitFallback (N : ℕ) (hN : 0 < N) : Model.Vector N :=
  (EuclideanSpace.basisFun (Fin N) ℝ) ⟨0, hN⟩

theorem unitFallback_mem (N : ℕ) (hN : 0 < N) : unitFallback N hN ∈ Model.unitSphere N :=
  (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one _

def canonicalTensor (N k : ℕ) (hN : 0 < N) (w : Model.Tensor N k) : Model.Tensor N k :=
  compactSelector (tensorImage N k) (fun _ ↦ 0)
    (Model.feature k (unitFallback N hN)) w

theorem tensorImage_isCompact (N k : ℕ) : IsCompact (tensorImage N k) :=
  (Geometry.unitSphere_isCompact N).image (Model.continuous_feature N k)

theorem canonicalTensor_measurable (N k : ℕ) (hN : 0 < N) :
    Measurable (canonicalTensor N k hN) :=
  compactSelector_measurable (tensorImage_isCompact N k) _ _

theorem canonicalTensor_mem (N k : ℕ) (hN : 0 < N) (w : Model.Tensor N k) :
    canonicalTensor N k hN w ∈ tensorImage N k :=
  compactSelector_mem (mem_image_of_mem _ (unitFallback_mem N hN)) w

theorem canonicalTensor_ae_maximizes (N k : ℕ) (hN : 0 < N) (lam : ℝ) :
    ∀ᵐ w ∂Model.observationLaw N k lam, ∀ x ∈ Model.unitSphere N,
      Model.score w x ≤ inner ℝ (canonicalTensor N k hN w) w := by
  have hK := tensorImage_isCompact N k
  have hne : (tensorImage N k).Nonempty := (Geometry.unitSphere_nonempty hN).image _
  have hsel := compactSelector_ae_maximizes hK hne (continuousOn_const (c := (0 : ℝ)))
    (fallback := Model.feature k (unitFallback N hN))
    (observationLaw_absolutelyContinuous_volume N k lam)
  filter_upwards [hsel] with w hw
  intro x hx
  have hle := le_supportValue hK hne (continuousOn_const (c := (0 : ℝ))) w
    (mem_image_of_mem _ hx)
  simpa only [Model.score, canonicalTensor, add_zero] using hle.trans_eq hw.symm

end
end TensorPCA.MleSelectorProofs
