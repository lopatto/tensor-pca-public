-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealVarianceProofs
public import TensorPCA.GuerraPinningProofs

/-! Jensen applied to the Gaussian output, latent sample, Bernoulli mask
and uniform reveal parameter. Only thermal replica variance enters the bound. -/
@[expose] public section
namespace TensorPCA.GaussianRevealVarianceAverageProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FiniteRevealProofs FiniteRevealAveragingProofs PosteriorPairProofs
open GaussianRevealVarianceProofs BayesianPinningVarianceProofs GuerraPinningProofs
open scoped Classical
noncomputable section
attribute [local instance] posterior_probability
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S D : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N : ℕ}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

theorem posterior_output_sqrt_variance_le (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (B : (Fin N → S) → D) (hB : Measurable B) (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) :
    (∫ y, Real.sqrt (replicaVariance (posteriorKernel q B y) a) ∂mixtureLaw q B) ≤
      Real.sqrt (∫ y, replicaVariance (posteriorKernel q B y) a ∂mixtureLaw q B) := by
  have : IsMarkovKernel (posteriorKernel q B) := posteriorKernel_isMarkov q B hB
  have : IsProbabilityMeasure (mixtureLaw q B) := mixtureLaw_probability q B hB
  have hm := (measurable_replicaVariance (posteriorKernel q B) a).sqrt
  have hs : MemLp (fun y ↦ Real.sqrt (replicaVariance (posteriorKernel q B y) a)) 2
      (mixtureLaw q B) := by
    apply MemLp.of_bound hm.aestronglyMeasurable (Real.sqrt (4*K^4))
    exact .of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (replicaVariance_bounds (posteriorKernel q B y) a hN hK ha).2
  exact integral_sqrt_le_sqrt_integral _
    (.of_forall fun y ↦ (replicaVariance_bounds (posteriorKernel q B y) a hN hK ha).1) hs

/-- The physical average of the square root of the actual posterior thermal
variance is bounded by the square root of the genuine pinning bound. -/
theorem actual_gaussian_pinning_sqrt_variance_bound (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (B : (Fin N → S) → D) (hB : Measurable B) (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ y,
      Real.sqrt (replicaVariance (posteriorKernel (posterior q mask x) B y) a)
      ∂mixtureLaw (posterior q mask x) B ∂q) ≤
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta))) := by
  let f : Finset (Fin N) → (Fin N → S) → ℝ := fun mask x ↦
    ∫ y, replicaVariance (posteriorKernel (posterior q mask x) B y) a ∂mixtureLaw (posterior q mask x) B
  have hf (mask : Finset (Fin N)) (x : Fin N → S) : 0 ≤ f mask x := by
    apply integral_nonneg
    intro y
    exact integral_nonneg (fun z ↦ sq_nonneg _)
  have hJ := uniform_reveal_mono q
    (fun mask x ↦ ∫ y, Real.sqrt (replicaVariance (posteriorKernel (posterior q mask x) B y) a)
      ∂mixtureLaw (posterior q mask x) B)
    (fun mask x ↦ Real.sqrt (f mask x))
    (fun mask x ↦ posterior_output_sqrt_variance_le (posterior q mask x) B hB a hN hK ha) hd0 hd1
  have hS := uniform_reveal_sqrt_le q f hf hd0 hd1
  have hV := Real.sqrt_le_sqrt (actual_gaussian_pinning_variance_bound q B hB a hN hK ha hd0 hd1)
  exact hJ.trans (hS.trans hV)

end
end TensorPCA.GaussianRevealVarianceAverageProofs
