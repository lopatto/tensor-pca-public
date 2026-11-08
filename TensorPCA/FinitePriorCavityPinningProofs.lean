-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealVarianceProofs
public import TensorPCA.TensorCavitySubsetProofs

/-! Exact common-mask averaging of old coordinates and the last reveal bit.
The old-background thermal pinning bound uses this marginal law. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityPinningProofs
open MeasureTheory ProbabilityTheory Set TensorCavitySubsetProofs
open RevealPolynomialProofs FiniteRevealAveragingProofs GaussianRevealVarianceProofs
open GaussianPriorTransferProofs GaussianPosteriorProofs FiniteRevealProofs PosteriorPairProofs
open scoped Classical BigOperators
noncomputable section
attribute [local instance] posterior_probability
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Embedding
variable {iota kappa : Type*} [DecidableEq iota] [DecidableEq kappa]

theorem weight_image (I A : Finset iota) (f : iota → kappa) (hf : Function.Injective f) (theta : ℝ) :
    weight (I.image f) (A.image f) theta = weight I A theta := by
  unfold weight
  rw [Finset.prod_image (fun i _ j _ h ↦ hf h)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.mem_image, hf.eq_iff, exists_eq_right]

theorem average_image (I : Finset iota) (f : iota → kappa) (hf : Function.Injective f)
    (h : Finset kappa → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average (I.image f) h theta =
      RevealPolynomialProofs.average I (fun A ↦ h (A.image f)) theta := by
  unfold RevealPolynomialProofs.average
  rw [Finset.powerset_image, Finset.sum_image (fun A _ B _ h ↦ Finset.image_injective hf h)]
  apply Finset.sum_congr rfl
  intro A _
  rw [weight_image I A f hf theta]

end Embedding

theorem average_oldPart_last (N : ℕ) (f : Finset (Fin N) → Bool → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average Finset.univ
      (fun A : Finset (Fin (N+1)) ↦ f (oldPart A) (decide (Fin.last N ∈ A))) theta =
    (1-theta)*RevealPolynomialProofs.average Finset.univ (fun A ↦ f A false) theta+
      theta*RevealPolynomialProofs.average Finset.univ (fun A ↦ f A true) theta := by
  have hu : (Finset.univ : Finset (Fin (N+1))) =
      insert (Fin.last N) ((Finset.univ : Finset (Fin N)).image Fin.castSucc) := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp [Finset.mem_image]
  rw [hu, average_insert _ _ _ (last_not_mem_image_castSucc Finset.univ) theta,
    average_image _ Fin.castSucc (Fin.castSucc_injective N),
    average_image _ Fin.castSucc (Fin.castSucc_injective N)]
  simp only [oldPart_image, oldPart_insert_last, last_not_mem_image_castSucc,
    decide_false, Finset.mem_insert_self, decide_true]

theorem average_oldPart (N : ℕ) (f : Finset (Fin N) → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average Finset.univ
      (fun A : Finset (Fin (N+1)) ↦ f (oldPart A)) theta =
      RevealPolynomialProofs.average Finset.univ f theta := by
  have h := average_oldPart_last N (fun A _ ↦ f A) theta
  rw [h]
  ring

theorem uniformAverage_oldPart (N : ℕ) (f : Finset (Fin N) → ℝ) (delta : ℝ) :
    uniformAverage Finset.univ delta (fun A : Finset (Fin (N+1)) ↦ f (oldPart A)) =
      uniformAverage Finset.univ delta f := by
  unfold uniformAverage
  simp_rw [average_oldPart]

variable {S D : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N : ℕ}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

/-- A full N+1-coordinate Bernoulli mask has the correct N-coordinate pinning
marginal; the last reveal bit does not change the old-background variance bound. -/
theorem actual_common_mask_pinning_variance_bound (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (B : (Fin N → S) → D) (hB : Measurable B) (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    uniformAverage Finset.univ delta (fun mask : Finset (Fin (N+1)) ↦ ∫ x, ∫ y,
      replicaVariance (posteriorKernel (posterior q (oldPart mask) x) B y) a
      ∂mixtureLaw (posterior q (oldPart mask) x) B ∂q) ≤
      4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)) := by
  rw [uniformAverage_oldPart N (fun mask ↦ ∫ x, ∫ y,
    replicaVariance (posteriorKernel (posterior q mask x) B y) a
    ∂mixtureLaw (posterior q mask x) B ∂q) delta]
  exact actual_gaussian_pinning_variance_bound q B hB a hN hK ha hd0 hd1

end
end TensorPCA.FinitePriorCavityPinningProofs
