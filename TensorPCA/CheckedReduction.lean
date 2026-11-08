-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.Reduction
public import TensorPCA.Coupled

/-! Parameterized assembly from intermediate mathematical claims.
The proof parameters are explicit; derived conclusions may be reused through
bounded convergence. Unconditional principal theorems are exported in Paper. -/
@[expose] public section
namespace TensorPCA.CheckedReduction
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal RealInnerProductSpace
universe u v

/-- Deterministic expected maximum convergence, strictly weaker than the
almost-sure principal result and obtained by the paper's mean sandwich. -/
def MeanMaximumLimit : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
    Tendsto (fun n ↦ Model.expectedMaximum (n+1) k lam) atTop (𝓝 (Scalar.mleValue k lam))

/-- Summable Gaussian centered deviations; no sample maximum limit is assumed. -/
def CenteredMaximumTails : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Statements.PhysicalSequence k Ω μ), ∀ eps : ℝ, 0 < eps →
      (∑' n : ℕ, μ {ω | eps ≤ |Statements.sampleMaximum E lam n ω -
        Model.expectedMaximum (n+1) k lam|}) ≠ ∞

theorem mleValue (hmean : MeanMaximumLimit) (htails : CenteredMaximumTails.{u}) :
    Statements.MLEValue.{u} := by
  intro k hk lam hlam Ω _ μ _ E
  apply Reduction.maximum_at E (hmean k hk lam hlam)
  have h := LimitTools.ae_tendsto_zero_of_summable_tails μ
    (fun n ω ↦ |Statements.sampleMaximum E lam n ω-Model.expectedMaximum (n+1) k lam|)
    (fun _ _ ↦ abs_nonneg _) (htails k hk lam hlam Ω μ E)
  exact h.mono (fun _ hω ↦ tendsto_zero_iff_norm_tendsto_zero.mpr hω)

/-- The finite envelope inequalities at countably many nearby parameters. -/
def MaximumEnvelopeSecants : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Statements.PhysicalSequence k Ω μ)
      (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
      (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
      (R : Statements.EstimatorCoupling E A ν), Statements.IsPaperMLE R lam →
      ∀ᵐ ω ∂μ, ∀ j : ℕ, ∀ᶠ n in atTop,
        (Statements.sampleMaximum E lam n ω-
          Statements.sampleMaximum E (lam-LimitTools.secantStep lam j) n ω) /
          LimitTools.secantStep lam j ≤ Reduction.overlapSlope R lam n ω ∧
        Reduction.overlapSlope R lam n ω ≤
          (Statements.sampleMaximum E (lam+LimitTools.secantStep lam j) n ω-
            Statements.sampleMaximum E lam n ω) / LimitTools.secantStep lam j

/-- The spherical fourth moment plus Markov supplies these zero-signal tails. -/
def ZeroMLEFourthMomentTails : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Statements.PhysicalSequence k Ω μ)
      (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
      (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
      (R : Statements.EstimatorCoupling E A ν), Statements.IsPaperMLE R 0 →
      ∀ eps : ℝ, 0 < eps → (∑' n : ℕ, μ {ω | eps ≤ Statements.sampleOverlap R 0 n ω}) ≠ ∞

/-- This composes the mean/concentration value proof with the secant proof;
the MLE value principal statement is not an additional assumed theorem. -/
theorem mleOverlap (hmean : MeanMaximumLimit) (htails : CenteredMaximumTails.{u})
    (hsec : MaximumEnvelopeSecants.{u,v}) (hzero : ZeroMLEFourthMomentTails.{u,v})
    (hselection : ∀ k : ℕ, 3 ≤ k → Scalar.SelectionLaws k)
    (hderiv : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
      Scalar.ValueDerivative k lam) : Statements.MLEOverlap.{u,v} := by
  have hv := mleValue hmean htails
  intro k hk lam hlam hne Ω _ μ _ E A _ ν _ R hMLE
  by_cases hz : lam = 0
  · subst lam
    apply Reduction.zero_overlap_at R (hzero k hk Ω μ E A ν R hMLE)
    rcases hselection k hk with ⟨hpos, hgap, _⟩
    simp only [Scalar.qStar, if_pos (le_trans hpos.le hgap.le)]
  · apply Reduction.positive_overlap_at (by omega : 0 < k) (lt_of_le_of_ne hlam (Ne.symm hz)) R
    · intro t ht
      exact hv k hk t ht.le Ω μ E
    · exact hsec k hk lam (lt_of_le_of_ne hlam (Ne.symm hz)) hne Ω μ E A ν R hMLE
    · exact hderiv k hk lam (lt_of_le_of_ne hlam (Ne.symm hz)) hne

/-- The actual Bayesian free-energy limit, before any derivative is taken. -/
def BayesianValueConvergence (k : ℕ) : Prop :=
  ∀ gamma : ℝ, 0 < gamma →
    Tendsto (fun n ↦ Statistical.sphericalBayesFreeEnergy (n+1) k gamma)
      atTop (𝓝 (Statistical.bayesianLimit k gamma))

/-- Convexity/differentiability of the concrete finite channel supplies these
secants. This is a finite derivative comparison, not a derivative limit. -/
def BayesianConvexSecants (k : ℕ) : Prop :=
  ∀ gamma : ℝ, 0 < gamma → ∀ j : ℕ, ∀ᶠ n in atTop,
    (Statistical.sphericalBayesFreeEnergy (n+1) k gamma-
      Statistical.sphericalBayesFreeEnergy (n+1) k (gamma-LimitTools.secantStep gamma j)) /
        LimitTools.secantStep gamma j ≤
        deriv (Statistical.sphericalBayesFreeEnergy (n+1) k) gamma ∧
    deriv (Statistical.sphericalBayesFreeEnergy (n+1) k) gamma ≤
      (Statistical.sphericalBayesFreeEnergy (n+1) k (gamma+LimitTools.secantStep gamma j)-
        Statistical.sphericalBayesFreeEnergy (n+1) k gamma) / LimitTools.secantStep gamma j

theorem tensorMMSE
    (hvalues : ∀ k : ℕ, 3 ≤ k → BayesianValueConvergence k)
    (hsec : ∀ k : ℕ, 3 ≤ k → BayesianConvexSecants k)
    (hchannel : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
      Statistical.FiniteIMMSE k lam)
    (hscalar : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
      HasDerivAt (Statistical.bayesianLimit k) ((1/2 : ℝ)*Scalar.qStar k lam^k) (lam^2)) :
    Statements.TensorMMSE := by
  apply Reduction.tensorMMSE hchannel
  intro k hk lam hlam hne
  exact Reduction.bayesian_derivative_at hlam (hvalues k hk)
    (hsec k hk (lam^2) (sq_pos_of_pos hlam)) (hscalar k hk lam hlam hne)

/-- Every finite posterior/odd-validation inequality is kept under the actual
estimator measurability and independent probability randomization hypotheses. -/
theorem estimatorOptimality
    (hfinite : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
      ∀ (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
        (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
        (est : ∀ n, Model.Estimator (n+1) k (A n)),
        (∀ n, Model.IsUnitEstimator (est n)) → Statistical.FiniteEstimatorBounds k lam ν est)
    (henvelopes : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
      Statistical.ValidationEnvelopeControl k lam) : Statements.EstimatorOptimality.{v} := by
  intro k hk lam hlam hne A _ ν _ est hunit
  exact Reduction.estimator_of_finite_bounds ν est
    (hfinite k hk lam hlam hne A ν est hunit) (henvelopes k hk lam hlam hne)

/-- Centered slice concentration is separate from the ground-state limit. -/
def CenteredSliceTails : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → ∀ m ∈ Icc (-1 : ℝ) 1,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Statements.PhysicalSequence k Ω μ), ∀ eps : ℝ, 0 < eps →
      (∑' n : ℕ, μ {ω | eps ≤ |Model.constrainedMaximum lam
        (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m -
        ∫ z, Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (n+2) k|}) ≠ ∞

theorem constrainedLimit
    (hground : ∀ k : ℕ, 3 ≤ k → ∀ m ∈ Icc (-1 : ℝ) 1, GroundState.SliceGroundLimit k m)
    (hslice : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → ∀ m ∈ Icc (-1 : ℝ) 1,
      GroundState.SliceDecomposition k lam m)
    (htails : CenteredSliceTails.{u}) : Statements.ConstrainedLimit.{u} := by
  intro k hk lam hlam m hm
  have hground' := hground k hk m hm
  have hslice' := hslice k hk lam hlam m hm
  refine ⟨Reduction.constrained_mean_at hground' hslice', ?_⟩
  intro Ω _ μ _ E
  apply (Reduction.constrained_at E hground' hslice' ?_).2
  have h := LimitTools.ae_tendsto_zero_of_summable_tails μ
    (fun n ω ↦ |Model.constrainedMaximum lam (E.sample (n+1) ω).1
      (E.sample (n+1) ω).2 m - ∫ z, Model.constrainedMaximum lam z.1 z.2 m
        ∂Model.experimentLaw (n+2) k|) (fun _ _ ↦ abs_nonneg _)
    (htails k hk lam hlam m hm Ω μ E)
  exact h.mono (fun _ hω ↦ tendsto_zero_iff_norm_tendsto_zero.mpr hω)

/-- Finite measurability, unit bound, and integral transport. This says nothing
about any limiting expected overlap. -/
def OverlapIntegralTransport : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : Statements.PhysicalSequence k Ω μ)
      (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
      (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
      (R : Statements.EstimatorCoupling E A ν),
      (∀ n, AEStronglyMeasurable (Statements.sampleOverlap R lam n) μ) ∧
      (∀ n, ∀ᵐ ω ∂μ, ‖Statements.sampleOverlap R lam n ω‖ ≤ 1) ∧
      (∀ n, Model.expectedOverlapPower (n+1) k lam (R.estimator n) (ν n) 1 =
        ∫ ω, Statements.sampleOverlap R lam n ω ∂μ)

/-- A consequence of the already derived overlap principal, by bounded
convergence. The previous principal is reused rather than re-assumed as an
external mathematical prerequisite in its own proof. -/
theorem mleAttainment (hoverlap : Statements.MLEOverlap.{u,v})
    (htransport : OverlapIntegralTransport.{u,v}) : Statements.MLEAttainment.{u,v} := by
  intro k hk lam hlam hne Ω _ μ _ E A _ ν _ R hMLE
  obtain ⟨hm, hb, ht⟩ := htransport k hk lam hlam Ω μ E A ν R
  exact Reduction.attainment_at R
    (hoverlap k hk lam hlam hne Ω μ E A ν R hMLE) hm hb ht

/-- The explicit one-dimensional derivative sign change; no local maximum
conclusion is included in this open calculus/RS-evaluation obligation. -/
def LocalEnergySigns (k : ℕ) (lam : ℝ) : Prop :=
  Real.sqrt (Scalar.qS k lam) ∈ Icc (-1 : ℝ) 1 ∧
  ∃ eps : ℝ, 0 < eps ∧
    ContinuousOn (Scalar.energy k lam)
      (Icc (Real.sqrt (Scalar.qS k lam)-eps) (Real.sqrt (Scalar.qS k lam)+eps)) ∧
    (∀ x ∈ Ioo (Real.sqrt (Scalar.qS k lam)-eps) (Real.sqrt (Scalar.qS k lam)),
      0 < deriv (Scalar.energy k lam) x) ∧
    (∀ x ∈ Ioo (Real.sqrt (Scalar.qS k lam)) (Real.sqrt (Scalar.qS k lam)+eps),
      deriv (Scalar.energy k lam) x < 0)

theorem landscape
    (hselection : ∀ k : ℕ, 3 ≤ k → Scalar.SelectionLaws k)
    (hupper : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
      ∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤ Scalar.mleValue k lam)
    (hpure : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
      Scalar.energy k lam 0 = Scalar.gs k)
    (hmatch : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, Scalar.lambdaS k < lam →
      Scalar.lambdaC k ≤ lam → Scalar.mleValue k lam =
        Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)))
    (hbelow : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, Scalar.lambdaS k < lam →
      lam < Scalar.lambdaC k → Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) < Scalar.gs k)
    (hsigns : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, Scalar.lambdaS k < lam →
      LocalEnergySigns k lam) : Statements.Landscape := by
  intro k hk
  constructor
  · intro lam hlam
    have hpos : 0 ≤ lam := ((hselection k hk).1.trans hlam).le
    obtain ⟨hx, hs⟩ := hsigns k hk lam hlam
    exact ⟨Reduction.landscape_local_at hx hs,
      Reduction.landscape_global_at (hupper k hk lam hpos) (hpure k hk lam hpos)
        (hmatch k hk lam hlam) (hbelow k hk lam hlam)⟩
  · intro lam hlam hle
    exact Reduction.zero_global_at hle (hupper k hk lam hlam) (hpure k hk lam hlam)

/-- A finite nearest-center construction, with a quantitative finite error
bound. Neither existence of asymptotically correct tests nor error convergence
is assumed; mean-square maximum convergence is supplied independently. -/
theorem finiteStrengthTesting
    (hclassifier : ∀ k : ℕ, 3 ≤ k → ∀ r : ℕ, ∀ strengths : Fin (r+1) → ℝ,
      Function.Injective strengths → (∀ i, Scalar.lambdaC k < strengths i) →
      ∃ (tests : ∀ n : ℕ, Model.Tensor (n+1) k → Fin (r+1)) (C : ℝ),
        (∀ n, Measurable (tests n)) ∧ ∀ i n,
        (Model.observationLaw (n+1) k (strengths i)).real {y | tests n y ≠ i} ≤
          C * Statistical.maximumMeanSquare (n+1) k (strengths i))
    (hmse : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, Scalar.lambdaC k < lam →
      Tendsto (fun n ↦ Statistical.maximumMeanSquare (n+1) k lam) atTop (𝓝 0)) :
    Statements.FiniteStrengthTesting := by
  intro k hk r strengths hinj hsuper
  obtain ⟨tests, C, hm, hb⟩ := hclassifier k hk r strengths hinj hsuper
  exact ⟨tests, Reduction.finite_testing_at strengths tests hm C hb
    (fun i ↦ hmse k hk (strengths i) (hsuper i))⟩

/-- The slice RS principal conclusion is derived from a general covariance
criterion and explicit polynomial facts, never assumed in equivalent form. -/
theorem variational (hrs : GroundState.GeneralRSVariationalLaw)
    (hpoly : GroundState.SlicePolynomialFacts)
    (hmin : ∀ k : ℕ, 3 ≤ k → ∀ m : ℝ, |m| < 1 → Scalar.FourParameterMinimizer k m)
    (hfamily : ∀ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q →
      Scalar.AdmissibleProfile (Scalar.fourParameterProfile delta a b q)) :
    Statements.VariationalConclusions :=
  Reduction.variational (GroundState.rsSlice_of_general hrs hpoly) hmin hfamily

end TensorPCA.CheckedReduction
