-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Model
public import TensorPCA.Scalar
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Order.LiminfLimsup

/-! Statistical and variational statements for the maintainer's local revision.
Experiments use dimensions n+1; constrained limits use dimensions n+2. The
structures specify the experiment's random variables and laws. Proofs of these
statements are exported in Paper. Independent expected types are in
StatementChecks, outside Solution's import closure. Numbered references below
identify the local revision and its public arXiv v2 counterpart. -/
@[expose] public section

namespace TensorPCA.Statements
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology RealInnerProductSpace
universe u v

/-- Arbitrarily coupled positive-dimensional experiments on one probability space.
The law equality includes the signal/noise independence within each dimension. -/
structure PhysicalSequence (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) where
  sample : (n : ℕ) → Ω → Model.Vector (n+1) × Model.Tensor (n+1) k
  measurable : ∀ n, Measurable (sample n)
  law : ∀ n, μ.map (sample n) = Model.experimentLaw (n+1) k

/-- Independent estimator randomness within each dimension; no across-dimension
independence or simultaneous-in-strength almost-sure assertion is imposed. -/
structure EstimatorCoupling {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : PhysicalSequence k Ω μ)
    (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)] (ν : ∀ n, Measure (A n)) where
  estimator : ∀ n, Model.Estimator (n+1) k (A n)
  unit : ∀ n, Model.IsUnitEstimator (estimator n)
  auxiliary : ∀ n, Ω → A n
  measurable : ∀ n, Measurable (auxiliary n)
  independentLaw : ∀ n, μ.map (fun ω ↦ (E.sample n ω, auxiliary n ω)) =
    (Model.experimentLaw (n+1) k).prod (ν n)

noncomputable def sampleMaximum {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : PhysicalSequence k Ω μ) (lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Model.normalizedMaximum (Model.observation lam (E.sample n ω))

noncomputable def sampleOverlap {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {E : PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    (R : EstimatorCoupling E A ν) (lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  |inner ℝ (R.estimator n (Model.observation lam (E.sample n ω))
    (R.auxiliary n ω)) (E.sample n ω).1|

/-- Likelihood-maximization convention, including fair sign for every
even-order antipodal pair. -/
def IsPaperMLE {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {E : PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    (R : EstimatorCoupling E A ν) (lam : ℝ) : Prop :=
  (∀ n, Model.IsMLE (n+1) k lam (R.estimator n) (ν n)) ∧
    (Even k → ∀ n, ∀ᵐ y ∂Model.observationLaw (n+1) k lam,
      (ν n).map (R.estimator n y) = (ν n).map (fun a ↦ -R.estimator n y a))

/-- Theorem 1.1 in both versions: no assertion at critical strength. -/
def Detection : Prop :=
  ∀ k : ℕ, 6 ≤ k → Even k → ∀ lam : ℝ, 0 ≤ lam →
    (lam < Scalar.lambdaC k → Tendsto (fun n ↦ Model.testingDistance (n+1) k lam)
      atTop (𝓝 0)) ∧
    (Scalar.lambdaC k < lam → Tendsto (fun n ↦ Model.testingDistance (n+1) k lam)
      atTop (𝓝 1))

/-- Theorem 1.2 in both versions, value: fixed strength, including critical strength. -/
def MLEValue : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : PhysicalSequence k Ω μ),
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ sampleMaximum E lam n ω)
        atTop (𝓝 (Scalar.mleValue k lam))

/-- Theorem 1.2 in both versions, overlap: all k≥3, zero strength retained, critical excluded. -/
def MLEOverlap : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : PhysicalSequence k Ω μ)
      (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
      (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
      (R : EstimatorCoupling E A ν), IsPaperMLE R lam →
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ sampleOverlap R lam n ω)
          atTop (𝓝 (Real.sqrt (Scalar.qStar k lam)))

/-- Local Proposition 5.9 (arXiv v2: Proposition 5.8): conditional-mean tensor loss. -/
def TensorMMSE : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
    Tendsto (fun n ↦ Model.tensorMMSE (n+1) k lam)
      atTop (𝓝 (1 - Scalar.qStar k lam ^ k))

/-- Local Corollary 5.10 (arXiv v2: Corollary 5.9), in the local formulation:
both absolute moments with arbitrary independent randomization. -/
def EstimatorOptimality : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
    ∀ (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
      (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
      (est : ∀ n, Model.Estimator (n+1) k (A n)),
      (∀ n, Model.IsUnitEstimator (est n)) →
      Filter.limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k)
        atTop ≤ (Real.sqrt (Scalar.qStar k lam)) ^ k ∧
      Filter.limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) 1)
        atTop ≤ Real.sqrt (Scalar.qStar k lam)

/-- The unnumbered expected-absolute-overlap attainment consequence of
Theorem 1.2 and local Corollary 5.10 (arXiv v2: Corollary 5.9), with the same
physical experiment hypotheses as the almost-sure MLE statement. -/
def MLEAttainment : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : PhysicalSequence k Ω μ)
      (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
      (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
      (R : EstimatorCoupling E A ν), IsPaperMLE R lam →
        Tendsto (fun n ↦ Model.expectedOverlapPower (n+1) k lam
          (R.estimator n) (ν n) 1) atTop (𝓝 (Real.sqrt (Scalar.qStar k lam)))

/-- A strict local maximum relative to the physical overlap domain. -/
def StrictLocalMaximumOn (f : ℝ → ℝ) (x : ℝ) : Prop :=
  x ∈ Icc (-1 : ℝ) 1 ∧ ∃ eps : ℝ, 0 < eps ∧
    ∀ y ∈ Icc (-1 : ℝ) 1, y ≠ x → |y-x| < eps → f y < f x

/-- Proposition 1.4 in both versions, with the local formulation: secondary
branch for λ>λs and zero globality through the closed subcritical range. -/
def Landscape : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (∀ lam : ℝ, Scalar.lambdaS k < lam →
      StrictLocalMaximumOn (Scalar.energy k lam) (Real.sqrt (Scalar.qS k lam)) ∧
      ((∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤
        Scalar.energy k lam (Real.sqrt (Scalar.qS k lam))) ↔ Scalar.lambdaC k ≤ lam)) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam ≤ Scalar.lambdaC k →
      ∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤ Scalar.energy k lam 0)

/-- Local Lemma 5.5 (arXiv v2: Lemma 5.4), Eq.(E-rs), pointwise in fixed
overlap and strength, including endpoints. -/
def ConstrainedLimit : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → ∀ m ∈ Icc (-1 : ℝ) 1,
    (Tendsto (fun n ↦ ∫ z, Model.constrainedMaximum lam z.1 z.2 m
      ∂Model.experimentLaw (n+2) k) atTop (𝓝 (Scalar.energy k lam m))) ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (E : PhysicalSequence k Ω μ),
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Model.constrainedMaximum lam
        (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m)
        atTop (𝓝 (Scalar.energy k lam m)))

/-- Local Lemma 5.6 and Remark 5.11 (arXiv v2: Lemma 5.5 and Remark 5.10):
the RS formula and equality of unrestricted/four-parameter variational infima. -/
def VariationalConclusions : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (∀ lam : ℝ, 0 ≤ lam → ∀ m ∈ Icc (-1 : ℝ) 1,
      Real.sqrt (1 - 1 / ((k : ℝ)-1)) ≤ |m| →
      Scalar.energy k lam m = Scalar.rsEnergy k lam m) ∧
    (∀ m : ℝ, |m| < 1 → Scalar.FourParameterReduction k m)

/-- The introductory finite-strength testing consequence. The family is nonempty;
the empty family has no testing obligation. Each fixed strength is supercritical. -/
def FiniteStrengthTesting : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ r : ℕ, ∀ strengths : Fin (r+1) → ℝ,
    Function.Injective strengths → (∀ i, Scalar.lambdaC k < strengths i) →
    ∃ tests : ∀ n : ℕ, Model.Tensor (n+1) k → Fin (r+1),
      (∀ n, Measurable (tests n)) ∧ ∀ i,
      Tendsto (fun n ↦ (Model.observationLaw (n+1) k (strengths i)).real
        {y | tests n y ≠ i}) atTop (𝓝 0)

/-- The unnumbered discontinuous-transition consequence of Theorem 1.2
in both versions, expressed using the positive branch. -/
def DiscontinuousTransition : Prop :=
  ∀ k : ℕ, 3 ≤ k → Scalar.lambdaS k < Scalar.lambdaC k ∧
    ((k : ℝ)-2)/((k : ℝ)-1) < Scalar.qS k (Scalar.lambdaC k) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < Scalar.lambdaC k → Scalar.qStar k lam = 0) ∧
    ¬ ContinuousAt (Scalar.qStar k) (Scalar.lambdaC k)

end TensorPCA.Statements
