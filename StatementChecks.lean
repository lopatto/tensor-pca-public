-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Solution

/-! Independent explicit expected types for all advertised results.
This check module is separate from Solution's import closure.
-/
@[expose] public section
namespace TensorPCA.StatementChecks
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators RealInnerProductSpace
universe u v

-- Theorem 1.1 in both versions: even k>=6, nonnegative fixed signal, no critical assertion.
example :
    ∀ k : ℕ, 6 ≤ k → Even k → ∀ lam : ℝ, 0 ≤ lam →
      (lam < Scalar.lambdaC k → Tendsto
        (fun n ↦ Model.testingDistance (n+1) k lam) atTop (𝓝 0)) ∧
      (Scalar.lambdaC k < lam → Tendsto
        (fun n ↦ Model.testingDistance (n+1) k lam) atTop (𝓝 1)) := @Paper.detection

-- Theorem 1.2 in both versions, value: critical strength belongs to the pure-model branch.
example :
    ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Statements.PhysicalSequence k Ω μ),
      ∀ᵐ ω ∂μ, Tendsto
        (fun n ↦ Model.normalizedMaximum (Model.observation lam (E.sample n ω)))
        atTop (𝓝 (if lam ≤ Scalar.lambdaC k then Scalar.gs k else
          Real.sqrt (k : ℝ) * (1 + lam^2 * (Scalar.qStar k lam)^(k-1)) /
            Real.sqrt (1 + lam^2 * (k : ℝ) * (Scalar.qStar k lam)^(k-1)))) := @Paper.mleValue

-- Theorem 1.2 in both versions, overlap: zero included; a fixed parameter's a.s. event.
example :
    ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Statements.PhysicalSequence k Ω μ)
        (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
        (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
        (R : Statements.EstimatorCoupling E A ν), Statements.IsPaperMLE R lam →
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦
        |inner ℝ (R.estimator n (Model.observation lam (E.sample n ω))
          (R.auxiliary n ω)) (E.sample n ω).1|)
        atTop (𝓝 (Real.sqrt (Scalar.qStar k lam))) := @Paper.mleOverlap

-- Local Proposition 5.9 (arXiv v2: Proposition 5.8): posterior tensor loss, positive noncritical strength.
example :
    ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
      Tendsto (fun n ↦ ∫ z,
        ‖Model.feature k z.1 - Model.posteriorTensor (n+1) k lam z‖^2
          ∂Model.experimentLaw (n+1) k)
        atTop (𝓝 (1 - (Scalar.qStar k lam)^k)) := @Paper.tensorMMSE

-- Local Corollary 5.10 (arXiv v2: Corollary 5.9), in the local absolute-overlap formulation:
-- absolute kth power (including odd k) and absolute first moment.
example :
    ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
      ∀ (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
        (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
        (est : ∀ n, Model.Estimator (n+1) k (A n)),
      (∀ n, Model.IsUnitEstimator (est n)) →
      limsup (fun n ↦ ∫ z,
        |inner ℝ (est n (Model.observation lam z.1) z.2) z.1.1|^k
          ∂(Model.experimentLaw (n+1) k).prod (ν n)) atTop ≤
            (Real.sqrt (Scalar.qStar k lam))^k ∧
      limsup (fun n ↦ ∫ z,
        |inner ℝ (est n (Model.observation lam z.1) z.2) z.1.1|^1
          ∂(Model.experimentLaw (n+1) k).prod (ν n)) atTop ≤
            Real.sqrt (Scalar.qStar k lam) := @Paper.estimatorOptimality

-- Unnumbered expected-absolute-overlap attainment consequence of Theorem 1.2
-- and local Corollary 5.10 (arXiv v2: Corollary 5.9).
example :
    ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → lam ≠ Scalar.lambdaC k →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Statements.PhysicalSequence k Ω μ)
        (A : ℕ → Type v) [∀ n, MeasurableSpace (A n)]
        (ν : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (ν n)]
        (R : Statements.EstimatorCoupling E A ν), Statements.IsPaperMLE R lam →
      Tendsto (fun n ↦ ∫ z,
        |inner ℝ (R.estimator n (Model.observation lam z.1) z.2) z.1.1|^1
          ∂(Model.experimentLaw (n+1) k).prod (ν n)) atTop
            (𝓝 (Real.sqrt (Scalar.qStar k lam))) := @Paper.mleAttainment

-- Proposition 1.4 in both versions, with the local formulation: strict local maximum and globality;
-- zero is globally maximizing on the entire nonnegative subcritical range.
example :
    ∀ k : ℕ, 3 ≤ k →
      (∀ lam : ℝ, Scalar.lambdaS k < lam →
        ((Real.sqrt (Scalar.qS k lam)) ∈ Icc (-1 : ℝ) 1 ∧
          ∃ eps : ℝ, 0 < eps ∧ ∀ m ∈ Icc (-1 : ℝ) 1,
            m ≠ Real.sqrt (Scalar.qS k lam) →
            |m - Real.sqrt (Scalar.qS k lam)| < eps →
            Scalar.energy k lam m < Scalar.energy k lam (Real.sqrt (Scalar.qS k lam))) ∧
        ((∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤
          Scalar.energy k lam (Real.sqrt (Scalar.qS k lam))) ↔ Scalar.lambdaC k ≤ lam)) ∧
      (∀ lam : ℝ, 0 ≤ lam → lam ≤ Scalar.lambdaC k →
        ∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤ Scalar.energy k lam 0) := @Paper.landscape

-- Local Lemma 5.5 (arXiv v2: Lemma 5.4), Eq.(E-rs): expected and a.s. limits, with N>=2 slices.
example :
    ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 ≤ lam → ∀ m ∈ Icc (-1 : ℝ) 1,
      (Tendsto (fun n ↦ ∫ z, Model.constrainedMaximum lam z.1 z.2 m
        ∂Model.experimentLaw (n+2) k) atTop
          (𝓝 (lam*m^k + Scalar.variationalValue (Scalar.xiSlice k m) 0))) ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Statements.PhysicalSequence k Ω μ),
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Model.constrainedMaximum lam
          (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m) atTop
            (𝓝 (lam*m^k + Scalar.variationalValue (Scalar.xiSlice k m) 0))) := @Paper.constrainedLimit

-- Local Lemma 5.6 and Remark 5.11 (arXiv v2: Lemma 5.5 and Remark 5.10):
-- RS endpoints and equality of unrestricted/four-parameter infima.
example :
    ∀ k : ℕ, 3 ≤ k →
      (∀ lam : ℝ, 0 ≤ lam → ∀ m ∈ Icc (-1 : ℝ) 1,
        Real.sqrt (1 - 1 / ((k : ℝ)-1)) ≤ |m| →
        Scalar.energy k lam m = lam*m^k + Real.sqrt ((k : ℝ)*(1-m^2))) ∧
      (∀ m : ℝ, |m| < 1 → Scalar.variationalValue (Scalar.xiSlice k m) 0 =
        (1/2 : ℝ) * sInf {v : ℝ | ∃ delta a b q : ℝ,
          0 < delta ∧ 0 ≤ a ∧ 0 ≤ b ∧ q ∈ Icc (0 : ℝ) 1 ∧
          v = Scalar.parisiFunctional (Scalar.xiSlice k m) 0
            (fun t ↦ delta+a*(1-t)+b*(1-max t q))}) := by
  have h : Statements.VariationalConclusions := @Paper.variationalConclusions
  have hprofile (delta a b q : ℝ) : Scalar.fourParameterProfile delta a b q =
      (fun t ↦ delta+a*(1-t)+b*(1-max t q)) := by
    funext t
    rfl
  simpa only [Statements.VariationalConclusions, Scalar.rsEnergy, Scalar.FourParameterReduction,
    Scalar.fourParameterValue, Scalar.FourParameterAdmissible,
    hprofile, and_assoc] using h

-- Unnumbered introductory testing consequence: nonempty fixed finite distinct supercritical strengths.
example :
    ∀ k : ℕ, 3 ≤ k → ∀ r : ℕ, ∀ strengths : Fin (r+1) → ℝ,
      Function.Injective strengths → (∀ i, Scalar.lambdaC k < strengths i) →
      ∃ tests : ∀ n : ℕ, Model.Tensor (n+1) k → Fin (r+1),
        (∀ n, Measurable (tests n)) ∧ ∀ i,
          Tendsto (fun n ↦ (Model.observationLaw (n+1) k (strengths i)).real
            {y | tests n y ≠ i}) atTop (𝓝 0) := @Paper.finiteStrengthTesting

-- Unnumbered consequence after Theorem 1.2 in both versions: a positive branch jump,
-- without asserting convergence of estimator overlap at critical strength.
example :
    ∀ k : ℕ, 3 ≤ k → Scalar.lambdaS k < Scalar.lambdaC k ∧
      ((k : ℝ)-2)/((k : ℝ)-1) < Scalar.qS k (Scalar.lambdaC k) ∧
      (∀ lam : ℝ, 0 ≤ lam → lam < Scalar.lambdaC k → Scalar.qStar k lam = 0) ∧
      ¬ ContinuousAt (Scalar.qStar k) (Scalar.lambdaC k) := @Paper.discontinuousTransition

-- Infimum-equality formulation of local Remark 5.11 (arXiv v2: Remark 5.10),
-- with the full admissible profile and parameter conditions.
example (k : ℕ) (hk : 3 ≤ k) (m : ℝ) (hm : |m| < 1) :
    Scalar.variationalValue (Scalar.xiSlice k m) 0 =
      (1/2 : ℝ) * sInf {v : ℝ | ∃ delta a b q : ℝ,
        0 < delta ∧ 0 ≤ a ∧ 0 ≤ b ∧ q ∈ Icc (0 : ℝ) 1 ∧
        v = Scalar.parisiFunctional (Scalar.xiSlice k m) 0
          (fun t => delta+a*(1-t)+b*(1-max t q))} := by
  have hprofile (delta a b q : ℝ) : Scalar.fourParameterProfile delta a b q =
      (fun t => delta+a*(1-t)+b*(1-max t q)) := by
    funext t
    rfl
  simpa only [Scalar.FourParameterReduction, Scalar.fourParameterValue,
    Scalar.FourParameterAdmissible, hprofile, and_assoc] using
      Paper.fourParameterReduction k hk m hm

end TensorPCA.StatementChecks
