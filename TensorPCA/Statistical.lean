/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TensorPCA.Model
public import TensorPCA.Scalar
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Ring

/-!
# Statistical intermediate quantities and reductions

The hypotheses of these lemmas are finite-dimensional analytic
identities/inequalities and limits of moments or derivatives of concrete
functions, supplied as explicit proof parameters. Unconditional detection
and MMSE limits are exported in Paper.
-/

@[expose] public section

namespace TensorPCA.Statistical

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable section

/-- The actual log likelihood ratio under the null observation. -/
def nullLogLikelihood (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) : ℝ :=
  Real.log (Model.likelihoodRatio N k lam w)

/-- Second moment of the actual null log likelihood; this is not a target
encoding or an abstract error sequence. -/
def nullLogSecondMoment (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ w, (nullLogLikelihood N k lam w) ^ 2 ∂Model.noiseLaw N k

/-- Expected normalized null log likelihood. -/
def nullNormalizedLogMean (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ w, nullLogLikelihood N k lam w / N ∂Model.noiseLaw N k

/-- Centered second moment of the normalized null log likelihood. -/
def nullNormalizedLogVariance (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ w, (nullLogLikelihood N k lam w / N - nullNormalizedLogMean N k lam) ^ 2
    ∂Model.noiseLaw N k

/-- Actual normalized planted log likelihood, parametrized by squared signal
strength `gamma`. The origin and negative values carry Mathlib's total sqrt
convention; derivative identities below are requested at positive strengths. -/
def sphericalBayesFreeEnergy (N k : ℕ) (gamma : ℝ) : ℝ :=
  (∫ z, Real.log (Model.likelihoodRatio N k (Real.sqrt gamma)
    (Model.observation (Real.sqrt gamma) z)) ∂Model.experimentLaw N k) / N

/-- The scalar variational limit appearing in the Gaussian-prior theorem after
normalization and transfer to the spherical prior. -/
def bayesianLimit (k : ℕ) (gamma : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sSup (Scalar.phi k (Real.sqrt gamma) '' Icc (0 : ℝ) 1)

/-- The finite likelihood-to-TV inequality obtained by layer cake, the
inequality `(1-exp t)_+ ≤ |t|`, and Cauchy–Schwarz. -/
def FiniteTVMomentBound (k : ℕ) (lam : ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ Model.testingDistance (n + 1) k lam ∧
    Model.testingDistance (n + 1) k lam ≤
      Real.sqrt (nullLogSecondMoment (n + 1) k lam)

/-- Quantitative null log-likelihood control, independent of the testing target. -/
def NullLogSecondMomentLimit (k : ℕ) (lam : ℝ) : Prop :=
  Tendsto (fun n : ℕ ↦ nullLogSecondMoment (n + 1) k lam) atTop (𝓝 0)

/-- A finite test-error bound in terms of the centered null variance.
The coefficient `C` and reciprocal remainder must be obtained from a likelihood threshold test; this proposition supplies neither their proof nor
the negative mean gap needed to prove it. -/
def FiniteTVVarianceBound (k : ℕ) (lam C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    1 - (C * nullNormalizedLogVariance (n + 1) k lam + 1 / ((n : ℝ) + 1)) ≤
      Model.testingDistance (n + 1) k lam ∧
    Model.testingDistance (n + 1) k lam ≤ 1

/-- Vanishing variance of the actual normalized null log likelihood. -/
def NullNormalizedLogVarianceLimit (k : ℕ) (lam : ℝ) : Prop :=
  Tendsto (fun n : ℕ ↦ nullNormalizedLogVariance (n + 1) k lam) atTop (𝓝 0)

/-- The finite-dimensional I-MMSE identity at `gamma=lam²` for the concrete
spherical Gaussian channel. Its intended theorem domain includes `0 < lam`.
It asserts differentiability of the actual Bayesian free energy. -/
def FiniteIMMSE (k : ℕ) (lam : ℝ) : Prop :=
  ∀ n : ℕ, HasDerivAt (sphericalBayesFreeEnergy (n + 1) k)
    ((1 / 2 : ℝ) * (1 - Model.tensorMMSE (n + 1) k lam)) (lam ^ 2)

/-- Convergence of derivatives of the actual spherical Bayesian free energies,
which must be proved from the asymptotic free-energy theorem and convexity. -/
def BayesianDerivativeLimit (k : ℕ) (lam : ℝ) : Prop :=
  Tendsto (fun n : ℕ ↦ deriv (sphericalBayesFreeEnergy (n + 1) k) (lam ^ 2))
    atTop (𝓝 ((1 / 2 : ℝ) * (Scalar.qStar k lam) ^ k))

/-- The actual posterior/validation-channel error envelope. This contains the
odd-order sign-recovery loss 2/(delta sqrt N), with no asymptotic estimator claim. -/
def validationEnvelope (N k : ℕ) (lam delta : ℝ) : ℝ :=
  Real.sqrt (1 - Model.tensorMMSE N k (Real.sqrt (lam^2+delta^2))) +
    2 / (delta * Real.sqrt N)

def validationRootEnvelope (N k : ℕ) (lam delta : ℝ) : ℝ :=
  (validationEnvelope N k lam delta) ^ ((k : ℝ)⁻¹)

/-- Limits of explicitly defined posterior-risk sequences. These inputs are
independent of the estimator; they follow from MMSE, scalar right continuity,
and positive-power continuity. They are not arbitrary estimator upper bounds. -/
def ValidationEnvelopeControl (k : ℕ) (lam : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ delta a b : ℝ, 0 < delta ∧
    Real.sqrt (lam^2+delta^2) ≠ Scalar.lambdaC k ∧
    Tendsto (fun n ↦ validationEnvelope (n+1) k lam delta) atTop (𝓝 a) ∧
    a ≤ (Real.sqrt (Scalar.qStar k lam))^k + eps ∧
    Tendsto (fun n ↦ validationRootEnvelope (n+1) k lam delta) atTop (𝓝 b) ∧
    b ≤ Real.sqrt (Scalar.qStar k lam) + eps

/-- Finite posterior Cauchy-Schwarz, Gaussian augmentation and odd sign
validation inequalities, plus the finite Holder consequence. -/
def FiniteEstimatorBounds (k : ℕ) (lam : ℝ) {A : ℕ → Type*}
    [∀ n, MeasurableSpace (A n)] (ν : ∀ n, Measure (A n))
    (est : ∀ n, Model.Estimator (n+1) k (A n)) : Prop :=
  ∀ delta : ℝ, 0 < delta → Real.sqrt (lam^2+delta^2) ≠ Scalar.lambdaC k →
    ∀ n : ℕ,
      Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k ≤
        validationEnvelope (n+1) k lam delta ∧
      Model.expectedOverlapPower (n+1) k lam (est n) (ν n) 1 ≤
        validationRootEnvelope (n+1) k lam delta

/-- Mean-square error of the actual maximum statistic relative to its scalar
limit; sufficient for a finite nearest-limit classifier via Chebyshev. -/
def maximumMeanSquare (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ y, (Model.normalizedMaximum y - Scalar.mleValue k lam)^2
    ∂Model.observationLaw N k lam

/-- Checked subcritical statistical glue: log-likelihood L2 control implies
vanishing testing distance. No detection conclusion is used as a premise. -/
theorem testingDistance_tendsto_zero_of_logSecondMoment {k : ℕ} {lam : ℝ}
    (hFinite : FiniteTVMomentBound k lam)
    (hMoment : NullLogSecondMomentLimit k lam) :
    Tendsto (fun n : ℕ ↦ Model.testingDistance (n + 1) k lam) atTop (𝓝 0) := by
  have hSqrt : Tendsto
      (fun n : ℕ ↦ Real.sqrt (nullLogSecondMoment (n + 1) k lam)) atTop (𝓝 0) := by
    simpa using hMoment.sqrt
  exact tendsto_const_nhds.squeeze hSqrt (fun n ↦ (hFinite n).1)
    (fun n ↦ (hFinite n).2)

/-- Checked supercritical test-error squeeze. A finite error inequality and
vanishing actual variance suffice; a testing-limit premise is not assumed. -/
theorem testingDistance_tendsto_one_of_logVariance {k : ℕ} {lam C : ℝ}
    (hFinite : FiniteTVVarianceBound k lam C)
    (hVariance : NullNormalizedLogVarianceLimit k lam) :
    Tendsto (fun n : ℕ ↦ Model.testingDistance (n + 1) k lam) atTop (𝓝 1) := by
  have hInv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hLower : Tendsto
      (fun n : ℕ ↦ 1 - (C * nullNormalizedLogVariance (n + 1) k lam +
        1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul hVariance).add hInv)
  exact hLower.squeeze' tendsto_const_nhds (hFinite.mono (fun _ h ↦ h.1))
    (hFinite.mono (fun _ h ↦ h.2))

/-- I-MMSE reduction. The explicit parameters concern a concrete finite
channel derivative identity and derivatives of its actual free energy, not the
claimed limit of the MMSE itself. -/
theorem tensorMMSE_tendsto_of_derivative_values {k : ℕ} {lam : ℝ}
    (hFinite : FiniteIMMSE k lam)
    (hDerivative : BayesianDerivativeLimit k lam) :
    Tendsto (fun n : ℕ ↦ Model.tensorMMSE (n + 1) k lam)
      atTop (𝓝 (1 - (Scalar.qStar k lam) ^ k)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hDerivative)
  have h' : Tendsto
      (fun n : ℕ ↦ 1 - 2 * deriv (sphericalBayesFreeEnergy (n + 1) k) (lam ^ 2))
      atTop (𝓝 (1 - (Scalar.qStar k lam) ^ k)) := by
    convert h using 1 <;> ring
  convert h' using 1
  funext n
  rw [(hFinite n).deriv]
  ring


end
end TensorPCA.Statistical
