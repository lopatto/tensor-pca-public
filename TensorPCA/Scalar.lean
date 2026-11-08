-- Copyright (c) 2026 Patrick Lopatto. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Scalar definitions for the maintainer's local revision. All infima and
suprema below are the ordinary conditionally complete real infimum/supremum.
Their existence, boundedness, and identifying properties in the paper's domains
are explicit proof obligations; the definitions do not assume those properties.
Values outside the paper's stated domains carry no asserted interpretation. -/

namespace TensorPCA.Scalar

open Set MeasureTheory

noncomputable section

/-- Equation (f-lambda-def), used only on `[0,1)`. -/
def f (k : ℕ) (lam q : ℝ) : ℝ :=
  lam ^ 2 * q ^ k + Real.log (1 - q) + q

/-- Equation (def_phi), the compact scalar potential on `[0,1]`. -/
def phi (k : ℕ) (lam q : ℝ) : ℝ :=
  lam ^ 2 * (k : ℝ) * q ^ (k - 1) -
    Real.log (1 + lam ^ 2 * (k : ℝ) * q ^ (k - 1)) -
    lam ^ 2 * ((k : ℝ) - 1) * q ^ k

/-- Equation (lambda_c-def). Pointwise nonpositivity is the displayed
nonpositive-supremum condition on the nonempty interval `[0,1)`. -/
def lambdaC (k : ℕ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∀ q ∈ Ico (0 : ℝ) 1, f k lam q ≤ 0}

/-- Equation (lambda_s-def), for `k ≥ 3`. -/
def lambdaS (k : ℕ) : ℝ :=
  Real.sqrt ((((k : ℝ) - 1) ^ (k - 1)) /
    ((k : ℝ) * ((k : ℝ) - 2) ^ (k - 2)))

/-- The larger positive stationary branch, characterized by (q_SE).
For `k ≥ 3` and `lam > lambdaS k`, the scalar stationary-point results identify
its unique element and the corresponding strict local maximizer. -/
def StableStationaryPoint (k : ℕ) (lam q : ℝ) : Prop :=
  q ∈ Ioo (((k : ℝ) - 2) / ((k : ℝ) - 1)) 1 ∧
    (k : ℝ) * lam ^ 2 * q ^ (k - 2) * (1 - q) = 1

/-- `q_s` in the manuscript, defined as the supremum of stable stationary points.
Its characterization for `k ≥ 3` and `lambdaS k < lam` is proved in
`ScalarStationaryProofs.qS_spec`; the definition itself does not assume it. -/
def qS (k : ℕ) (lam : ℝ) : ℝ :=
  sSup {q : ℝ | StableStationaryPoint k lam q}

/-- A global maximizer of the scalar potential on its noncompact domain. -/
def IsScalarMaximizer (k : ℕ) (lam q : ℝ) : Prop :=
  q ∈ Ico (0 : ℝ) 1 ∧ ∀ r ∈ Ico (0 : ℝ) 1, f k lam r ≤ f k lam q

/-- Equation (q-star-def), including the convention `qStar k (lambdaC k)=0`.
The supercritical maximizer's existence and uniqueness are established by the
scalar selection results for `k ≥ 3`. -/
def qStar (k : ℕ) (lam : ℝ) : ℝ :=
  if lam ≤ lambdaC k then 0 else sSup {q : ℝ | IsScalarMaximizer k lam q}

/-- Equation (def_varphi), on strictly positive `z`. -/
def varphi (k : ℕ) (z : ℝ) : ℝ :=
  (1 + z) / z ^ 2 * Real.log (1 + z) - 1 / z - 1 / (k : ℝ)

/-- The positive zero `z_k`. Existence and uniqueness for `k ≥ 3` are established
by the scalar selection results; the `sInf` definition does not assume either. -/
def zK (k : ℕ) : ℝ :=
  sInf {z : ℝ | 0 < z ∧ varphi k z = 0}

/-- Equation (def_GS), the manuscript's pure-model ground-state constant. -/
def gs (k : ℕ) : ℝ :=
  Real.sqrt (k : ℝ) / Real.sqrt (1 + zK k) * (1 + zK k / (k : ℝ))

/-- The supercritical scalar expression in (lim_max_likelihood). -/
def supercriticalValue (k : ℕ) (lam : ℝ) : ℝ :=
  Real.sqrt (k : ℝ) * (1 + lam ^ 2 * (qStar k lam) ^ (k - 1)) /
    Real.sqrt (1 + lam ^ 2 * (k : ℝ) * (qStar k lam) ^ (k - 1))

/-- The full value in (lim_max_likelihood), retaining its critical endpoint. -/
def mleValue (k : ℕ) (lam : ℝ) : ℝ :=
  if lam ≤ lambdaC k then gs k else supercriticalValue k lam

/-- Equation (xi-m), including its constant subtraction and linear term. -/
def xiSlice (k : ℕ) (m t : ℝ) : ℝ :=
  (m ^ 2 + (1 - m ^ 2) * t) ^ k - m ^ (2 * k)

/-- The class `C` in the ground-state variational formula. We represent a
continuous function on `[0,1]` by a real function whose restriction has exactly
the stated properties; values outside `[0,1]` are unused by the functional. -/
def AdmissibleProfile (p : ℝ → ℝ) : Prop :=
  ContinuousOn p (Icc (0 : ℝ) 1) ∧
  AntitoneOn p (Icc (0 : ℝ) 1) ∧
  ConcaveOn ℝ (Icc (0 : ℝ) 1) p ∧
  ∀ t ∈ Icc (0 : ℝ) 1, 0 < p t

/-- The variational class is nonempty; a positive constant is admissible. -/
theorem admissibleProfile_const {c : ℝ} (hc : 0 < c) :
    AdmissibleProfile (fun _ : ℝ => c) := by
  refine ⟨continuousOn_const, ?_, concaveOn_const c (convex_Icc 0 1), ?_⟩
  · intro x hx y hy hxy
    exact le_rfl
  · intro t ht
    exact hc

/-- A positive constant witnesses nonemptiness of the profile class. -/
theorem admissibleProfiles_nonempty : {p : ℝ → ℝ | AdmissibleProfile p}.Nonempty :=
  ⟨fun _ => 1, admissibleProfile_const zero_lt_one⟩

/-- The functional `P_h`, including the boundary coefficient `xi'(0)`.
`xi` is a real covariance function (a polynomial in the slice applications). -/
def parisiFunctional (xi : ℝ → ℝ) (h : ℝ) (p : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, deriv (deriv xi) t * p t + 1 / p t) +
    (h ^ 2 + deriv xi 0) * p 0

/-- The ground-state variational value `G(xi,h)`, with the required factor 1/2.
No minimizer is selected; the degenerate zero-covariance case is therefore
allowed to have an unattained infimum, as in the manuscript. -/
def variationalValue (xi : ℝ → ℝ) (h : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sInf {v : ℝ | ∃ p : ℝ → ℝ,
    AdmissibleProfile p ∧ v = parisiFunctional xi h p}

/-- The variational expression in local Lemma 5.5 (arXiv v2: Lemma 5.4),
identified with the constrained-maximum limit by `Paper.constrainedLimit`. -/
def energy (k : ℕ) (lam m : ℝ) : ℝ :=
  lam * m ^ k + variationalValue (xiSlice k m) 0

/-- The replica-symmetric expression in local Lemma 5.6 (arXiv v2: Lemma 5.5),
on its stated overlap range. -/
def rsEnergy (k : ℕ) (lam m : ℝ) : ℝ :=
  lam * m ^ k + Real.sqrt ((k : ℝ) * (1 - m ^ 2))

/-- The profile in local Remark 5.11 (arXiv v2: Remark 5.10). -/
def fourParameterProfile (delta a b q t : ℝ) : ℝ :=
  delta + a * (1 - t) + b * (1 - max t q)

/-- The parameter range in local Remark 5.11 (arXiv v2: Remark 5.10). -/
def FourParameterAdmissible (delta a b q : ℝ) : Prop :=
  0 < delta ∧ 0 ≤ a ∧ 0 ≤ b ∧ q ∈ Icc (0 : ℝ) 1

/-- Restriction of the variational infimum to the four-parameter family.
Equality with `variationalValue` is a separate structural assertion, proved for
the slice covariances and parameters in `Paper.fourParameterReduction`; no
equality for arbitrary `xi` and `h` is assumed by this definition. -/
def fourParameterValue (xi : ℝ → ℝ) (h : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sInf {v : ℝ | ∃ delta a b q : ℝ,
    FourParameterAdmissible delta a b q ∧
      v = parisiFunctional xi h (fourParameterProfile delta a b q)}

/-- Critical selection/existence assertions from gauss_scalar and the positive
root argument, established for `3 ≤ k` by `ScalarSelectionProofs.selectionLaws`.
The proposition records the properties without assuming them in the scalar
definitions. -/
def SelectionLaws (k : ℕ) : Prop :=
  0 < lambdaS k ∧ lambdaS k < lambdaC k ∧
  BddAbove {lam : ℝ | 0 ≤ lam ∧ ∀ q ∈ Ico (0 : ℝ) 1, f k lam q ≤ 0} ∧
  (∀ lam : ℝ, lambdaS k < lam →
    StableStationaryPoint k lam (qS k lam) ∧
      ∀ q : ℝ, StableStationaryPoint k lam q → q = qS k lam) ∧
  (∀ lam : ℝ, lambdaC k < lam →
    IsScalarMaximizer k lam (qStar k lam) ∧ 0 < qStar k lam ∧
      qStar k lam = qS k lam ∧
      ∀ q : ℝ, IsScalarMaximizer k lam q → q = qStar k lam) ∧
  (0 < zK k ∧ varphi k (zK k) = 0 ∧
    ∀ z : ℝ, 0 < z → varphi k z = 0 → z = zK k) ∧
  (∀ lam : ℝ, 0 ≤ lam → qStar k lam ∈ Ico (0 : ℝ) 1)

/-- The critical matching identity from Lemma x_k. -/
def CriticalRootIdentity (k : ℕ) : Prop :=
  (lambdaC k) ^ 2 * (k : ℝ) * (qS k (lambdaC k)) ^ (k - 1) = zK k

/-- The integrated scalar identity used in the value sandwich. The integrand
is `(sqrt q)^k`, so odd tensor orders do not undergo natural-number division. -/
def ValueIdentity (k : ℕ) (lam : ℝ) : Prop :=
  mleValue k lam = gs k + ∫ t in (0 : ℝ)..lam, (Real.sqrt (qStar k t)) ^ k

/-- The derivative used in the overlap squeeze at a fixed positive parameter
away from the critical threshold. -/
def ValueDerivative (k : ℕ) (lam : ℝ) : Prop :=
  HasDerivAt (mleValue k) ((Real.sqrt (qStar k lam)) ^ k) lam

/-- The replica-symmetric evaluation used in local Lemma 5.6 (arXiv v2: Lemma 5.5). -/
def RSVariationalLaw (k : ℕ) : Prop :=
  ∀ m ∈ Icc (-1 : ℝ) 1,
    Real.sqrt (1 - 1 / ((k : ℝ) - 1)) ≤ |m| →
      variationalValue (xiSlice k m) 0 = Real.sqrt ((k : ℝ) * (1 - m ^ 2))

/-- The minimizer-attainment assertion discussed in local Remark 5.11
(arXiv v2: Remark 5.10). This predicate is separate from the exported equality
of infima and requires an admissible global minimizer. -/
def FourParameterMinimizer (k : ℕ) (m : ℝ) : Prop :=
  ∃ delta a b q : ℝ,
    FourParameterAdmissible delta a b q ∧
    AdmissibleProfile (fourParameterProfile delta a b q) ∧
    ∀ p : ℝ → ℝ, AdmissibleProfile p →
      parisiFunctional (xiSlice k m) 0 (fourParameterProfile delta a b q) ≤
        parisiFunctional (xiSlice k m) 0 p

/-- The infimum-equality formulation of local Remark 5.11 (arXiv v2: Remark 5.10),
asserted for `3 ≤ k` and `|m| < 1`. -/
def FourParameterReduction (k : ℕ) (m : ℝ) : Prop :=
  variationalValue (xiSlice k m) 0 = fourParameterValue (xiSlice k m) 0


end
end TensorPCA.Scalar
