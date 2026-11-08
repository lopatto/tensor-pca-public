-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Model
public import TensorPCA.Scalar
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Concrete contracts for the coupled trial bound and null free-energy rates.
These definitions specify intermediate proof contracts. Zero-volume windows have
extended-real free energy minus infinity. Positive-window log integrability is
stated separately; Mathlib's total real log is never used as the physical value
of an empty window. Trial parameters are ordered `(lam,m,Lambda,u)`. -/
@[expose] public section

namespace TensorPCA.Coupled
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
noncomputable section

/-- The absolute-overlap window in the manuscript's two-replica constraint. -/
def pairWindow (N : ℕ) (u eta : ℝ) : Set (Model.Vector N × Model.Vector N) :=
  {xy | |inner ℝ xy.1 xy.2| ∈ Ioo (u-eta) (u+eta)}

/-- Unweighted product-sphere mass of the actual overlap window. -/
def windowMass (N : ℕ) (u eta : ℝ) : ℝ≥0∞ :=
  ((Model.spherePrior N).prod (Model.spherePrior N)) (pairWindow N u eta)

/-- The actual constrained product-sphere partition function. -/
def pairPartition (N k : ℕ) (lam u eta : ℝ) (w : Model.Tensor N k) : ℝ :=
  ∫ xy, (pairWindow N u eta).indicator
    (fun xy ↦ Real.exp (-lam *
      (Model.hamiltonian w xy.1 + Model.hamiltonian w xy.2))) xy
    ∂(Model.spherePrior N).prod (Model.spherePrior N)

/-- Real expected free energy when the window has positive mass; this quantity
is used only after its explicit positivity/integrability obligation is proved. -/
def meanPairFreeEnergy (N k : ℕ) (lam u eta : ℝ) : ℝ :=
  ∫ w, Real.log (pairPartition N k lam u eta w) / N ∂Model.noiseLaw N k

/-- Extended-real expected constrained free energy, including empty windows. -/
def expectedCoupledFreeEnergy (N k : ℕ) (lam u eta : ℝ) : EReal :=
  if windowMass N u eta = 0 then ⊥ else (meanPairFreeEnergy N k lam u eta : EReal)

/-- Nonempty overlap windows have positive sphere-product mass in dimensions
at least two. Dimension one is deliberately covered by the EReal convention. -/
def PositiveWindowMass : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ u ∈ Icc (0 : ℝ) 1, ∀ eta : ℝ, 0 < eta →
    0 < windowMass N u eta

/-- The supporting regularity needed before interpreting the positive branch. -/
def PositiveWindowRegularity : Prop :=
  ∀ (N k : ℕ), 1 ≤ N → ∀ lam u eta : ℝ,
    0 ≤ lam → u ∈ Icc (0 : ℝ) 1 → 0 < eta → windowMass N u eta ≠ 0 →
    (∀ w : Model.Tensor N k, 0 < pairPartition N k lam u eta w) ∧
    Integrable (fun w ↦ Real.log (pairPartition N k lam u eta w) / N)
      (Model.noiseLaw N k)

/-- Explicit derivative of xi(t)=lam²t^k on the required k≥2 domain. -/
def xiPrime (k : ℕ) (lam u : ℝ) : ℝ :=
  (k : ℝ) * lam^2 * u^(k-1)

/-- theta(t)=t xi'(t)-xi(t), evaluated without hidden analytic assumptions. -/
def theta (k : ℕ) (lam u : ℝ) : ℝ :=
  ((k : ℝ)-1) * lam^2 * u^k

/-- The exact displayed scalar trial functional preceding Theorem 4.1. -/
def trial (k : ℕ) (lam m Lambda u : ℝ) : ℝ :=
  lam^2 + (1-m) * theta k lam u - Lambda*u +
    (1/m) * Real.log ((1 + xiPrime k lam u - Lambda) /
      (1 + (1-m) * xiPrime k lam u - Lambda)) -
    (1/2 : ℝ) * (Real.log (1 + xiPrime k lam u + Lambda) +
      Real.log (1 + xiPrime k lam u - Lambda))

/-- Parameter order: lam=p0, m=p1, Lambda=p2, u=p3. -/
def Admissible (k : ℕ) (barLam : ℝ) (p : Fin 4 → ℝ) : Prop :=
  p 0 ∈ Icc (0 : ℝ) barLam ∧ p 1 ∈ Icc (1 : ℝ) 2 ∧
    p 2 ∈ Icc (0 : ℝ) 1 ∧ p 3 ∈ Icc (0 : ℝ) 1 ∧
    0 < 1 + (1-p 1) * xiPrime k (p 0) (p 3) - p 2

/-- Theorem 4.1, including one error constant for every compact set of admissible
parameters. Singletons recover the individual-parameter assertion. -/
def CoupledTrialBound : Prop :=
  ∀ k : ℕ, 2 ≤ k → Even k → ∀ barLam : ℝ, 0 ≤ barLam →
    ∀ K : Set (Fin 4 → ℝ), IsCompact K →
      K ⊆ {p | Admissible k barLam p} →
      ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ N : ℕ, 1 ≤ N →
        ∀ eta : ℝ, 0 < eta →
          expectedCoupledFreeEnergy N k (p 0) (p 3) eta ≤
            ((trial k (p 0) (p 1) (p 2) (p 3) + C*eta +
              C * Real.log ((N : ℝ)+1) / N : ℝ) : EReal)

/-- Mean of the actual null spherical free energy. -/
def meanNullFE (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ w, Model.freeEnergy N k lam w ∂Model.noiseLaw N k

/-- Centered second moment of that free energy, with the actual Gaussian law. -/
def varNullFE (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ w, (Model.freeEnergy N k lam w - meanNullFE N k lam)^2 ∂Model.noiseLaw N k

/-- Theorem 2.3. Constants depend on k,lam,eps and are uniform for all N≥1. -/
def MeanFreeEnergyRate : Prop :=
  ∀ k : ℕ, 4 ≤ k → Even k → ∀ lam : ℝ,
    0 ≤ lam → lam < Scalar.lambdaC k → ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        |meanNullFE N k lam - lam^2/2| ≤ C * (N : ℝ)^(-(k : ℝ)/4+eps)

/-- Theorem 2.4, with its exact k/4+1-eps variance exponent. -/
def VarianceFreeEnergyRate : Prop :=
  ∀ k : ℕ, 4 ≤ k → Even k → ∀ lam : ℝ,
    0 ≤ lam → lam < Scalar.lambdaC k → ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        varNullFE N k lam ≤ C / (N : ℝ)^((k : ℝ)/4+1-eps)

/-- Theorem 2.2: the probability is under the actual Gaussian null noise. -/
def FluctuationFreeEnergyRate : Prop :=
  ∀ k : ℕ, 4 ≤ k → Even k → ∀ lam : ℝ,
    0 ≤ lam → lam < Scalar.lambdaC k → ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
        (Model.noiseLaw N k).real
          {w | |Model.freeEnergy N k lam w - lam^2/2| > x/N} ≤
          C / (x^2 * (N : ℝ)^(((k : ℝ)-4)/4-eps))

/-- Integrability/nonnegative-second-moment obligations underlying all three
rate contracts. They must be proved, not silently supplied by total integrals. -/
def NullFreeEnergyRegularity : Prop :=
  ∀ (N k : ℕ), 1 ≤ N → ∀ lam : ℝ, 0 ≤ lam →
    Integrable (Model.freeEnergy N k lam) (Model.noiseLaw N k) ∧
    Integrable (fun w ↦ (Model.freeEnergy N k lam w)^2) (Model.noiseLaw N k)

end
end TensorPCA.Coupled
