-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.Model
public import TensorPCA.Scalar

/-! The finite Gaussian mixture needed for sphere slices. The independent
random constant block is omitted here because its expected contribution is zero;
identification with the original slice is a separate finite-law obligation. -/
@[expose] public section
namespace TensorPCA.GroundState
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace

abbrev Coordinate (N k : ℕ) := (p : Fin k) × (Fin (p.val+1) → Fin N)
abbrev Disorder (N k : ℕ) := EuclideanSpace ℝ (Coordinate N k)
noncomputable def sliceFeature {N : ℕ} (k : ℕ) (m : ℝ) (x : Model.Vector N) : Disorder N k :=
  WithLp.toLp 2 (fun i ↦ Real.sqrt N * Real.sqrt (Nat.choose k (i.1.val+1)) *
    m ^ (k-(i.1.val+1)) * (Real.sqrt (1-m^2)) ^ (i.1.val+1) *
    ∏ j, x (i.2 j))
noncomputable def expectedSliceGround (N k : ℕ) (m : ℝ) : ℝ :=
  ∫ g, sSup ((fun x ↦ inner ℝ (sliceFeature k m x) g) '' Model.unitSphere N) / N
    ∂stdGaussian (Disorder N k)

/-- The required finite-mixture specialization of Theorem 5.1. It concerns an
independently defined Gaussian Hamiltonian, not a constrained planted maximum. -/
def SliceGroundLimit (k : ℕ) (m : ℝ) : Prop :=
  Filter.Tendsto (fun n ↦ expectedSliceGround (n+1) k m) Filter.atTop
    (nhds (Scalar.variationalValue (Scalar.xiSlice k m) 0))

/-- Finite Gaussian rotation/splitting and the N−1 versus N normalization,
expressed as a vanishing mean discrepancy. No ground-state value is assumed. -/
def SliceDecomposition (k : ℕ) (lam m : ℝ) : Prop :=
  Filter.Tendsto (fun n ↦
    (∫ z, Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (n+2) k) -
      (lam*m^k + expectedSliceGround (n+1) k m)) Filter.atTop (nhds 0)
/-- The genuine finite nonnegative covariance-polynomial class. Degree-one
terms are included; a random constant term has no ground-state mean effect. -/
def FiniteNonnegativeCovariance (xi : ℝ → ℝ) : Prop :=
  ∃ P : ℕ, ∃ c : Fin P → ℝ, (∀ p, 0 ≤ c p) ∧
    ∀ t : ℝ, xi t = ∑ p : Fin P, c p * t ^ (p.val+1)

/-- The general finite-mixture RS criterion from Chen–Sen Proposition 1,
including the separately required linear-field extension. It is not the slice
RS conclusion renamed as a premise. -/
def GeneralRSVariationalLaw : Prop :=
  ∀ (xi : ℝ → ℝ) (h : ℝ), FiniteNonnegativeCovariance xi → 0 ≤ h →
    deriv (deriv xi) 1 ≤ deriv xi 1+h^2 →
    Scalar.variationalValue xi h = Real.sqrt (deriv xi 1+h^2)

/-- Finite binomial expansion, derivative evaluation and the numerical RS
inequality for the explicit slice polynomial. No variational value occurs. -/
def SlicePolynomialFacts : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ m ∈ Icc (-1 : ℝ) 1,
    FiniteNonnegativeCovariance (Scalar.xiSlice k m) ∧
    deriv (Scalar.xiSlice k m) 1 = (k : ℝ)*(1-m^2) ∧
    (Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m| →
      deriv (deriv (Scalar.xiSlice k m)) 1 ≤ deriv (Scalar.xiSlice k m) 1)

theorem rsSlice_of_general (hrs : GeneralRSVariationalLaw)
    (hpoly : SlicePolynomialFacts) : ∀ k : ℕ, 3 ≤ k → Scalar.RSVariationalLaw k := by
  intro k hk m hm hlarge
  obtain ⟨hfinite, hderiv, hcrit⟩ := hpoly k hk m hm
  have hg := hrs (Scalar.xiSlice k m) 0 hfinite (le_refl 0)
    (by simpa using hcrit hlarge)
  simpa only [zero_pow (by decide : 2 ≠ 0), add_zero, hderiv] using hg

end TensorPCA.GroundState
