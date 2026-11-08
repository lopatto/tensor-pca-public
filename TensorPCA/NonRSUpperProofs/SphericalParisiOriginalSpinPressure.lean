-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed Apache-2.0 port from immutable source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalParisiLabeledOriginalEndpoint.lean
Definitions, theorem statements and proof bodies are retained, with local
namespace/import prefixes and narrow checked prerequisites. See LICENSE.
Only the independent uniform label law and original spin pressure prefix is
retained here; downstream endpoint factorization imports this shared prefix. -/
module
public import TensorPCA.NonRSUpperProofs.FiniteTensorMixtureMaximum
public import TensorPCA.GaussianSpinInterpolationProofs
public import Mathlib.Probability.ProbabilityMassFunction.Integrals


@[expose] public section
open TensorPCA.RetainedCountProofs

/-! Actual physical original endpoint factorization into its spherical
spin partition and a genuinely independent scalar Gaussian REM label bank.
The label preparation is the literal uniform finite probability measure. -/

namespace TensorPCA.NonRSUpperProofs.SphericalParisiLabeledOriginalEndpoint
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The literal uniform finite law. The current Mathlib constructor is
`PMF.ofFintype`; every singleton still has probability exactly `1/k`. -/
def labelLaw (k : ℕ) [NeZero k] : Measure (Fin k) :=
  (PMF.ofFintype (fun _ : Fin k => (k : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne k) (ENNReal.natCast_ne_top k))).toMeasure
instance labelLaw_probability (k : ℕ) [NeZero k] : IsProbabilityMeasure (labelLaw k) := by
  unfold labelLaw
  infer_instance

theorem labelLaw_integral (k : ℕ) [NeZero k] (f : Fin k → ℝ) :
    (∫ i,f i ∂labelLaw k)=(∑ i : Fin k,f i)/(k : ℝ) := by
  rw [labelLaw,PMF.integral_eq_sum]
  simp only [PMF.ofFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

def spinLinear {N : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β : ℝ) (z : UnitSphere N) :
    EuclideanSpace ℝ (Coordinate N d) →L[ℝ] ℝ :=
  innerSL ℝ (β • FiniteTensorMixtureMaximum.feature d c z.val)

def originalSpinPressure {N : ℕ} (μ : Measure (UnitSphere N)) (d : σ → ℕ) (c : σ → ℝ) (β : ℝ) : ℝ :=
  ∫ g,logPartition μ (spinLinear d c β) g
    ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)

omit [DecidableEq σ] in
theorem spinLinear_continuous {N : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β : ℝ) :
    Continuous (spinLinear (N := N) d c β) := by
  classical
  exact (innerSL ℝ).continuous.comp
    (((FiniteTensorMixtureMaximum.feature_continuous d c).comp continuous_subtype_val).const_smul β)

omit [DecidableEq σ] in
theorem spinLinear_bounded {N : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : UnitSphere N,‖spinLinear d c β z‖ ≤ C := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (spinLinear_continuous (N := N) d c β).continuousOn
  exact ⟨max B 0,le_max_right _ _,fun z => (hB z (mem_univ z)).trans (le_max_left _ _)⟩

omit [DecidableEq σ] in
theorem originalSpinLogPartition_integrable {N : ℕ}
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ] (d : σ → ℕ) (c : σ → ℝ) (β : ℝ) :
    Integrable (logPartition μ (spinLinear d c β))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) := by
  obtain ⟨C,hC,hbound⟩ := spinLinear_bounded (N := N) d c β
  simpa only [one_smul] using logPartition_radial_gaussian_integrable μ _
    (spinLinear_continuous d c β).measurable hC (.of_forall hbound) (1 : ℝ)


end
end TensorPCA.NonRSUpperProofs.SphericalParisiLabeledOriginalEndpoint
