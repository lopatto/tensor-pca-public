-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed port from immutable Apache-2.0 source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalParisiLabeledOriginalEndpoint.lean
Only namespace/import paths are adapted to the checked local Gaussian
foundation. Definitions and proof arguments are retained. See LICENSE. -/
module
public import TensorPCA.NonRSUpperProofs.SphericalParisiOriginalSpinPressure

public import TensorPCA.NonRSUpperProofs.SphericalParisiLabeledUnheldComparison
public import TensorPCA.NonRSUpperProofs.SphericalParisiGaussianREM
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
open SphericalParisiLabeledCovariance SphericalParisiLabeledRealization
open SphericalParisiLabeledTrace SphericalParisiLabeledThreeBlock SphericalParisiLabeledUnheldComparison
open GaussianCompactFeatureComparison GaussianSpinInterpolation SphericalParisiGaussianREM
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/- The exact label-law/spin-pressure prefix is shared with the sphere-net
reference proof, imported below instead of redeclaring those definitions. -/

private theorem join_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u u' : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    inner ℝ (sumJoin (u,w)) (sumJoin (u',w'))=inner ℝ u u'+inner ℝ w w' := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

omit [DecidableEq σ] in
theorem actual_originalFeature_value_split {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (Δ : ℝ)
    (z : UnitSphere N × Fin k) (g : EuclideanSpace ℝ (Coordinate N d)) (y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (originalFeature d c Δ z) (sumJoin (g,y))=
      inner ℝ (FiniteTensorMixtureMaximum.feature d c z.1.val) g+
        Real.sqrt (N : ℝ)*Real.sqrt Δ*y z.2 := by
  rw [originalFeature,join_inner,real_inner_smul_left,EuclideanSpace.inner_single_left]
  simp only [conj_trivial,one_mul]

omit [DecidableEq σ] in
/-- Exact samplewise original spin/REM partition factorization. -/
theorem actual_original_partition_factorization {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [SFinite μ] (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 : ℝ) (g : EuclideanSpace ℝ (Coordinate N d)) (y : EuclideanSpace ℝ (Fin k)) :
    GaussianSpinInterpolation.moment (μ.prod (labelLaw k)) (fun _ => 1)
      (fun z : UnitSphere N × Fin k => innerSL ℝ
        (β • originalFeature d c (theta d c q1-theta d c q0) z)) (sumJoin (g,y))=
      GaussianSpinInterpolation.moment μ (fun _ => 1) (spinLinear d c β) g*
        ((∑ i : Fin k,Real.exp ((β*Real.sqrt (theta d c q1-theta d c q0))*Real.sqrt (N : ℝ)*y i))/(k : ℝ)) := by
  unfold GaussianSpinInterpolation.moment weight
  simp only [one_mul,innerSL_apply_apply,real_inner_smul_left,actual_originalFeature_value_split,
    mul_add,Real.exp_add,spinLinear]
  have he : (fun z : UnitSphere N × Fin k =>
      Real.exp (β*inner ℝ (FiniteTensorMixtureMaximum.feature d c z.1.val) g)*
        Real.exp (β*(Real.sqrt (N : ℝ)*Real.sqrt (theta d c q1-theta d c q0)*y z.2)))=
      fun z => Real.exp (β*inner ℝ (FiniteTensorMixtureMaximum.feature d c z.1.val) g)*
        Real.exp ((β*Real.sqrt (theta d c q1-theta d c q0))*Real.sqrt (N : ℝ)*y z.2) := by
    funext z
    congr 2
    ring
  rw [he,integral_prod_mul
    (fun z : UnitSphere N => Real.exp (β*inner ℝ (FiniteTensorMixtureMaximum.feature d c z.val) g))
    (fun i : Fin k => Real.exp ((β*Real.sqrt (theta d c q1-theta d c q0))*Real.sqrt (N : ℝ)*y i)),
    labelLaw_integral]

omit [DecidableEq σ] in
theorem actual_original_log_partition_factorization {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ] (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 : ℝ) (g : EuclideanSpace ℝ (Coordinate N d)) (y : EuclideanSpace ℝ (Fin k)) :
    logPartition (μ.prod (labelLaw k)) (fun z : UnitSphere N × Fin k =>
      innerSL ℝ (β • originalFeature d c (theta d c q1-theta d c q0) z)) (sumJoin (g,y))=
      logPartition μ (spinLinear d c β) g+
        remLogAverage N k (β*Real.sqrt (theta d c q1-theta d c q0)) y := by
  obtain ⟨C,_hC,hbound⟩ := spinLinear_bounded (N := N) d c β
  have hZ := moment_one_pos μ (spinLinear d c β) (spinLinear_continuous d c β).measurable
    (.of_forall hbound) g
  have hY : 0 < (∑ i : Fin k,Real.exp ((β*Real.sqrt (theta d c q1-theta d c q0))*Real.sqrt (N : ℝ)*y i))/(k : ℝ) := by
    have hk : 0 < k := NeZero.pos k
    exact div_pos ((Real.exp_pos _).trans_le (Finset.single_le_sum
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ (⟨0,hk⟩ : Fin k)))) (Nat.cast_pos.mpr hk)
  unfold logPartition
  rw [actual_original_partition_factorization,Real.log_mul hZ.ne' hY.ne']
  unfold remLogAverage
  congr 2
  ring

end
end TensorPCA.NonRSUpperProofs.SphericalParisiLabeledOriginalEndpoint
