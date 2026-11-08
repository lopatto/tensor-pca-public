-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GroundUpperProofs
public import TensorPCA.NonRSUpperProofs.SphericalParisiGroundRSUpper

/-! Exact finite expectation transport to the concrete ordered-tensor model
used by the physical one-step upper. The two fields have identical increment
metrics under their canonical Gaussian laws, including signed overlap.
No physical limit or ground-state formula is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSSphericalGroundUpperTransportProofs
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open NonRSUpperProofs
noncomputable section

theorem unitSphere_eq_source (N : ℕ) :
    Model.unitSphere N = PureTensorJetBounds.UnitSphere N := by
  ext x
  simp only [Model.unitSphere, mem_setOf_eq, PureTensorJetBounds.UnitSphere,
    Metric.mem_sphere, dist_zero_right]

theorem source_sliceFeature_inner {N k : ℕ} {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (x y : Model.Vector N) :
    inner ℝ
      (FiniteTensorMixtureMaximum.feature (fun p : Fin k => p.val + 1)
        (VariationalProofs.sliceCoefficient k m) x)
      (FiniteTensorMixtureMaximum.feature (fun p : Fin k => p.val + 1)
        (VariationalProofs.sliceCoefficient k m) y) =
      (N : ℝ) * Scalar.xiSlice k m (inner ℝ x y) := by
  rw [FiniteTensorMixtureMaximum.feature_inner _ _ (VariationalProofs.sliceCoefficient_nonneg k hm),
    VariationalProofs.xiSlice_eq_sum]

theorem sliceFeature_increment_eq_source {N k : ℕ} {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (x y : Model.Vector N) :
    ‖GroundState.sliceFeature k m x - GroundState.sliceFeature k m y‖ =
      ‖FiniteTensorMixtureMaximum.feature (fun p : Fin k => p.val + 1)
          (VariationalProofs.sliceCoefficient k m) x -
        FiniteTensorMixtureMaximum.feature (fun p : Fin k => p.val + 1)
          (VariationalProofs.sliceCoefficient k m) y‖ := by
  have hnorm (z : Model.Vector N) : ‖GroundState.sliceFeature k m z‖ ^ 2 =
      ‖FiniteTensorMixtureMaximum.feature (fun p : Fin k => p.val + 1)
        (VariationalProofs.sliceCoefficient k m) z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      GroundUpperProofs.sliceFeature_inner hm, source_sliceFeature_inner hm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_sub_sq_real, hnorm x, hnorm y,
    GroundUpperProofs.sliceFeature_inner hm, source_sliceFeature_inner hm]

/-- The source maximum is a genuine integrable random variable under its
literal finite ordered standard Gaussian coefficient law. -/
theorem source_actualMaximum_integrable {N : ℕ} (hN : 0 < N) (k : ℕ) (m : ℝ) :
    Integrable
      (SphericalParisiGroundRSUpper.actualMaximum (N := N) (fun p : Fin k => p.val + 1)
        (VariationalProofs.sliceCoefficient k m))
      (SYK.standardGaussianMeasureOnEuclidean
        (FiniteTensorMixtureMaximum.Coordinate N (fun p : Fin k => p.val + 1))) :=
  SphericalParisiGroundRSUpper.actualMaximum_integrable hN _ _

/-- Exact expected maximum, with the factor N and both Gaussian laws explicit.
The equality holds for every degree, and hence in particular for k>=3. -/
theorem expectedSliceGround_eq_actualMaximum {N : ℕ} (hN : 0 < N) (k : ℕ)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.expectedSliceGround N k m =
      (∫ g, SphericalParisiGroundRSUpper.actualMaximum (N := N)
        (fun p : Fin k => p.val + 1) (VariationalProofs.sliceCoefficient k m) g
        ∂SYK.standardGaussianMeasureOnEuclidean
          (FiniteTensorMixtureMaximum.Coordinate N (fun p : Fin k => p.val + 1))) / (N : ℝ) := by
  letI : Nonempty (PureTensorJetBounds.UnitSphere N) := by
    rw [← unitSphere_eq_source]
    exact (Geometry.unitSphere_nonempty hN).to_subtype
  letI : CompactSpace (PureTensorJetBounds.UnitSphere N) := by
    rw [← unitSphere_eq_source]
    exact isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  let a : PureTensorJetBounds.UnitSphere N → GroundState.Disorder N k :=
    fun x => GroundState.sliceFeature k m x.val
  let b : PureTensorJetBounds.UnitSphere N →
      EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate N (fun p : Fin k => p.val + 1)) :=
    fun x => FiniteTensorMixtureMaximum.feature (fun p : Fin k => p.val + 1)
      (VariationalProofs.sliceCoefficient k m) x.val
  have ha : Continuous a :=
    (GroundUpperProofs.continuous_sliceFeature N k m).comp continuous_subtype_val
  have hb : Continuous b :=
    (FiniteTensorMixtureMaximum.feature_continuous _ _).comp continuous_subtype_val
  have hinc (x y : PureTensorJetBounds.UnitSphere N) : ‖a x - a y‖ = ‖b x - b y‖ :=
    sliceFeature_increment_eq_source hm x.val y.val
  have H := le_antisymm
    (GaussianMaximumComparisonProofs.expected_supremum_comparison a b ha hb
      (fun x y => (hinc x y).le))
    (GaussianMaximumComparisonProofs.expected_supremum_comparison b a hb ha
      (fun x y => (hinc x y).ge))
  have hsup (g : GroundState.Disorder N k) :
      sSup ((fun x => inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) =
        ⨆ x : PureTensorJetBounds.UnitSphere N, inner ℝ (a x) g := by
    dsimp only [a]
    rw [← unitSphere_eq_source, iSup, Set.image_eq_range]
  unfold GroundState.expectedSliceGround
  simp_rw [hsup]
  rw [integral_div, GaussianConcentrationBridge.standardGaussianMeasure_bridge]
  change (∫ g, (⨆ x, inner ℝ (a x) g) ∂stdGaussian (GroundState.Disorder N k)) / (N : ℝ) =
    (∫ g, (⨆ x, inner ℝ (b x) g)
      ∂stdGaussian (EuclideanSpace ℝ
        (FiniteTensorMixtureMaximum.Coordinate N (fun p : Fin k => p.val + 1)))) / (N : ℝ)
  exact congrArg (fun z : ℝ => z / (N : ℝ)) H


end
end TensorPCA.NonRSSphericalGroundUpperTransportProofs
