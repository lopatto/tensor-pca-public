-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed count-foundation port from immutable source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalMorse.lean
Definitions, theorem types and proof bodies are retained. Only the local
namespace/import prefixes are changed to TensorPCA.RetainedCountProofs.
See the repository LICENSE. -/
module

public import TensorPCA.RetainedCountProofs.GaussianMorse
public import TensorPCA.RetainedCountProofs.SphericalIntrinsicKacRice

/-! Almost-sure Morse regularity of the mixed spherical field. -/

@[expose] public section

namespace TensorPCA.RetainedCountProofs.SphericalMorse

open MeasureTheory ProbabilityTheory Set Function Metric
open TensorPCA.RetainedCountProofs.SphericalModel TensorPCA.RetainedCountProofs.SphericalForm
open TensorPCA.RetainedCountProofs.SphericalGaussianJet TensorPCA.RetainedCountProofs.WholeFieldRegression
open TensorPCA.RetainedCountProofs.SphereChartVolume TensorPCA.RetainedCountProofs.SphericalChartKacRice
open TensorPCA.RetainedCountProofs.SphereHessian TensorPCA.RetainedCountProofs.SphericalKacRiceGluing
open TensorPCA.RetainedCountProofs.SphericalChartGeometry TensorPCA.RetainedCountProofs.GaussianLocalCoordinates
open TensorPCA.RetainedCountProofs.SphericalIntrinsicKacRice
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal critical set on the actual sphere of radius `sqrt (n+1)`. -/
def sphereCriticalSet {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (J : Disorder (n+1) P) :
    Set (Vector (n+1)) :=
  {x | ‖x‖ ^ 2 = (n+1 : ℕ) ∧ surfaceGradient (field c J) x = 0}

/-- Almost every original tensor disorder has only regular critical points
in the actual spherical chart. -/
theorem actual_chart_regular_ae (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < 2 →
        surfaceGradient (field c J) (manuscriptChart n u) = 0 →
        (actualChartHessian n c J u).det ≠ 0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have h := regular_zeros_ae (chartGamma n c) (ball 0 2) isOpen_ball
    (chartGamma_contDiffOn n c) (fun u hu => center_chartGamma_surjective n μ hQ (by simpa using hu))
  have hlaw := actual_flattened_gaussian (n+1) μ.maxDegree
  rw [← hlaw.map_eq] at h
  have hpull := ae_of_ae_map hlaw.aemeasurable h
  filter_upwards [hpull] with J hJ
  intro u hu hcrit
  apply hJ u (by simpa using hu)
  rw [chartGamma_zero_iff_derivative_zero n c hu, unpack_euclideanDisorder]
  exact (actual_field_chart_critical_iff c J hu).mpr hcrit

/-- All intrinsic critical Hessians of the actual field are nonsingular,
almost surely under the original full tensor disorder law. -/
theorem actual_sphere_morse_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      ∀ x ∈ sphereCriticalSet n c J, (intrinsicHessian (field c J) x).det ≠ 0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  filter_upwards [actual_chart_regular_ae n μ hQ,
    fixed_point_noncritical_ae n hn μ hQ (southPole n) (southPole_norm_sq n)] with J hJ hpole
  intro x hx hdeg
  have hxp : x ≠ southPole n := fun he => hpole (he ▸ hx.2)
  have hximage : x ∈ manuscriptChart n '' ball 0 2 := by
    rw [manuscriptChart_image_ball_except_pole]
    exact ⟨hx.1, hxp⟩
  obtain ⟨u, hu, rfl⟩ := hximage
  have hu' : ‖u‖ < 2 := by simpa using hu
  have hreg := hJ u hu' hx.2
  apply hreg
  rw [actualChartHessian_det c J hu' hx.2, hdeg, mul_zero]

end
end TensorPCA.RetainedCountProofs.SphericalMorse

