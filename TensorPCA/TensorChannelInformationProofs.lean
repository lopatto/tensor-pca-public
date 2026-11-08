-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianChannelInformationProofs
public import TensorPCA.SphericalGaussianTransferProofs

/-!
# The tensor channel's normalized information identity

The Gaussian signal uses the G/sqrt(N) prior feature; the spherical
signal uses the angular prior. Both use strength sqrt(gamma)*sqrt(N).
Information below is the joint-versus-product KL divided by physical N.
-/
@[expose] public section

namespace TensorPCA.TensorChannelInformationProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
  GaussianChannelInformationProofs SphericalGaussianTransferProofs
open scoped ENNReal RealInnerProductSpace

noncomputable def gaussianSignal (N k : ℕ) (gamma : ℝ) : Model.Vector N → Model.Tensor N k :=
  (Real.sqrt gamma * Real.sqrt N) • gaussianFeature N k

noncomputable def sphericalSignal (N k : ℕ) (gamma : ℝ) : Model.Vector N → Model.Tensor N k :=
  (Real.sqrt gamma * Real.sqrt N) • Model.feature (N := N) k

noncomputable def gaussianPriorInformation (N k : ℕ) (gamma : ℝ) : ℝ :=
  channelInformation (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma) / N

noncomputable def sphericalPriorInformation (N k : ℕ) (gamma : ℝ) : ℝ :=
  channelInformation (Model.spherePrior N) (sphericalSignal N k gamma) / N

theorem measurable_gaussianSignal (N k : ℕ) (gamma : ℝ) : Measurable (gaussianSignal N k gamma) :=
  (measurable_gaussianFeature N k).const_smul _

theorem measurable_sphericalSignal (N k : ℕ) (gamma : ℝ) : Measurable (sphericalSignal N k gamma) :=
  (Model.continuous_feature N k).measurable.const_smul _

theorem gaussianSignal_memLp_two {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    MemLp (gaussianSignal N k gamma) 2 (stdGaussian (Model.Vector N)) :=
  (gaussianFeature_memLp_two hN).const_smul _

theorem sphericalSignal_memLp_two {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    MemLp (sphericalSignal N k gamma) 2 (Model.spherePrior N) := by
  have hfeature : MemLp (Model.feature (N := N) k) 2 (Model.spherePrior N) :=
    MemLp.of_bound (Model.continuous_feature N k).aestronglyMeasurable 1
      ((Geometry.spherePrior_norm_ae hN).mono fun x hx ↦ (Geometry.feature_unit_norm x hx).le)
  exact hfeature.const_smul _

theorem gaussianPriorInformation_finite {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    klDiv (jointLaw (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma))
      ((stdGaussian (Model.Vector N)).prod
        (mixtureLaw (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma))) ≠ ∞ :=
  channelInformation_finite _ _ (measurable_gaussianSignal N k gamma) (gaussianSignal_memLp_two hN gamma)

theorem sphericalPriorInformation_finite {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    klDiv (jointLaw (Model.spherePrior N) (sphericalSignal N k gamma))
      ((Model.spherePrior N).prod (mixtureLaw (Model.spherePrior N) (sphericalSignal N k gamma))) ≠ ∞ :=
  channelInformation_finite _ _ (measurable_sphericalSignal N k gamma) (sphericalSignal_memLp_two hN gamma)

theorem scaled_energy_div {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (mu : Measure Omega) (F : Omega → E) {N : ℕ} (hN : 0 < N)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    ((1 / 2 : ℝ) * (∫ x, ‖(Real.sqrt gamma * Real.sqrt N) • F x‖ ^ 2 ∂mu)) / N =
      gamma / 2 * ∫ x, ‖F x‖ ^ 2 ∂mu := by
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [mul_pow, Real.sq_sqrt hgamma, Real.sq_sqrt (Nat.cast_nonneg N), integral_const_mul]
  have hNz : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp [hNz]

theorem gaussianPriorFreeEnergy_eq_energy_sub_information {N k : ℕ} (hN : 0 < N)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    gaussianPriorFreeEnergy N k gamma =
      gamma / 2 * (∫ g, ‖gaussianFeature N k g‖ ^ 2 ∂stdGaussian (Model.Vector N)) -
        gaussianPriorInformation N k gamma := by
  change mixtureFreeEnergy (stdGaussian (Model.Vector N)) (gaussianSignal N k gamma) / N = _
  rw [mixtureFreeEnergy_eq_energy_sub_information _ _ (measurable_gaussianSignal N k gamma)
    (gaussianSignal_memLp_two hN gamma), sub_div]
  exact congrArg (fun t : ℝ ↦ t-gaussianPriorInformation N k gamma)
    (scaled_energy_div (stdGaussian (Model.Vector N)) (gaussianFeature N k) hN hgamma)

theorem sphericalPriorFreeEnergy_eq_energy_sub_information {N k : ℕ} (hN : 0 < N)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    Statistical.sphericalBayesFreeEnergy N k gamma = gamma / 2-sphericalPriorInformation N k gamma := by
  have hlaw : mixtureLaw (Model.spherePrior N) (sphericalSignal N k gamma) =
      Model.observationLaw N k (Real.sqrt gamma) := rfl
  have hFE : Statistical.sphericalBayesFreeEnergy N k gamma =
      mixtureFreeEnergy (Model.spherePrior N) (sphericalSignal N k gamma) / N := by
    rw [mixtureFreeEnergy, hlaw]
    exact (congrArg (fun t : ℝ ↦ t / N) (actualFreeEnergy_eq_klDiv hN (Real.sqrt gamma))).symm
  rw [hFE, mixtureFreeEnergy_eq_energy_sub_information _ _ (measurable_sphericalSignal N k gamma)
    (sphericalSignal_memLp_two hN gamma), sub_div]
  have he := scaled_energy_div (Model.spherePrior N) (Model.feature (N := N) k) hN hgamma
  have hnorm : (∫ x, ‖Model.feature k x‖ ^ 2 ∂Model.spherePrior N) = 1 := by
    calc
      _ = ∫ _x : Model.Vector N, (1 : ℝ) ∂Model.spherePrior N := by
        apply integral_congr_ae
        filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
        simp only [Geometry.feature_unit_norm (k := k) x hx, one_pow]
      _ = 1 := by simp
  rw [hnorm, mul_one] at he
  exact congrArg (fun t : ℝ ↦ t-sphericalPriorInformation N k gamma) he

/-- Explicit nonunit Gaussian-prior penalty; this is not the sphere's constant
quadratic normalizer. -/
theorem gaussianSignal_likelihoodWeight {N k : ℕ} {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (g : Model.Vector N) (y : Model.Tensor N k) :
    mixtureWeight (gaussianSignal N k gamma g) y =
      Real.exp ((Real.sqrt gamma * Real.sqrt N) * Model.score y ((Real.sqrt N)⁻¹ • g) -
        (N : ℝ) * gamma / 2 * ‖gaussianFeature N k g‖ ^ 2) := by
  change Real.exp (inner ℝ ((Real.sqrt gamma * Real.sqrt N) • gaussianFeature N k g) y -
    ‖(Real.sqrt gamma * Real.sqrt N) • gaussianFeature N k g‖ ^ 2 / 2) = _
  rw [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow,
    Real.sq_sqrt hgamma, Real.sq_sqrt (Nat.cast_nonneg N)]
  congr 1
  change (Real.sqrt gamma * Real.sqrt N) * Model.score y ((Real.sqrt N)⁻¹ • g) -
    gamma * (N : ℝ) * ‖gaussianFeature N k g‖ ^ 2 / 2 = _
  ring


end TensorPCA.TensorChannelInformationProofs
