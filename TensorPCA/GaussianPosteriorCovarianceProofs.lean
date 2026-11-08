-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPosteriorIBPProofs

/-!
# Gaussian integration by parts for the nonunit posterior

The observation and normalized posterior are the Gaussian channel laws.
Bounded signal and observable hypotheses are used only for the finite-prior
interpolation calculus.
-/
@[expose] public section

namespace TensorPCA.GaussianPosteriorCovarianceProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSpinInterpolation GaussianAffineGibbsProofs GaussianPosteriorIBPProofs
open scoped RealInnerProductSpace

theorem stronglyMeasurable_posteriorMean {Omega E V : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [SFinite mu] (F : Omega → E) (a : Omega → V)
    (ha : StronglyMeasurable a) : StronglyMeasurable (posteriorMean mu F a) :=
  ha.integral_kernel

theorem norm_posteriorMean_le {Omega E V : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (a : Omega → V) {C : ℝ} (haB : ∀ᵐ x ∂mu, ‖a x‖ ≤ C) (y : E) :
    ‖posteriorMean mu F a y‖ ≤ C := by
  have : IsMarkovKernel (posteriorKernel mu F) := posteriorKernel_isMarkov mu F hF
  have hac : posteriorKernel mu F y ≪ mu := by
    rw [posteriorKernel_apply mu F hF]
    exact withDensity_absolutelyContinuous mu _
  simpa only [posteriorMean, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (hac.ae_le haB))

theorem integral_posteriorMean {Omega E V : Type*} [MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (a : Omega → V) (ha : StronglyMeasurable a) (haInt : Integrable a mu) :
    (∫ z : Omega × E, posteriorMean mu F a (F z.1+z.2) ∂mu.prod (stdGaussian E)) =
      ∫ x, a x ∂mu := by
  have hObs : Measurable (fun z : Omega × E ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  rw [integral_congr_ae (posteriorMean_ae_eq_condExp mu F hF a ha haInt),
    integral_condExp (μ := mu.prod (stdGaussian E)) (f := fun z : Omega × E ↦ a z.1) hObs.comap_le]
  simpa only [probReal_univ, one_smul] using (integral_fun_fst (μ := mu) (ν := stdGaussian E) a)

theorem posteriorMean_gaussian_ibp {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → EuclideanSpace ℝ iota) (hF : Measurable F)
    (a : Omega → ℝ) (ha : Measurable a) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (haB : ∀ᵐ x ∂mu, |a x| ≤ C) (hFB : ∀ᵐ x ∂mu, ‖F x‖ ≤ K)
    (v d : EuclideanSpace ℝ iota) :
    (∫ w, inner ℝ d w * posteriorMean mu F a (v+w)
      ∂stdGaussian (EuclideanSpace ℝ iota)) =
      ∫ w, posteriorMean mu F (fun x ↦ a x * inner ℝ (F x) d) (v+w) -
        posteriorMean mu F a (v+w) * posteriorMean mu F (fun x ↦ inner ℝ (F x) d) (v+w)
        ∂stdGaussian (EuclideanSpace ℝ iota) := by
  have hL := measurable_augmentedField F hF
  have hLB := augmentedField_ae_bound mu F hK hFB
  have hb : ∀ᵐ x ∂mu, |a x| ≤ C ∧ ‖augmentedField F x‖ ≤ K+K^2 :=
    haB.and hLB
  have h := affine_expectation_ibp mu a (augmentedField F) ha hL hC
    (by positivity : 0 ≤ K+K^2) hb
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ iota) ℝ) (v, -(1:ℝ)/2) d
  simp only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero] at h
  calc
    _ = ∫ w, inner ℝ d w * expectation mu a (augmentedField F) (v+w, -(1:ℝ)/2)
        ∂stdGaussian (EuclideanSpace ℝ iota) := by
      apply integral_congr_ae
      exact .of_forall fun w ↦ by
        dsimp only
        rw [posteriorMean_eq_expectation mu F hF hK hFB]
    _ = ∫ w, expectationDerivative mu a (augmentedField F) (v+w, -(1:ℝ)/2) (d,0)
        ∂stdGaussian (EuclideanSpace ℝ iota) := h
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun w ↦ ?_
      dsimp only
      rw [expectationDerivative_apply mu a (augmentedField F) ha hL hb]
      simp only [augmentedField_apply, mul_zero, add_zero]
      rw [← posteriorMean_eq_expectation mu F hF hK hFB,
        ← posteriorMean_eq_expectation mu F hF hK hFB,
        ← posteriorMean_eq_expectation mu F hF hK hFB]


end TensorPCA.GaussianPosteriorCovarianceProofs
