-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationMomentProofs
public import TensorPCA.GaussianMixtureStabilityProofs
public import TensorPCA.FinitePriorChannelProofs

/-! Finite-prior scalar potential approximation under the same Gaussian
coupling. Prior pushforward is proved at the output-law level, retaining the
full nonunit Gaussian likelihood penalty. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationScalarProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianFinitePriorApproximationProofs
open GaussianFinitePriorApproximationMomentProofs GaussianPriorTransferProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

section PriorTransport
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem mixtureFreeEnergy_map_prior (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Ω') (hf : Measurable f) (F : Ω' → E) (hF : Measurable F) :
    mixtureFreeEnergy (μ.map f) F = mixtureFreeEnergy μ (F ∘ f) := by
  unfold mixtureFreeEnergy
  rw [SphericalGaussianTransferProofs.mixtureLaw_map_prior μ f hf F hF]
end PriorTransport

/-- Probability Cauchy--Schwarz twice, with all second/fourth integrability
premises explicit, controls the first two moments by the actual fourth root. -/
theorem first_second_moments_le_fourthRoot {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (h2 : MemLp f 2 μ) (h4 : MemLp (fun x ↦ (f x)^2) 2 μ) :
    (∫ x,f x ∂μ) ≤ Real.sqrt (Real.sqrt (∫ x,(f x)^4 ∂μ)) ∧
      (∫ x,(f x)^2 ∂μ) ≤ (Real.sqrt (Real.sqrt (∫ x,(f x)^4 ∂μ)))^2 := by
  have H1 : (∫ x,f x ∂μ)^2 ≤ ∫ x,(f x)^2 ∂μ := by
    have H := variance_nonneg f μ
    rw [variance_eq_sub h2] at H
    simpa only [Pi.pow_apply,sub_nonneg] using H
  have H2 : (∫ x,(f x)^2 ∂μ)^2 ≤ ∫ x,(f x)^4 ∂μ := by
    have H := variance_nonneg (fun x ↦ (f x)^2) μ
    rw [variance_eq_sub h4] at H
    simpa only [Pi.pow_apply,← pow_mul,Nat.reduceMul,sub_nonneg] using H
  have hs4 : 0 ≤ ∫ x,(f x)^4 ∂μ := integral_nonneg (fun x ↦ by change 0 ≤ (f x)^4; positivity)
  have hs2 : 0 ≤ ∫ x,(f x)^2 ∂μ := integral_nonneg (fun x ↦ by change 0 ≤ (f x)^2; positivity)
  have hFirst : 0 ≤ ∫ x,f x ∂μ := integral_nonneg hf
  have hS4 := Real.sq_sqrt hs4
  have hS2 := Real.sq_sqrt (Real.sqrt_nonneg (∫ x,(f x)^4 ∂μ))
  have hSecond : (∫ x,(f x)^2 ∂μ) ≤ Real.sqrt (∫ x,(f x)^4 ∂μ) := by
    nlinarith [Real.sqrt_nonneg (∫ x,(f x)^4 ∂μ)]
  constructor
  · nlinarith [Real.sqrt_nonneg (Real.sqrt (∫ x,(f x)^4 ∂μ))]
  · nlinarith

theorem quantization_error_memLp (j : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ℝ ↦ |gaussianQuantizer j x-x|) p (stdGaussian ℝ) := by
  apply ((IsGaussian.memLp_id (stdGaussian ℝ) p hp).norm).mono'
    (continuous_abs.measurable.comp ((gaussianQuantizer_measurable j).sub measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    simpa only [Real.norm_eq_abs,abs_abs,id_eq,Function.comp_apply,Pi.sub_apply,gaussianQuantizer] using
      clipRound_error_le_abs (j+1) (D := (j+1)^(j+1)) (pow_pos (Nat.succ_pos j) (j+1)) x)

theorem gaussian_error_moment_bounds (j : ℕ) :
    (∫ x : ℝ,|gaussianQuantizer j x-x| ∂stdGaussian ℝ) ≤ gaussianFourthRootError j ∧
      (∫ x : ℝ,|gaussianQuantizer j x-x|^2 ∂stdGaussian ℝ) ≤ (gaussianFourthRootError j)^2 := by
  have he : Measurable (fun x : ℝ ↦ |gaussianQuantizer j x-x|) :=
    continuous_abs.measurable.comp ((gaussianQuantizer_measurable j).sub measurable_id)
  have hi4 : Integrable (fun x : ℝ ↦ |gaussianQuantizer j x-x|^4) (stdGaussian ℝ) := by
    simpa only [Real.norm_eq_abs,abs_abs] using
      (quantization_error_memLp j 4 (by norm_num)).integrable_norm_pow'
  have hs : MemLp (fun x : ℝ ↦ |gaussianQuantizer j x-x|^2) 2 (stdGaussian ℝ) :=
    (memLp_two_iff_integrable_sq (he.pow_const 2).aestronglyMeasurable).mpr
      (by simpa only [← pow_mul,Nat.reduceMul] using hi4)
  exact first_second_moments_le_fourthRoot (stdGaussian ℝ) _ (fun x ↦ abs_nonneg _)
    (quantization_error_memLp j 2 (by norm_num)) hs

theorem scalar_freeEnergy_approx_le (j : ℕ) (c : ℝ) :
    |mixtureFreeEnergy (stdGaussian ℝ) (fun x : ℝ ↦ c*x)-
      mixtureFreeEnergy (finiteGaussianPrior j) (fun x : ℝ ↦ c*x)| ≤
        c^2*(((j : ℝ)+1)*gaussianFourthRootError j+(1/2 : ℝ)*(gaussianFourthRootError j)^2) := by
  have hm : mixtureFreeEnergy (finiteGaussianPrior j) (fun x : ℝ ↦ c*x) =
      mixtureFreeEnergy (stdGaussian ℝ) (fun x ↦ c*gaussianQuantizer j x) :=
    mixtureFreeEnergy_map_prior (stdGaussian ℝ) (gaussianQuantizer j) (gaussianQuantizer_measurable j)
      (fun x : ℝ ↦ c*x) (by fun_prop)
  rw [hm]
  have H := GaussianMixtureStabilityProofs.abs_mixtureFreeEnergy_sub_le (stdGaussian ℝ)
    (fun x : ℝ ↦ c*x) (fun x ↦ c*gaussianQuantizer j x) (by fun_prop)
    (measurable_const.mul (gaussianQuantizer_measurable j))
    ((IsGaussian.memLp_two_id : MemLp (id : ℝ → ℝ) 2 (stdGaussian ℝ)).const_mul c)
    ((gaussianQuantizer_memLp_two j).const_mul c)
    (Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (gaussianQuantizer_abs_le_bound j x) (abs_nonneg c)))
  have he (x : ℝ) : ‖c*x-c*gaussianQuantizer j x‖ = |c| *|gaussianQuantizer j x-x| := by
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_sub_comm]
  simp_rw [he,mul_pow] at H
  rw [integral_const_mul,integral_const_mul] at H
  have hMom := gaussian_error_moment_bounds j
  have hB : 0 ≤ (j : ℝ)+1 := by positivity
  have hFirst := mul_le_mul_of_nonneg_left hMom.1 hB
  calc
    _ ≤ |c| *((j : ℝ)+1)*(|c| *(∫ x : ℝ,|gaussianQuantizer j x-x| ∂stdGaussian ℝ))+
        (1/2 : ℝ)*(|c|^2*(∫ x : ℝ,|gaussianQuantizer j x-x|^2 ∂stdGaussian ℝ)) := H
    _ = c^2*(((j : ℝ)+1)*(∫ x : ℝ,|gaussianQuantizer j x-x| ∂stdGaussian ℝ)+
        (1/2 : ℝ)*(∫ x : ℝ,|gaussianQuantizer j x-x|^2 ∂stdGaussian ℝ)) := by
      ring_nf
      rw [sq_abs]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hMom.2]) (sq_nonneg c)

/-- A single actual error controls all scalar trial parameters q in [0,1]. -/
def scalarApproximationError (k : ℕ) (gamma : ℝ) (j : ℕ) : ℝ :=
  (k : ℝ)*gamma*(((j : ℝ)+1)*gaussianFourthRootError j+(1/2 : ℝ)*(gaussianFourthRootError j)^2)

theorem scalarPotential_uniform_approx (k : ℕ) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (j : ℕ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    |FinitePriorChannelProofs.scalarPotential (stdGaussian ℝ) id k gamma q-
      FinitePriorChannelProofs.scalarPotential (finiteGaussianPrior j) id k gamma q| ≤
        scalarApproximationError k gamma j := by
  let c := Real.sqrt ((k : ℝ)*gamma*q^(k-1))
  have hc : c^2 = (k : ℝ)*gamma*q^(k-1) := Real.sq_sqrt
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hgamma) (pow_nonneg hq.1 _))
  have hcBound : c^2 ≤ (k : ℝ)*gamma := by
    rw [hc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ hq.1 hq.2) (mul_nonneg (Nat.cast_nonneg k) hgamma)
  unfold FinitePriorChannelProofs.scalarPotential
  simp only [id_eq]
  rw [show ∀ A B P : ℝ,(A-P)-(B-P) = A-B from fun A B P ↦ by ring]
  apply (scalar_freeEnergy_approx_le j c).trans
  exact mul_le_mul_of_nonneg_right hcBound (by unfold gaussianFourthRootError; positivity)

theorem scalarApproximationError_tendsto (k : ℕ) (gamma : ℝ) :
    Tendsto (scalarApproximationError k gamma) atTop (𝓝 (0 : ℝ)) := by
  have hD : Tendsto gaussianFourthRootError atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_zero,one_mul] using weighted_gaussianFourthRootError_tendsto 0
  have hBD : Tendsto (fun j : ℕ ↦ ((j : ℝ)+1)*gaussianFourthRootError j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one] using weighted_gaussianFourthRootError_tendsto 1
  have H := (hBD.add ((hD.pow 2).const_mul (1/2 : ℝ))).const_mul ((k : ℝ)*gamma)
  change Tendsto (fun j : ℕ ↦ (k : ℝ)*gamma*(((j : ℝ)+1)*gaussianFourthRootError j+(1/2 : ℝ)*(gaussianFourthRootError j)^2)) atTop (𝓝 (0 : ℝ))
  simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] using H

end
end TensorPCA.GaussianFinitePriorApproximationScalarProofs
