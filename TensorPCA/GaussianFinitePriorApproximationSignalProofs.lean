-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationCouplingProofs
public import TensorPCA.TensorOrbitAggregationProofs

/-! Quantized tensor signals and dimension-uniform coupling estimates.
Gaussian radius and clipping error remain coupled; Cauchy--Schwarz controls
that dependence using their independently proved fourth moments. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationSignalProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianFinitePriorApproximationProofs
open GaussianFinitePriorApproximationMomentProofs GaussianFinitePriorApproximationTensorProofs
open GaussianFinitePriorApproximationCouplingProofs SphericalGaussianTransferProofs
open TensorChannelInformationProofs TensorOrbitAggregationProofs GaussianCoordinateProjectionProofs OrderedTensorComparisonProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

theorem normalized_smul_norm (N : ℕ) (g : Model.Vector N) :
    ‖(Real.sqrt N)⁻¹ • g‖ = ‖g‖/Real.sqrt N := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  ring

theorem gaussianFeature_sub_quantized_norm_le {N k : ℕ} (hk : 1 ≤ k) (j : ℕ) (g : Model.Vector N) :
    ‖gaussianFeature N k g-gaussianFeature N k (quantizeVector N j g)‖ ≤
      (k : ℝ)*(‖g‖/Real.sqrt N)^(k-1)*(‖quantizeVector N j g-g‖/Real.sqrt N) := by
  have hq : ‖(Real.sqrt N)⁻¹ • quantizeVector N j g‖ ≤ ‖(Real.sqrt N)⁻¹ • g‖ := by
    rw [normalized_smul_norm,normalized_smul_norm]
    exact div_le_div_of_nonneg_right (quantizeVector_norm_le N j g) (Real.sqrt_nonneg _)
  have H := feature_sub_norm_le hk ((Real.sqrt N)⁻¹ • g) ((Real.sqrt N)⁻¹ • quantizeVector N j g)
  rw [max_eq_left hq,normalized_smul_norm,← smul_sub,normalized_smul_norm,
    norm_sub_rev g (quantizeVector N j g)] at H
  exact H

theorem quantized_gaussianFeature_norm_le {N k : ℕ} (hN : 0 < N) (j : ℕ) (g : Model.Vector N) :
    ‖gaussianFeature N k (quantizeVector N j g)‖ ≤ ((j : ℝ)+1)^k := by
  rw [gaussianFeature,Geometry.feature_norm,normalized_smul_norm]
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mpr
  exact (quantizeVector_clip_norm_le N j g).trans_eq (mul_comm _ _)

theorem quantized_gaussianFeature_memLp_two {N k : ℕ} (hN : 0 < N) (j : ℕ) :
    MemLp (fun g ↦ gaussianFeature N k (quantizeVector N j g)) 2 (stdGaussian (Model.Vector N)) :=
  MemLp.of_bound ((measurable_gaussianFeature N k).comp (quantizeVector_measurable N j)).aestronglyMeasurable
    (((j : ℝ)+1)^k) (Eventually.of_forall (quantized_gaussianFeature_norm_le hN j))

/-- Ordinary probability Cauchy--Schwarz, using the exact canonical L2 API. -/
theorem integral_mul_le_sqrt_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf0 : ∀ x,0 ≤ f x) (hg0 : ∀ x,0 ≤ g x) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,f x*g x ∂μ) ≤ Real.sqrt (∫ x,(f x)^2 ∂μ)*Real.sqrt (∫ x,(g x)^2 ∂μ) := by
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using H

def radiusFourthBound (k : ℕ) : ℝ := ∏ i ∈ Finset.range (2*(k-1)),(1+2*(i : ℝ))

theorem radiusFourthBound_nonneg (k : ℕ) : 0 ≤ radiusFourthBound k :=
  Finset.prod_nonneg (fun _i _hi ↦ by positivity)

/-- Genuine dimension-uniform tensor coupling, with no independence assertion
between the Gaussian radius and its quantization error. -/
theorem gaussianFeature_quantization_sq_integral_le {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) (j : ℕ) :
    (∫ g : Model.Vector N,‖gaussianFeature N k g-gaussianFeature N k (quantizeVector N j g)‖^2
      ∂stdGaussian (Model.Vector N)) ≤
        (k : ℝ)^2*Real.sqrt (radiusFourthBound k)*(gaussianFourthRootError j)^2 := by
  let μ := stdGaussian (Model.Vector N)
  let u := fun g : Model.Vector N ↦ (‖g‖/Real.sqrt N)^(2*(k-1))
  let v := fun g : Model.Vector N ↦ (‖quantizeVector N j g-g‖/Real.sqrt N)^2
  have hum : Measurable u := by dsimp [u]; fun_prop
  have hvm : Measurable v := by
    exact ((continuous_norm.measurable.comp ((quantizeVector_measurable N j).sub measurable_id)).div_const _).pow_const 2
  have huSq : Integrable (fun g ↦ (u g)^2) μ := by
    simpa only [u,← pow_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      GaussianMomentProofs.normalized_radius_even_integrable N (2*(k-1))
  have hvSq : Integrable (fun g ↦ (v g)^2) μ := by
    have H := ((quantizeVector_error_memLp N j 4 (by norm_num)).integrable_norm_pow').div_const ((Real.sqrt N)^4)
    simpa only [v,← pow_mul,Nat.reduceMul,div_pow] using H
  have hu : MemLp u 2 μ := (memLp_two_iff_integrable_sq hum.aestronglyMeasurable).mpr huSq
  have hv : MemLp v 2 μ := (memLp_two_iff_integrable_sq hvm.aestronglyMeasurable).mpr hvSq
  have hu0 (g : Model.Vector N) : 0 ≤ u g := by dsimp [u]; positivity
  have hv0 (g : Model.Vector N) : 0 ≤ v g := sq_nonneg _
  have hU : (∫ g,(u g)^2 ∂μ) ≤ radiusFourthBound k := by
    simpa only [u,radiusFourthBound,← pow_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      normalized_radius_even_moment_le hN (2*(k-1))
  have hV : (∫ g,(v g)^2 ∂μ) ≤ (gaussianFourthRootError j)^4 := by
    simpa only [v,← pow_mul,Nat.reduceMul] using normalized_vector_error_fourth_le hN j
  have hVSqrt : Real.sqrt (∫ g,(v g)^2 ∂μ) ≤ (gaussianFourthRootError j)^2 := by
    have H := Real.sqrt_le_sqrt hV
    simpa only [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg (gaussianFourthRootError j))] using H
  have hprod : (∫ g,u g*v g ∂μ) ≤ Real.sqrt (radiusFourthBound k)*(gaussianFourthRootError j)^2 :=
    (integral_mul_le_sqrt_mul μ u v hu0 hv0 hu hv).trans
      (mul_le_mul (Real.sqrt_le_sqrt hU) hVSqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hpoint (g : Model.Vector N) :
      ‖gaussianFeature N k g-gaussianFeature N k (quantizeVector N j g)‖^2 ≤ (k : ℝ)^2*(u g*v g) := by
    have H := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (gaussianFeature_sub_quantized_norm_le hk j g)
    apply H.trans_eq
    have hp : ((‖g‖/Real.sqrt N)^(k-1))^2 = (‖g‖/Real.sqrt N)^(2*(k-1)) := by
      rw [← pow_mul,Nat.mul_comm (k-1) 2]
    rw [mul_pow,mul_pow,hp]
    dsimp [u,v]
    ring
  have hi := ((gaussianFeature_memLp_two (k := k) hN).sub (quantized_gaussianFeature_memLp_two (k := k) hN j)).integrable_norm_pow'
  have H := integral_mono hi ((hu.integrable_mul hv).const_mul ((k : ℝ)^2)) hpoint
  rw [integral_const_mul] at H
  apply H.trans
  simpa only [Pi.mul_apply,mul_assoc] using mul_le_mul_of_nonneg_left hprod (sq_nonneg (k : ℝ))

theorem coordinateProjection_norm_le {α ι : Type*} [Fintype α] [Fintype ι]
    (e : α ↪ ι) (z : EuclideanSpace ℝ ι) : ‖coordinateProjection e z‖ ≤ ‖z‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have H := norm_sq_sub_projection e z
  have hp : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ Set.range e),(z i)^2 :=
    Finset.sum_nonneg (fun _i _hi ↦ sq_nonneg _)
  linarith

/-- Actual unordered aggregation is contractive relative to the full signal. -/
theorem unorderedSignal_norm_le_full (N k : ℕ) (gamma : ℝ) (g : Model.Vector N) :
    ‖unorderedSignal N k gamma g‖ ≤ ‖gaussianSignal N k gamma g‖ := by
  rw [← (orbitEmbedding N k).norm_map (unorderedSignal N k gamma g),orbitEmbedding_signal]
  exact coordinateProjection_norm_le _ _

theorem unorderedSignal_sub_norm_le_full (N k : ℕ) (gamma : ℝ) (g h : Model.Vector N) :
    ‖unorderedSignal N k gamma g-unorderedSignal N k gamma h‖ ≤
      ‖gaussianSignal N k gamma g-gaussianSignal N k gamma h‖ := by
  rw [← (orbitEmbedding N k).norm_map (unorderedSignal N k gamma g-unorderedSignal N k gamma h),
    map_sub,orbitEmbedding_signal,orbitEmbedding_signal,← map_sub]
  exact coordinateProjection_norm_le _ _

theorem quantized_unorderedSignal_norm_le {N k : ℕ} (hN : 0 < N) (gamma : ℝ) (j : ℕ) (g : Model.Vector N) :
    ‖unorderedSignal N k gamma (quantizeVector N j g)‖ ≤
      (Real.sqrt gamma*Real.sqrt N)*((j : ℝ)+1)^k := by
  apply (unorderedSignal_norm_le_full N k gamma _).trans
  rw [gaussianSignal,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left (quantized_gaussianFeature_norm_le hN j g) (by positivity)

theorem quantized_unorderedSignal_memLp_two {N k : ℕ} (hN : 0 < N) (gamma : ℝ) (j : ℕ) :
    MemLp (fun g ↦ unorderedSignal N k gamma (quantizeVector N j g)) 2 (stdGaussian (Model.Vector N)) :=
  MemLp.of_bound ((measurable_unorderedSignal N k gamma).comp (quantizeVector_measurable N j)).aestronglyMeasurable
    ((Real.sqrt gamma*Real.sqrt N)*((j : ℝ)+1)^k)
      (Eventually.of_forall (quantized_unorderedSignal_norm_le hN gamma j))

/-- The actual unordered signal coupling has a squared error of order N,
with an explicit scalar quantization factor tending to zero. -/
theorem unorderedSignal_quantization_sq_integral_le {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (j : ℕ) :
    (∫ g : Model.Vector N,‖unorderedSignal N k gamma g-unorderedSignal N k gamma (quantizeVector N j g)‖^2
      ∂stdGaussian (Model.Vector N)) ≤
        (N : ℝ)*gamma*(k : ℝ)^2*Real.sqrt (radiusFourthBound k)*(gaussianFourthRootError j)^2 := by
  have hs : (Real.sqrt gamma*Real.sqrt N)^2 = gamma*(N : ℝ) := by
    rw [mul_pow,Real.sq_sqrt hgamma,Real.sq_sqrt (Nat.cast_nonneg N)]
  have hpoint (g : Model.Vector N) :
      ‖unorderedSignal N k gamma g-unorderedSignal N k gamma (quantizeVector N j g)‖^2 ≤
        (gamma*(N : ℝ))*‖gaussianFeature N k g-gaussianFeature N k (quantizeVector N j g)‖^2 := by
    have H := unorderedSignal_sub_norm_le_full N k gamma g (quantizeVector N j g)
    rw [gaussianSignal,Pi.smul_apply,Pi.smul_apply,← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at H
    have HH := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr H
    rw [mul_pow,hs] at HH
    exact HH
  have hi := ((unorderedSignal_memLp_two (k := k) hN gamma).sub (quantized_unorderedSignal_memLp_two (k := k) hN gamma j)).integrable_norm_pow'
  have hf := ((gaussianFeature_memLp_two (k := k) hN).sub (quantized_gaussianFeature_memLp_two (k := k) hN j)).integrable_norm_pow'
  have H := integral_mono hi (hf.const_mul (gamma*(N : ℝ))) hpoint
  rw [integral_const_mul] at H
  calc
    _ ≤ (gamma*(N : ℝ))*(∫ g : Model.Vector N,
        ‖gaussianFeature N k g-gaussianFeature N k (quantizeVector N j g)‖^2 ∂stdGaussian (Model.Vector N)) := H
    _ ≤ (gamma*(N : ℝ))*((k : ℝ)^2*Real.sqrt (radiusFourthBound k)*(gaussianFourthRootError j)^2) :=
      mul_le_mul_of_nonneg_left (gaussianFeature_quantization_sq_integral_le hN hk j) (mul_nonneg hgamma (Nat.cast_nonneg N))
    _ = _ := by ring

end
end TensorPCA.GaussianFinitePriorApproximationSignalProofs
