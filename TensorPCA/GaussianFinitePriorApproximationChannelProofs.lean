-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationSignalProofs
public import TensorPCA.GaussianFinitePriorApproximationAlphabetProofs

/-! Dimension-uniform approximation of the unordered Gaussian prior channel by finite-alphabet channels. Ordered tensors are used only for
signal norm domination; no fixed repeated-index free-energy loss enters the
quantization error. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationChannelProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianPriorTransferProofs
open GaussianFinitePriorApproximationProofs GaussianFinitePriorApproximationMomentProofs
open GaussianFinitePriorApproximationScalarProofs GaussianFinitePriorApproximationAlphabetProofs
open GaussianFinitePriorApproximationCouplingProofs GaussianFinitePriorApproximationSignalProofs
open FinitePriorChannelProofs TensorOrbitAggregationProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

theorem stdGaussian_real_eq_gaussianReal : stdGaussian ℝ = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  funext t
  simp [charFun_stdGaussian,charFun_gaussianReal,Real.norm_eq_abs]
  congr 1
  rw [← Complex.ofReal_pow,sq_abs,Complex.ofReal_pow]
  ring

theorem gaussian_configuration_map (N : ℕ) :
    (configurationPrior (stdGaussian ℝ) N).map (configurationVector (N := N) (id : ℝ → ℝ)) =
      stdGaussian (Model.Vector N) := by
  unfold configurationPrior configurationVector
  simp only [id_eq]
  rw [stdGaussian_real_eq_gaussianReal]
  exact map_pi_eq_stdGaussian

theorem gaussian_realPrior_freeEnergy_eq (N k : ℕ) (gamma : ℝ) :
    freeEnergy (stdGaussian ℝ) id N k gamma = unorderedPriorFreeEnergy N k gamma := by
  have hV : Measurable (configurationVector (N := N) (id : ℝ → ℝ)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin N ↦ ℝ)).measurable
  have H := mixtureFreeEnergy_map_prior (configurationPrior (stdGaussian ℝ) N)
    (configurationVector (N := N) (id : ℝ → ℝ)) hV (unorderedSignal N k gamma) (measurable_unorderedSignal N k gamma)
  rw [gaussian_configuration_map] at H
  unfold freeEnergy unorderedPriorFreeEnergy
  exact congrArg (fun z : ℝ ↦ z/(N : ℝ)) H.symm

theorem quantized_realPrior_freeEnergy_eq (j N k : ℕ) (gamma : ℝ) :
    freeEnergy (finiteGaussianPrior j) id N k gamma =
      mixtureFreeEnergy (stdGaussian (Model.Vector N))
        (fun g ↦ unorderedSignal N k gamma (quantizeVector N j g))/(N : ℝ) := by
  change freeEnergy ((stdGaussian ℝ).map (gaussianQuantizer j)) id N k gamma = _
  rw [← freeEnergy_value_pushforward (stdGaussian ℝ) (gaussianQuantizer j) (gaussianQuantizer_measurable j)]
  have hV : Measurable (configurationVector (N := N) (id : ℝ → ℝ)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin N ↦ ℝ)).measurable
  have H := mixtureFreeEnergy_map_prior (configurationPrior (stdGaussian ℝ) N)
    (configurationVector (N := N) (id : ℝ → ℝ)) hV
    (fun g ↦ unorderedSignal N k gamma (quantizeVector N j g))
    ((measurable_unorderedSignal N k gamma).comp (quantizeVector_measurable N j))
  rw [gaussian_configuration_map] at H
  unfold freeEnergy
  exact congrArg (fun z : ℝ ↦ z/(N : ℝ)) H.symm

/-- Probability Cauchy--Schwarz at a proved squared-norm bound. -/
theorem integral_norm_le_of_sq_integral_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → E)
    (hF : MemLp F 2 μ) {C : ℝ} (hC : 0 ≤ C) (hb : (∫ x,‖F x‖^2 ∂μ) ≤ C^2) :
    (∫ x,‖F x‖ ∂μ) ≤ C := by
  have H := variance_nonneg (fun x ↦ ‖F x‖) μ
  rw [variance_eq_sub hF.norm] at H
  have hs : (∫ x,‖F x‖ ∂μ)^2 ≤ ∫ x,‖F x‖^2 ∂μ := by
    simpa only [Pi.pow_apply,sub_nonneg] using H
  nlinarith only [hs,hb,hC]

def signalSqConstant (k : ℕ) : ℝ := (k : ℝ)^2*Real.sqrt (radiusFourthBound k)

def tensorApproximationError (k : ℕ) (gamma : ℝ) (j : ℕ) : ℝ :=
  (gamma*Real.sqrt (signalSqConstant k))*(((j : ℝ)+1)^k*gaussianFourthRootError j)+
    ((1/2 : ℝ)*gamma*signalSqConstant k)*(gaussianFourthRootError j)^2

theorem signalSqConstant_nonneg (k : ℕ) : 0 ≤ signalSqConstant k := by unfold signalSqConstant; positivity

theorem tensorApproximationError_nonneg (k : ℕ) {gamma : ℝ} (hgamma : 0 ≤ gamma) (j : ℕ) :
    0 ≤ tensorApproximationError k gamma j := by
  unfold tensorApproximationError
  have hD := signalSqConstant_nonneg k
  unfold gaussianFourthRootError
  positivity

theorem tensorApproximationError_tendsto (k : ℕ) (gamma : ℝ) :
    Tendsto (tensorApproximationError k gamma) atTop (𝓝 (0 : ℝ)) := by
  have hD : Tendsto gaussianFourthRootError atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_zero,one_mul] using weighted_gaussianFourthRootError_tendsto 0
  have H := ((weighted_gaussianFourthRootError_tendsto k).const_mul
    (gamma*Real.sqrt (signalSqConstant k))).add ((hD.pow 2).const_mul ((1/2 : ℝ)*gamma*signalSqConstant k))
  change Tendsto (fun j : ℕ ↦ (gamma*Real.sqrt (signalSqConstant k))*
    (((j : ℝ)+1)^k*gaussianFourthRootError j)+((1/2 : ℝ)*gamma*signalSqConstant k)*(gaussianFourthRootError j)^2)
      atTop (𝓝 (0 : ℝ))
  simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] using H

/-- Uniform in every positive dimension: the Gaussian UNORDERED channel is
approximated by the actual finite-support UNORDERED prior channel. -/
theorem unordered_freeEnergy_uniform_approx {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (j : ℕ) :
    |unorderedPriorFreeEnergy N k gamma-freeEnergy (finiteGaussianPrior j) id N k gamma| ≤
      tensorApproximationError k gamma j := by
  let δ := gaussianFourthRootError j
  let B := (j : ℝ)+1
  let D := signalSqConstant k
  let K := (Real.sqrt gamma*Real.sqrt N)*B^k
  let C := (Real.sqrt N*Real.sqrt gamma*Real.sqrt D)*δ
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hD : 0 ≤ D := signalSqConstant_nonneg k
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by dsimp [K,B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCsq : C^2 = (N : ℝ)*gamma*D*δ^2 := by
    dsimp [C]
    simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hgamma,Real.sq_sqrt hD]
  have h2 : (∫ g : Model.Vector N,
      ‖unorderedSignal N k gamma g-unorderedSignal N k gamma (quantizeVector N j g)‖^2
        ∂stdGaussian (Model.Vector N)) ≤ (N : ℝ)*gamma*D*δ^2 := by
    simpa only [D,δ,signalSqConstant,mul_assoc] using unorderedSignal_quantization_sq_integral_le hN hk hgamma j
  have hDiff : MemLp (fun g : Model.Vector N ↦
      unorderedSignal N k gamma g-unorderedSignal N k gamma (quantizeVector N j g)) 2 (stdGaussian (Model.Vector N)) :=
    (unorderedSignal_memLp_two (k := k) hN gamma).sub (quantized_unorderedSignal_memLp_two (k := k) hN gamma j)
  have h1 := integral_norm_le_of_sq_integral_le (stdGaussian (Model.Vector N)) _ hDiff hC (h2.trans_eq hCsq.symm)
  have H := GaussianMixtureStabilityProofs.abs_mixtureFreeEnergy_sub_le (stdGaussian (Model.Vector N))
    (unorderedSignal N k gamma) (fun g ↦ unorderedSignal N k gamma (quantizeVector N j g))
    (measurable_unorderedSignal N k gamma)
    ((measurable_unorderedSignal N k gamma).comp (quantizeVector_measurable N j))
    (unorderedSignal_memLp_two (k := k) hN gamma) (quantized_unorderedSignal_memLp_two (k := k) hN gamma j) (K := K)
    (Eventually.of_forall (quantized_unorderedSignal_norm_le (k := k) hN gamma j))
  have hRaw : K*(∫ g : Model.Vector N,
        ‖unorderedSignal N k gamma g-unorderedSignal N k gamma (quantizeVector N j g)‖ ∂stdGaussian (Model.Vector N))+
      (1/2 : ℝ)*(∫ g : Model.Vector N,
        ‖unorderedSignal N k gamma g-unorderedSignal N k gamma (quantizeVector N j g)‖^2 ∂stdGaussian (Model.Vector N)) ≤
        K*C+(1/2 : ℝ)*((N : ℝ)*gamma*D*δ^2) :=
    add_le_add (mul_le_mul_of_nonneg_left h1 hK) (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have hNsq : Real.sqrt (N : ℝ)*Real.sqrt N = N := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hGsq : Real.sqrt gamma*Real.sqrt gamma = gamma := by
    nlinarith [Real.sq_sqrt hgamma]
  have hKC : K*C = (N : ℝ)*gamma*Real.sqrt D*(B^k*δ) := by
    dsimp [K,C]
    calc
      _ = (Real.sqrt N*Real.sqrt N)*(Real.sqrt gamma*Real.sqrt gamma)*Real.sqrt D*(B^k*δ) := by ring
      _ = _ := by rw [hNsq,hGsq]
  rw [quantized_realPrior_freeEnergy_eq]
  unfold unorderedPriorFreeEnergy
  rw [← sub_div,abs_div,abs_of_pos hn]
  apply (div_le_div_of_nonneg_right H hn.le).trans
  apply (div_le_div_of_nonneg_right hRaw hn.le).trans_eq
  rw [hKC]
  dsimp [tensorApproximationError,D,δ,B]
  field_simp [hn.ne']

/-- The same uniform approximation has the actual finite alphabet required by
the finite-prior theorem, with exact product-law and signal transport. -/
theorem lifted_unordered_freeEnergy_uniform_approx {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (j : ℕ) :
    |unorderedPriorFreeEnergy N k gamma-
      freeEnergy (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma| ≤
        tensorApproximationError k gamma j := by
  rw [lifted_freeEnergy_eq]
  exact unordered_freeEnergy_uniform_approx hN hk hgamma j

/-- Complete genuine quantization obligation: explicit finite-alphabet priors
of second moment at most one approximate the actual unordered tensor and
scalar channels by one error sequence, uniformly in N and q respectively. -/
theorem gaussianFinitePriorUniformApproximation (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    ∃ r : ℕ → ℝ, (∀ j,0 ≤ r j) ∧ Tendsto r atTop (𝓝 (0 : ℝ)) ∧
      ∀ j : ℕ, (∫ s : QuantizedAlphabet j,(s : ℝ)^2 ∂liftedGaussianPrior j) ≤ 1 ∧
        (∀ N : ℕ,1 ≤ N →
          |unorderedPriorFreeEnergy N k gamma-
            freeEnergy (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma| ≤ r j) ∧
        (∀ q ∈ Icc (0 : ℝ) 1,
          |scalarPotential (stdGaussian ℝ) id k gamma q-
            scalarPotential (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) k gamma q| ≤ r j) := by
  let r := fun j ↦ tensorApproximationError k gamma j+scalarApproximationError k gamma j
  have hT (j : ℕ) : 0 ≤ tensorApproximationError k gamma j := tensorApproximationError_nonneg k hgamma j
  have hS (j : ℕ) : 0 ≤ scalarApproximationError k gamma j := by
    unfold scalarApproximationError gaussianFourthRootError
    positivity
  have hR : Tendsto r atTop (𝓝 (0 : ℝ)) := by
    simpa only [r,add_zero] using (tensorApproximationError_tendsto k gamma).add (scalarApproximationError_tendsto k gamma)
  refine ⟨r,fun j ↦ add_nonneg (hT j) (hS j),hR,?_⟩
  intro j
  refine ⟨liftedGaussianPrior_second_moment_le_one j,?_,?_⟩
  · intro N hN
    exact (lifted_unordered_freeEnergy_uniform_approx (by omega : 0 < N) (by omega : 1 ≤ k) hgamma j).trans
      (le_add_of_nonneg_right (hS j))
  · intro q hq
    exact (lifted_scalarPotential_uniform_approx k hgamma j hq).trans (le_add_of_nonneg_left (hT j))

end
end TensorPCA.GaussianFinitePriorApproximationChannelProofs
