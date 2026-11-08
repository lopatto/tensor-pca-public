-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairRegularityProofs
public import Mathlib.Analysis.Calculus.MeanValue

/-! Gaussian concentration for the literal positive-window coupled free energy.
The base window measure is finite and nonzero, with its mass offset retained.
No probability-normalization assumption on that base measure is introduced. -/

@[expose] public section
namespace TensorPCA.PairConcentrationProofs
open MeasureTheory ProbabilityTheory Set Filter PairRegularityProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- A bounded finite nonzero Gibbs field has a globally Lipschitz log partition.
The arbitrary base mass contributes a constant and therefore no derivative. -/
theorem logPartition_lipschitz {V H : Type*} [MeasurableSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (GaussianSpinInterpolation.logPartition ν L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    ((GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).differentiable (by norm_num))
  intro w
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hK,
    (GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
  exact GaussianSpinInterpolation.norm_score_le ν L hL hK hb w

/-- Disorder scaling and physical-coordinate normalization for any finite
nonzero bounded-field Gibbs base measure. -/
theorem scaled_logPartition_lipschitz {V H : Type*} [MeasurableSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (lam d : ℝ) (hd : 0 < d) :
    LipschitzWith (K*|lam|/d).toNNReal
      (fun w ↦ GaussianSpinInterpolation.logPartition ν L (lam • w)/d) := by
  have hlog := logPartition_lipschitz ν L hL hK hb
  apply LipschitzWith.of_dist_le_mul
  intro w v
  rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg hK (abs_nonneg _)) hd.le)]
  have H : |GaussianSpinInterpolation.logPartition ν L (lam • w)-
      GaussianSpinInterpolation.logPartition ν L (lam • v)| ≤ K*(|lam| *‖w-v‖) := by
    simpa only [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      Real.coe_toNNReal _ hK] using hlog.dist_le_mul (lam • w) (lam • v)
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hd, dist_eq_norm]
  exact (div_le_div_of_nonneg_right H hd.le).trans_eq (by ring)

/-- The genuine coupled free energy has scale 2|λ|/sqrt(N), independently of
window width and location whenever the actual base mass is positive. -/
theorem pairFreeEnergy_lipschitz {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) :
    LipschitzWith (2*|lam|/Real.sqrt N).toNNReal
      (fun w ↦ Real.log (Coupled.pairPartition N k lam u eta w)/N) := by
  have := pairWindowLaw_neZero N u eta hm
  have H := scaled_logPartition_lipschitz (pairWindowLaw N u eta) (pairLinear N k)
    (pairLinear_continuous N k).measurable (by positivity) (pairLinear_bound hN u eta)
    lam N (Nat.cast_pos.mpr hN)
  have hscale : 2*Real.sqrt N*|lam|/(N : ℝ) = 2*|lam|/Real.sqrt N := by
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
    field_simp [hs.ne']
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  rw [hscale] at H
  convert H using 1
  funext w
  rw [pairPartition_eq_moment]
  rfl

/-- The zero-strength partition retains exactly the unnormalized window mass. -/
@[simp] theorem pairPartition_zero (N k : ℕ) (u eta : ℝ) (w : Model.Tensor N k) :
    Coupled.pairPartition N k 0 u eta w = (pairWindowLaw N u eta).real univ := by
  rw [pairPartition_eq_moment]
  simp [GaussianSpinInterpolation.moment, GaussianSpinInterpolation.weight]

/-- The zero-strength mean includes the logarithmic base-mass offset. -/
@[simp] theorem meanPairFreeEnergy_zero (N k : ℕ) (u eta : ℝ) :
    Coupled.meanPairFreeEnergy N k 0 u eta = Real.log ((pairWindowLaw N u eta).real univ)/N := by
  simp only [Coupled.meanPairFreeEnergy, pairPartition_zero, integral_const, probReal_univ, one_smul]

/-- The reviewed EReal quantity equals the literal finite real mean on its
positive-window branch; no total-log value for an empty window is exported. -/
theorem expectedCoupledFreeEnergy_eq (N k : ℕ) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) :
    Coupled.expectedCoupledFreeEnergy N k lam u eta =
      (Coupled.meanPairFreeEnergy N k lam u eta : EReal) := by
  simp only [Coupled.expectedCoupledFreeEnergy, hm, ite_false]

/-- Gaussian concentration for the actual finite positive-window coupled mean.
The factor four in the variance scale comes from the two thermal replicas. -/
theorem pairFreeEnergy_gaussian_tail {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w | |Real.log (Coupled.pairPartition N k lam u eta w)/N-
      Coupled.meanPairFreeEnergy N k lam u eta| > t} ≤
      ENNReal.ofReal (2*Real.exp (-(N : ℝ)*t^2/(8*lam^2))) := by
  by_cases hlam : lam = 0
  · subst lam
    simp only [pairPartition_zero, meanPairFreeEnergy_zero, sub_self, abs_zero,
      not_lt.mpr ht.le, ofPred_false, measure_empty]
    exact zero_le
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hL : 0 < 2*|lam|/Real.sqrt N := div_pos (mul_pos (by norm_num) (abs_pos.mpr hlam)) hs
  have hb := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (fun w : Model.Tensor N k ↦ Real.log (Coupled.pairPartition N k lam u eta w)/N)
    (2*|lam|/Real.sqrt N) t hL ht (pairFreeEnergy_lipschitz hN lam u eta hm)
  have he : -t^2/(2*(2*|lam|/Real.sqrt N)^2) = -(N : ℝ)*t^2/(8*lam^2) := by
    rw [div_pow, mul_pow, sq_abs]
    field_simp [hs.ne', hlam]
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  simpa only [Model.noiseLaw, Coupled.meanPairFreeEnergy, he] using hb

end
end TensorPCA.PairConcentrationProofs
