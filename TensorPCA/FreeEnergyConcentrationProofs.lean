-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FreeEnergyGradientProofs
public import Mathlib.Analysis.Calculus.MeanValue

/-! Null free energy has the Gaussian Lipschitz scale |λ|/sqrt(N).
The bounded Gibbs score proves this uniformly in the disorder. -/

@[expose] public section
namespace TensorPCA.FreeEnergyConcentrationProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- Uniform derivative bound with the exact physical N normalization. -/
theorem freeEnergy_fderiv_norm_le {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (w : Model.Tensor N k) :
    ‖fderiv ℝ (Model.freeEnergy N k lam) w‖ ≤ |lam|/Real.sqrt N := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [(FreeEnergyGradientProofs.freeEnergy_hasFDerivAt hN lam w).fderiv,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    _ ≤ (N : ℝ)⁻¹*(|lam| * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left
        (GaussianSpinInterpolation.norm_score_le (Model.spherePrior N)
          (FreeEnergyProofs.thermalLinear N k lam)
          (FreeEnergyProofs.thermalLinear_continuous N k lam).measurable
          (by positivity) (FreeEnergyProofs.thermalLinear_bound hN lam) w)
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = _ := by
      field_simp [hs.ne']
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]
      ring

/-- The free energy is |λ|/sqrt(N)-Lipschitz, including λ=0. -/
theorem freeEnergy_lipschitz {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    LipschitzWith (|lam|/Real.sqrt N).toNNReal (Model.freeEnergy N k lam) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    ((FreeEnergyProofs.freeEnergy_contDiff hN lam).differentiable (by norm_num))
  intro w
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  exact freeEnergy_fderiv_norm_le hN lam w

/-- Zero strength gives the exact zero observable. -/
@[simp] theorem freeEnergy_zero (N k : ℕ) (w : Model.Tensor N k) :
    Model.freeEnergy N k 0 w = 0 := by
  simp [Model.freeEnergy, Model.partitionFunction]

/-- At zero strength every positive centered tail is empty. -/
theorem freeEnergy_zero_tail (N k : ℕ) (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w | |Model.freeEnergy N k 0 w-Coupled.meanNullFE N k 0| > t} = 0 := by
  simp only [Coupled.meanNullFE, freeEnergy_zero, integral_zero, sub_self, abs_zero,
    not_lt.mpr ht.le, ofPred_false, measure_empty]

/-- Gaussian concentration about the null free-energy mean.
Zero strength is covered by its exact empty-tail identity. -/
theorem freeEnergy_gaussian_tail {N k : ℕ} (hN : 0 < N) (lam t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w | |Model.freeEnergy N k lam w-Coupled.meanNullFE N k lam| > t} ≤
      ENNReal.ofReal (2*Real.exp (-(N : ℝ)*t^2/(2*lam^2))) := by
  by_cases hlam : lam = 0
  · subst lam
    rw [freeEnergy_zero_tail N k t ht]
    exact zero_le
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hL : 0 < |lam|/Real.sqrt N := div_pos (abs_pos.mpr hlam) hs
  have hb := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (Model.freeEnergy N k lam) (|lam|/Real.sqrt N) t hL ht (freeEnergy_lipschitz hN lam)
  have he : -t^2/(2*(|lam|/Real.sqrt N)^2) = -(N : ℝ)*t^2/(2*lam^2) := by
    rw [div_pow, sq_abs]
    field_simp [hs.ne', hlam]
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  simpa only [Model.noiseLaw, Coupled.meanNullFE, he] using hb

end
end TensorPCA.FreeEnergyConcentrationProofs
