-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FreeEnergyGradientProofs
public import TensorPCA.GaussianPoincareProofs

/-! Sharp finite null free-energy variance control in the tensor model. -/
@[expose] public section
namespace TensorPCA.NullVarianceProofs
open MeasureTheory ProbabilityTheory ThermalReplicaProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem varNullFE_le_replicaMean {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Coupled.varNullFE N k lam ≤ (lam^2/(N : ℝ))*replicaMean N k lam := by
  have hL2 := FreeEnergyProofs.freeEnergy_memLp (k := k) hN lam 2 (by norm_num)
  have H := GaussianPoincareProofs.variance_stdGaussian_le_fderiv (Model.freeEnergy N k lam)
    (GibbsSmoothProofs.freeEnergy_contDiff_infty hN lam) hL2
    (FreeEnergyGradientProofs.freeEnergy_gradientEnergy_integrable hN lam)
  have hm : AEMeasurable (Model.freeEnergy N k lam) (stdGaussian (Model.Tensor N k)) :=
    (GibbsSmoothProofs.freeEnergy_contDiff_infty hN lam).continuous.measurable.aemeasurable
  rw [variance_eq_integral hm] at H
  simp_rw [FreeEnergyGradientProofs.freeEnergy_fderiv_norm_sq hN lam] at H
  rw [integral_const_mul] at H
  simpa only [Coupled.varNullFE, Coupled.meanNullFE, Model.noiseLaw, replicaMean] using H

theorem varNullFE_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Coupled.varNullFE N k lam ≤ lam^2/(N : ℝ) := by
  calc
    _ ≤ (lam^2/(N : ℝ))*replicaMean N k lam := varNullFE_le_replicaMean hN lam
    _ ≤ (lam^2/(N : ℝ))*1 := mul_le_mul_of_nonneg_left (replicaMean_le_one hN lam)
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg N))
    _ = _ := mul_one _

end
end TensorPCA.NullVarianceProofs
