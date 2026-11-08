-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import TensorPCA.Coupled
public import TensorPCA.GaussianSpinInterpolationProofs

/-! The thermal partition function and free energy, with their negative
Hamiltonian sign and N normalization, as finite bounded-feature Gibbs integrals. -/

@[expose] public section
namespace TensorPCA.FreeEnergyProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def thermalLinear (N k : ℕ) (lam : ℝ) (x : Model.Vector N) : Model.Tensor N k →L[ℝ] ℝ :=
  (-lam*Real.sqrt N) • innerSL ℝ (Model.feature k x)

theorem thermalLinear_continuous (N k : ℕ) (lam : ℝ) :
    Continuous (thermalLinear N k lam) := by
  change Continuous (fun x : Model.Vector N ↦ (-lam*Real.sqrt N) • innerSL ℝ (Model.feature k x))
  exact (continuous_const : Continuous (fun _ : Model.Vector N ↦ (-lam*Real.sqrt N : ℝ))).smul
    ((innerSL ℝ).continuous.comp (Model.continuous_feature N k))

theorem thermalLinear_bound {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    ∀ᵐ x ∂Model.spherePrior N, ‖thermalLinear N k lam x‖ ≤ |lam| *Real.sqrt N := by
  filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
  rw [thermalLinear, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (Real.sqrt_nonneg _), innerSL_apply_norm, Geometry.feature_unit_norm x hx, mul_one]

theorem partitionFunction_eq_moment (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    Model.partitionFunction N k lam w =
      GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ ↦ 1) (thermalLinear N k lam) w := by
  unfold Model.partitionFunction GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [thermalLinear, ContinuousLinearMap.smul_apply, innerSL_apply_apply, one_mul,
    Model.hamiltonian, Model.score, smul_eq_mul]
  congr 1
  ring

theorem partitionFunction_pos {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    0 < Model.partitionFunction N k lam w := by
  rw [partitionFunction_eq_moment]
  exact GaussianSpinInterpolation.moment_one_pos (Model.spherePrior N) (thermalLinear N k lam)
    (thermalLinear_continuous N k lam).measurable (thermalLinear_bound hN lam) w

theorem freeEnergy_eq_logPartition (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    Model.freeEnergy N k lam w =
      GaussianSpinInterpolation.logPartition (Model.spherePrior N) (thermalLinear N k lam) w/N := by
  rw [Model.freeEnergy, partitionFunction_eq_moment]
  rfl

theorem freeEnergy_contDiff {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    ContDiff ℝ 1 (Model.freeEnergy N k lam) := by
  have H := (GaussianSpinInterpolation.logPartition_contDiff (Model.spherePrior N)
    (thermalLinear N k lam) (thermalLinear_continuous N k lam).measurable
    (by positivity : 0 ≤ |lam| *Real.sqrt N) (thermalLinear_bound hN lam)).div_const (N : ℝ)
  convert H using 1
  funext w
  exact freeEnergy_eq_logPartition N k lam w

theorem freeEnergy_abs_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    |Model.freeEnergy N k lam w| ≤ (|lam| *Real.sqrt N/(N : ℝ))*‖w‖ := by
  have H := GaussianSpinInterpolation.abs_logPartition_le (Model.spherePrior N)
    (thermalLinear N k lam) (thermalLinear_continuous N k lam).measurable
    (thermalLinear_bound hN lam) w
  have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [freeEnergy_eq_logPartition, abs_div, abs_of_nonneg hNr]
  calc
    _ ≤ (|lam| *Real.sqrt N*‖w‖)/(N : ℝ) := div_le_div_of_nonneg_right H (Nat.cast_nonneg N)
    _ = _ := by ring

theorem freeEnergy_memLp {N k : ℕ} (hN : 0 < N) (lam : ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (Model.freeEnergy N k lam) p (Model.noiseLaw N k) := by
  have H := ((IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) p hp).norm).const_smul
    (|lam| *Real.sqrt N/(N : ℝ))
  apply H.mono' (freeEnergy_contDiff hN lam).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w ↦ by
    simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, id_eq] using freeEnergy_abs_le hN lam w)

theorem nullFreeEnergyRegularity : Coupled.NullFreeEnergyRegularity := by
  intro N k hN lam hlam
  have H := freeEnergy_memLp (k := k) (by omega : 0 < N) lam 2 (by norm_num)
  exact ⟨H.integrable (by norm_num), H.integrable_sq⟩

end
end TensorPCA.FreeEnergyProofs
