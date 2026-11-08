-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GibbsSmoothProofs
public import TensorPCA.ThermalReplicaProofs

/-! The free-energy gradient energy as a two-replica tensor overlap.
This supplies the finite-energy hypothesis for the sharp Gaussian Poincare theorem. -/

@[expose] public section
namespace TensorPCA.FreeEnergyGradientProofs
open Set Filter MeasureTheory ProbabilityTheory FreeEnergyProofs ThermalReplicaProofs
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem norm_sq_eq_coordinate_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    ‖L‖^2 = ∑ i, (L (EuclideanSpace.single i 1))^2 := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm L
  have hnorm : ‖v‖ = ‖L‖ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map L
  have hcoord (i : ι) : v i = L (EuclideanSpace.single i 1) := by
    have H := InnerProductSpace.toDual_symm_apply
      (x := EuclideanSpace.single i (1 : ℝ)) (y := L)
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, v] using H
  have H := EuclideanSpace.real_norm_sq_eq v
  rw [hnorm] at H
  simpa only [hcoord] using H

theorem thermalLinear_eq_scaled (N k : ℕ) (lam : ℝ) :
    thermalLinear N k lam = GaussianSpinInterpolation.scaledLinear (thermalLinear N k 1) lam := by
  funext x
  ext w
  simp only [thermalLinear, GaussianSpinInterpolation.scaledLinear,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem freeEnergy_hasFDerivAt {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    HasFDerivAt (Model.freeEnergy N k lam)
      ((N : ℝ)⁻¹ • GaussianSpinInterpolation.score (Model.spherePrior N) (thermalLinear N k lam) w) w := by
  have H := (GaussianSpinInterpolation.logPartition_hasFDerivAt (Model.spherePrior N)
    (thermalLinear N k lam) (thermalLinear_continuous N k lam).measurable
    (by positivity : 0 ≤ |lam| * Real.sqrt N) (thermalLinear_bound hN lam) w).const_smul (N : ℝ)⁻¹
  convert H using 1
  funext z
  rw [freeEnergy_eq_logPartition, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem freeEnergy_fderiv_apply {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (w d : Model.Tensor N k) :
    fderiv ℝ (Model.freeEnergy N k lam) w d = (lam/(N : ℝ))*
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ thermalLinear N k 1 x d) (thermalLinear N k 1) (lam • w) := by
  rw [(freeEnergy_hasFDerivAt hN lam w).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
    GaussianSpinInterpolation.score_apply (Model.spherePrior N) (thermalLinear N k lam)
      (thermalLinear_continuous N k lam).measurable (thermalLinear_bound hN lam) w d]
  have hfun : (fun x ↦ thermalLinear N k lam x d) = (fun x ↦ lam*thermalLinear N k 1 x d) := by
    funext x
    rw [thermalLinear_eq_scaled N k lam]
    simp only [GaussianSpinInterpolation.scaledLinear, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hfun, GaussianSpinInterpolation.expectation_const_mul,
    thermalLinear_eq_scaled N k lam, GaussianSpinInterpolation.expectation_scaledLinear]
  ring


theorem thermal_coordinate_squares (N k : ℕ) (x : Model.Vector N) :
    (∑ i : Fin k → Fin N,
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x)^2) =
      (N : ℝ)*(inner ℝ x x)^k := by
  have H := base_signedKernel N k x x
  simpa only [GaussianSpinComparison.signedKernel, GaussianSpinComparison.covarianceSign,
    Bool.false_eq_true, ite_false, one_mul, pow_two] using H

theorem thermal_expectation_square_sum {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (w : Model.Tensor N k) :
    (∑ i : Fin k → Fin N, GaussianSpinInterpolation.expectation (Model.spherePrior N)
      (fun x ↦ (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x)^2)
      (thermalLinear N k 1) (lam • w)) = (N : ℝ) := by
  let : IsProbabilityMeasure (thermalGibbs N k lam w) := thermalGibbs_probability hN lam w
  have hL := (thermalLinear_continuous N k 1).measurable
  have hLp (i : Fin k → Fin N) : MemLp
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i) 2
      (thermalGibbs N k lam w) := by
    apply MemLp.of_bound
      (GaussianSpinComparison.coordinateObservable_measurable (thermalLinear N k 1) hL i).aestronglyMeasurable
      (Real.sqrt N)
    have hbound : ∀ᵐ x ∂thermalGibbs N k lam w,
        |GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x| ≤ Real.sqrt N :=
      (thermalGibbs_absolutelyContinuous N k lam w).ae_le
      (GaussianSpinComparison.coordinateObservable_bound (Model.spherePrior N)
        (thermalLinear N k 1) (base_bound hN) i)
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have hmean (i : Fin k → Fin N) :
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x)^2)
        (thermalLinear N k 1) (lam • w) =
      ∫ x, (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x)^2
        ∂thermalGibbs N k lam w := by
    rw [thermalGibbs_eq_baseGibbs]
    exact (GaussianSpinInterpolation.integral_gibbsMeasure (Model.spherePrior N) (thermalLinear N k 1)
      hL (base_bound hN) (lam • w)
      (fun x ↦ (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x)^2)).symm
  simp_rw [hmean]
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ (hLp i).integrable_sq)]
  simp_rw [thermal_coordinate_squares]
  apply integral_eq_const
  filter_upwards [thermalGibbs_unit_ae hN lam w] with x hx
  rw [real_inner_self_eq_norm_sq, show ‖x‖ = 1 from hx]
  simp

theorem thermal_meanSquare_sum {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    (∑ i : Fin k → Fin N, (GaussianSpinInterpolation.expectation (Model.spherePrior N)
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
      (thermalLinear N k 1) (lam • w))^2) = (N : ℝ)*replicaMoment N k lam w := by
  have hL := (thermalLinear_continuous N k 1).measurable
  have hvar (i : Fin k → Fin N) :
      variance (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
        (thermalGibbs N k lam w) =
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i x)^2)
        (thermalLinear N k 1) (lam • w) -
      (GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
        (thermalLinear N k 1) (lam • w))^2 := by
    rw [thermalGibbs_eq_baseGibbs]
    exact (GaussianSpinInterpolation.expectation_variance (Model.spherePrior N)
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i) (thermalLinear N k 1)
      (GaussianSpinComparison.coordinateObservable_measurable (thermalLinear N k 1) hL i) hL
      ((GaussianSpinComparison.coordinateObservable_bound (Model.spherePrior N)
        (thermalLinear N k 1) (base_bound hN) i).and (base_bound hN)) (lam • w)).symm
  have H := thermal_varianceTrace hN lam w
  simp_rw [hvar] at H
  rw [Finset.sum_sub_distrib, thermal_expectation_square_sum hN lam w] at H
  linarith

theorem freeEnergy_fderiv_norm_sq {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    ‖fderiv ℝ (Model.freeEnergy N k lam) w‖^2 =
      (lam^2/(N : ℝ))*replicaMoment N k lam w := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [norm_sq_eq_coordinate_sum]
  simp_rw [freeEnergy_fderiv_apply hN lam w, mul_pow]
  rw [← Finset.mul_sum]
  have H := thermal_meanSquare_sum hN lam w
  unfold GaussianSpinComparison.coordinateObservable at H
  rw [H]
  field_simp [hNr]

theorem freeEnergy_gradientEnergy_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun w ↦ ‖fderiv ℝ (Model.freeEnergy N k lam) w‖^2) (Model.noiseLaw N k) := by
  have H := (replicaMoment_integrable (k := k) hN lam).const_mul (lam^2/(N : ℝ))
  apply H.congr
  exact Filter.Eventually.of_forall (fun w ↦ (freeEnergy_fderiv_norm_sq hN lam w).symm)

end
end TensorPCA.FreeEnergyGradientProofs
