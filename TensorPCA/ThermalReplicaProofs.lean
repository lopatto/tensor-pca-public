-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FreeEnergyProofs
public import TensorPCA.GaussianSpinComparisonProofs

/-! Thermal Gibbs replicas and the finite Gaussian covariance derivative.
The Gibbs density retains the manuscript's negative Hamiltonian exponent. -/

@[expose] public section
namespace TensorPCA.ThermalReplicaProofs
open Set Filter MeasureTheory ProbabilityTheory FreeEnergyProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def thermalGibbs (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) : Measure (Model.Vector N) :=
  (Model.spherePrior N).withDensity (fun x ↦ ENNReal.ofReal
    (Real.exp (-lam*Model.hamiltonian w x)/Model.partitionFunction N k lam w))

def replicaMoment (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) : ℝ :=
  ∫ z : Model.Vector N × Model.Vector N, (inner ℝ z.1 z.2)^k
    ∂(thermalGibbs N k lam w).prod (thermalGibbs N k lam w)

def replicaMean (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ w, replicaMoment N k lam w ∂Model.noiseLaw N k

theorem thermalLinear_base_apply (N k : ℕ) (lam : ℝ)
    (w : Model.Tensor N k) (x : Model.Vector N) :
    thermalLinear N k 1 x (lam • w) = -lam*Model.hamiltonian w x := by
  simp only [thermalLinear, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    inner_smul_right, smul_eq_mul, Model.hamiltonian, Model.score]
  ring

theorem partitionFunction_eq_baseMoment (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    Model.partitionFunction N k lam w =
      GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ ↦ 1)
        (thermalLinear N k 1) (lam • w) := by
  unfold Model.partitionFunction GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by simp only [thermalLinear_base_apply, one_mul])

theorem thermalGibbs_eq_baseGibbs (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    thermalGibbs N k lam w = GaussianSpinInterpolation.gibbsMeasure (Model.spherePrior N)
      (thermalLinear N k 1) (lam • w) := by
  unfold thermalGibbs GaussianSpinInterpolation.gibbsMeasure
  congr 1
  funext x
  rw [thermalLinear_base_apply, partitionFunction_eq_baseMoment]

theorem base_bound {N k : ℕ} (hN : 0 < N) :
    ∀ᵐ x ∂Model.spherePrior N, ‖thermalLinear N k 1 x‖ ≤ Real.sqrt N := by
  simpa only [abs_one, one_mul] using thermalLinear_bound (k := k) hN 1

theorem thermalGibbs_probability {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    IsProbabilityMeasure (thermalGibbs N k lam w) := by
  rw [thermalGibbs_eq_baseGibbs]
  exact GaussianSpinInterpolation.gibbsMeasure_probability (Model.spherePrior N)
    (thermalLinear N k 1) (thermalLinear_continuous N k 1).measurable (base_bound hN) (lam • w)

theorem thermalGibbs_absolutelyContinuous (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    thermalGibbs N k lam w ≪ Model.spherePrior N := withDensity_absolutelyContinuous _ _

theorem thermalGibbs_unit_ae {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    ∀ᵐ x ∂thermalGibbs N k lam w, x ∈ Model.unitSphere N :=
  (thermalGibbs_absolutelyContinuous N k lam w).ae_le (Geometry.spherePrior_norm_ae hN)

theorem base_signedKernel (N k : ℕ) (x y : Model.Vector N) :
    GaussianSpinComparison.signedKernel (thermalLinear N k 1) (fun _ ↦ false) x y =
      (N : ℝ)*(inner ℝ x y)^k := by
  simp only [GaussianSpinComparison.signedKernel, GaussianSpinComparison.covarianceSign,
    Bool.false_eq_true, ite_false, one_mul, GaussianSpinComparison.coordinateObservable,
    thermalLinear, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, smul_eq_mul]
  have hterm (i : Fin k → Fin N) :
      (-1*Real.sqrt N*Model.feature k x i)*(-1*Real.sqrt N*Model.feature k y i) =
        (N : ℝ)*(Model.feature k y i*Model.feature k x i) := by
    have hs : (Real.sqrt (N : ℝ))^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    calc
      _ = (Real.sqrt (N : ℝ))^2*(Model.feature k y i*Model.feature k x i) := by ring
      _ = _ := by rw [hs]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Geometry.feature_inner]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]


theorem rotatedLinear_false_pi_div_two (N k : ℕ) :
    GaussianSpinComparison.rotatedLinear (thermalLinear N k 1) (fun _ ↦ false) (Real.pi/2) =
      thermalLinear N k 1 := by
  have hrot : GaussianSpinComparison.rotation (fun _ : (Fin k → Fin N) ↦ false) (Real.pi/2) =
      ContinuousLinearMap.id ℝ (Model.Tensor N k) := by
    ext w i
    simp only [GaussianSpinComparison.rotation_apply, GaussianSpinComparison.rotationCoefficient,
      Bool.false_eq_true, ite_false, Real.sin_pi_div_two, one_mul, ContinuousLinearMap.id_apply]
  funext x
  rw [GaussianSpinComparison.rotatedLinear, hrot, ContinuousLinearMap.comp_id]

theorem thermal_varianceTrace {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    (∑ i : Fin k → Fin N, variance
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
      (thermalGibbs N k lam w)) = (N : ℝ)-(N : ℝ)*replicaMoment N k lam w := by
  let : IsProbabilityMeasure (thermalGibbs N k lam w) := thermalGibbs_probability hN lam w
  have H := GaussianSpinComparison.signedVarianceTrace_eq_kernels (Model.spherePrior N)
    (thermalLinear N k 1) (thermalLinear_continuous N k 1).measurable (Real.sqrt_nonneg _)
    (base_bound hN) (fun _ ↦ false) (Real.pi/2) (lam • w)
  rw [rotatedLinear_false_pi_div_two, ← thermalGibbs_eq_baseGibbs] at H
  simp only [GaussianSpinComparison.covarianceSign, Bool.false_eq_true, ite_false, one_mul] at H
  simp_rw [base_signedKernel] at H
  have hdiag : (∫ x : Model.Vector N, (N : ℝ)*(inner ℝ x x)^k ∂thermalGibbs N k lam w) = (N : ℝ) := by
    apply integral_eq_const
    filter_upwards [thermalGibbs_unit_ae hN lam w] with x hx
    rw [real_inner_self_eq_norm_sq, show ‖x‖ = 1 from hx]
    simp
  rw [hdiag, integral_const_mul] at H
  exact H

theorem replicaMoment_abs_le_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    |replicaMoment N k lam w| ≤ 1 := by
  let : IsProbabilityMeasure (thermalGibbs N k lam w) := thermalGibbs_probability hN lam w
  have hunit : ∀ᵐ z ∂(thermalGibbs N k lam w).prod (thermalGibbs N k lam w),
      z.1 ∈ Model.unitSphere N ∧ z.2 ∈ Model.unitSphere N :=
    (Measure.quasiMeasurePreserving_fst.ae (thermalGibbs_unit_ae hN lam w)).and
      (Measure.quasiMeasurePreserving_snd.ae (thermalGibbs_unit_ae hN lam w))
  have H := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := (thermalGibbs N k lam w).prod (thermalGibbs N k lam w))
    (f := fun z : Model.Vector N × Model.Vector N ↦ (inner ℝ z.1 z.2)^k) (by
      filter_upwards [hunit] with z hz
      rw [Real.norm_eq_abs, abs_pow]
      apply pow_le_one₀ (abs_nonneg _)
      simpa only [show ‖z.1‖ = 1 from hz.1, show ‖z.2‖ = 1 from hz.2, one_mul] using
        abs_real_inner_le_norm z.1 z.2)
  simpa only [replicaMoment, Real.norm_eq_abs, probReal_univ, mul_one] using H


theorem thermalCoordinateVariance_continuous {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (i : Fin k → Fin N) : Continuous (fun w : Model.Tensor N k ↦ variance
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i) (thermalGibbs N k lam w)) := by
  let ρ := GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i
  have hL := (thermalLinear_continuous N k 1).measurable
  have hρ := GaussianSpinComparison.coordinateObservable_measurable (thermalLinear N k 1) hL i
  have hb := (GaussianSpinComparison.coordinateObservable_bound (Model.spherePrior N)
    (thermalLinear N k 1) (base_bound hN) i).and (base_bound (k := k) hN)
  have hb2 : ∀ᵐ x ∂Model.spherePrior N, |(ρ x)^2| ≤ (Real.sqrt N)^2 ∧
      ‖thermalLinear N k 1 x‖ ≤ Real.sqrt N := by
    filter_upwards [hb] with x hx
    refine ⟨?_, hx.2⟩
    simpa only [abs_pow, sq_abs] using
      (sq_le_sq₀ (abs_nonneg (ρ x)) (Real.sqrt_nonneg (N : ℝ))).mpr hx.1
  have hc1 := (GaussianSpinInterpolation.expectation_contDiff (Model.spherePrior N) ρ
    (thermalLinear N k 1) hρ hL (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hb).continuous.comp
      (continuous_id.const_smul lam)
  have hc2 := (GaussianSpinInterpolation.expectation_contDiff (Model.spherePrior N) (fun x ↦ (ρ x)^2)
    (thermalLinear N k 1) (hρ.pow_const 2) hL (sq_nonneg _) (Real.sqrt_nonneg _) hb2).continuous.comp
      (continuous_id.const_smul lam)
  convert hc2.sub (hc1.pow 2) using 1
  funext w
  rw [thermalGibbs_eq_baseGibbs]
  exact (GaussianSpinInterpolation.expectation_variance (Model.spherePrior N) ρ
    (thermalLinear N k 1) hρ hL hb (lam • w)).symm

theorem replicaMoment_continuous {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Continuous (replicaMoment N k lam) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hfun : replicaMoment N k lam = (fun w : Model.Tensor N k ↦ 1-
      (∑ i : Fin k → Fin N, variance
        (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
        (thermalGibbs N k lam w))/(N : ℝ)) := by
    funext w
    have H := thermal_varianceTrace hN lam w
    field_simp [hNr]
    nlinarith
  rw [hfun]
  exact continuous_const.sub ((continuous_finset_sum Finset.univ
    (fun i _ ↦ thermalCoordinateVariance_continuous hN lam i)).div_const (N : ℝ))

theorem replicaMoment_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (replicaMoment N k lam) (Model.noiseLaw N k) := by
  apply Integrable.of_bound (replicaMoment_continuous hN lam).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun w ↦ by
    simpa only [Real.norm_eq_abs] using replicaMoment_abs_le_one hN lam w)

theorem thermalCoordinateVariance_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (i : Fin k → Fin N) : Integrable (fun w : Model.Tensor N k ↦ variance
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i) (thermalGibbs N k lam w))
      (Model.noiseLaw N k) := by
  apply Integrable.of_bound (thermalCoordinateVariance_continuous hN lam i).aestronglyMeasurable (2*N)
  apply Filter.Eventually.of_forall
  intro w
  have hvar : 0 ≤ variance (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
      (thermalGibbs N k lam w) := variance_nonneg _ _
  rw [Real.norm_eq_abs, abs_of_nonneg hvar]
  have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    variance_nonneg (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) j)
      (thermalGibbs N k lam w)) (Finset.mem_univ i)
  have hm := (abs_le.mp (replicaMoment_abs_le_one hN lam w)).1
  have hmul := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have ht := thermal_varianceTrace hN lam w
  nlinarith


theorem averagedLogPartition_hasDerivAt_replica {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    HasDerivAt (GaussianSpinInterpolation.averagedLogPartition (Model.spherePrior N)
      (thermalLinear N k 1)) (lam*(N : ℝ)*(1-replicaMean N k lam)) lam := by
  have hL := (thermalLinear_continuous N k 1).measurable
  have H := GaussianSpinInterpolation.averagedLogPartition_hasDerivAt_covarianceTrace
    (Model.spherePrior N) (thermalLinear N k 1) hL (Real.sqrt_nonneg _) (base_bound hN) lam
  have hvar (i : Fin k → Fin N) (w : Model.Tensor N k) :
      GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ (thermalLinear N k 1 x (EuclideanSpace.single i 1))^2)
        (thermalLinear N k 1) (lam • w) -
      (GaussianSpinInterpolation.expectation (Model.spherePrior N)
        (fun x ↦ thermalLinear N k 1 x (EuclideanSpace.single i 1))
        (thermalLinear N k 1) (lam • w))^2 =
      variance (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
        (thermalGibbs N k lam w) := by
    rw [thermalGibbs_eq_baseGibbs]
    exact GaussianSpinInterpolation.expectation_variance (Model.spherePrior N)
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i)
      (thermalLinear N k 1)
      (GaussianSpinComparison.coordinateObservable_measurable (thermalLinear N k 1) hL i) hL
      ((GaussianSpinComparison.coordinateObservable_bound (Model.spherePrior N)
        (thermalLinear N k 1) (base_bound hN) i).and (base_bound hN)) (lam • w)
  simp_rw [hvar, GaussianConcentrationBridge.standardGaussianMeasure_bridge] at H
  have hsum : (∑ i : Fin k → Fin N, ∫ w, variance
      (GaussianSpinComparison.coordinateObservable (thermalLinear N k 1) i) (thermalGibbs N k lam w)
        ∂Model.noiseLaw N k) = (N : ℝ)*(1-replicaMean N k lam) := by
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ thermalCoordinateVariance_integrable hN lam i)]
    simp_rw [thermal_varianceTrace hN lam]
    rw [integral_sub (integrable_const _) ((replicaMoment_integrable hN lam).const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, replicaMean]
    ring
  simp only [Model.noiseLaw] at hsum
  simpa only [hsum, mul_assoc] using H

theorem meanNullFE_eq_averagedLogPartition (N k : ℕ) (lam : ℝ) :
    Coupled.meanNullFE N k lam = GaussianSpinInterpolation.averagedLogPartition
      (Model.spherePrior N) (thermalLinear N k 1) lam/(N : ℝ) := by
  rw [Coupled.meanNullFE, GaussianSpinInterpolation.averagedLogPartition,
    GaussianConcentrationBridge.standardGaussianMeasure_bridge]
  rw [← integral_div]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  rw [Model.freeEnergy, partitionFunction_eq_baseMoment]
  rfl

theorem meanNullFE_hasDerivAt {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    HasDerivAt (Coupled.meanNullFE N k) (lam*(1-replicaMean N k lam)) lam := by
  have H := (averagedLogPartition_hasDerivAt_replica (k := k) hN lam).div_const (N : ℝ)
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  convert H using 1
  · funext u
    exact meanNullFE_eq_averagedLogPartition N k u
  · field_simp [hNr]

def freeEnergyGap (N k : ℕ) (lam : ℝ) : ℝ := lam^2/2-Coupled.meanNullFE N k lam

theorem freeEnergyGap_hasDerivAt {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    HasDerivAt (freeEnergyGap N k) (lam*replicaMean N k lam) lam := by
  have H := (((hasDerivAt_id lam).pow 2).div_const 2).sub (meanNullFE_hasDerivAt (k := k) hN lam)
  convert H using 1
  · rfl
  · simp only [id_eq]
    ring


theorem replicaMean_le_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) : replicaMean N k lam ≤ 1 := by
  have H := norm_integral_le_of_norm_le_const (μ := Model.noiseLaw N k) (C := (1 : ℝ))
    (f := replicaMoment N k lam)
    (Filter.Eventually.of_forall (fun w ↦ by
      simpa only [Real.norm_eq_abs] using replicaMoment_abs_le_one (k := k) hN lam w))
  have Ha : |replicaMean N k lam| ≤ 1 := by
    simpa only [replicaMean, Real.norm_eq_abs, probReal_univ, mul_one] using H
  exact (le_abs_self _).trans Ha

theorem replicaMean_nonneg (N k : ℕ) (heven : Even k) (lam : ℝ) : 0 ≤ replicaMean N k lam := by
  apply integral_nonneg
  intro w
  apply integral_nonneg
  intro z
  exact heven.pow_nonneg _

theorem meanNullFE_zero (N k : ℕ) : Coupled.meanNullFE N k 0 = 0 := by
  simp [Coupled.meanNullFE, Model.freeEnergy, Model.partitionFunction]

theorem freeEnergyGap_zero (N k : ℕ) : freeEnergyGap N k 0 = 0 := by
  simp only [freeEnergyGap, meanNullFE_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_self]

theorem meanNullFE_nonneg {N k : ℕ} (hN : 0 < N) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ Coupled.meanNullFE N k lam := by
  have hd : Differentiable ℝ (Coupled.meanNullFE N k) :=
    fun u ↦ (meanNullFE_hasDerivAt hN u).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hd.continuous.continuousOn
    hd.differentiableOn (fun u hu ↦ by
      rw [(meanNullFE_hasDerivAt hN u).deriv]
      exact mul_nonneg (show 0 ≤ u from interior_subset hu)
        (sub_nonneg.mpr (replicaMean_le_one hN u)))
  have H := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hlam hlam
  simpa only [meanNullFE_zero] using H

theorem freeEnergyGap_bounds {N k : ℕ} (hN : 0 < N) (heven : Even k)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ freeEnergyGap N k lam ∧ freeEnergyGap N k lam ≤ lam^2/2 := by
  have hd : Differentiable ℝ (freeEnergyGap N k) :=
    fun u ↦ (freeEnergyGap_hasDerivAt hN u).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hd.continuous.continuousOn
    hd.differentiableOn (fun u hu ↦ by
      rw [(freeEnergyGap_hasDerivAt hN u).deriv]
      exact mul_nonneg (show 0 ≤ u from interior_subset hu) (replicaMean_nonneg N k heven u))
  constructor
  · have H := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hlam hlam
    simpa only [freeEnergyGap_zero] using H
  · have H := meanNullFE_nonneg (k := k) hN hlam
    unfold freeEnergyGap
    linarith

end
end TensorPCA.ThermalReplicaProofs
