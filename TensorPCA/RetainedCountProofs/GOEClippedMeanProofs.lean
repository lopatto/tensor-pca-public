-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.RetainedCountProofs.GOEClippedDeterminants
public import TensorPCA.RetainedCountProofs.CanonicalGOERealization
public import TensorPCA.RetainedCountProofs.GOEPhysicalPotential
/-! Gaussian clipped-trace moments and ordinary determinant means. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEClippedMeanProofs
noncomputable section
open MeasureTheory ProbabilityTheory
open GOEAsymptotics GOEClippedDeterminants CanonicalGOERealization
open scoped BigOperators Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal actual matrix statistic evaluated at its proved Gaussian realization. -/
def realizedClippedTrace (n : ℕ) (k rho : ℝ)
    (z : EuclideanSpace ℝ (CoefficientIndex (n+1))) : ℝ :=
  matrixClippedTrace (n+1) k rho (gaussianToMatrix (realization (n+1) (n+1) 1 z))

lemma realizedClippedTrace_lipschitz (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith (Real.sqrt 2/rho).toNNReal (realizedClippedTrace n k rho) := by
  have hL : 0 ≤ Real.sqrt 2/rho := by positivity
  have hm : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hs : Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt (2/((n+1 : ℕ) : ℝ)) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg (n+1))]
    congr 1
    field_simp
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.coe_toNNReal _ hL]
  change |realizedClippedTrace n k rho z-realizedClippedTrace n k rho w| ≤
    (Real.sqrt 2/rho)*‖z-w‖
  have h := (matrixClippedTrace_gaussian_lipschitz (n+1) k hrho).dist_le_mul
    (realization (n+1) (n+1) 1 z) (realization (n+1) (n+1) 1 w)
  change |realizedClippedTrace n k rho z-realizedClippedTrace n k rho w| ≤
    (Real.sqrt ((n+1 : ℕ) : ℝ)*(1/rho))*
      ‖realization (n+1) (n+1) 1 z-realization (n+1) (n+1) 1 w‖ at h
  have hW : ‖realization (n+1) (n+1) 1 z-realization (n+1) (n+1) 1 w‖ ≤
      Real.sqrt (2/((n+1 : ℕ) : ℝ))*‖z-w‖ := by
    rw [← map_sub]
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    have hh := mul_le_mul_of_nonneg_right (realization_norm_le (n+1) (n+1) 1) (norm_nonneg (z-w))
    simpa only [mul_one] using hh
  calc
    _ ≤ (Real.sqrt ((n+1 : ℕ) : ℝ)*(1/rho))*
        (Real.sqrt (2/((n+1 : ℕ) : ℝ))*‖z-w‖) :=
      h.trans (mul_le_mul_of_nonneg_left hW (by positivity))
    _ = (Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt (2/((n+1 : ℕ) : ℝ))/rho)*‖z-w‖ := by ring
    _ = _ := by rw [hs]

lemma realizedClippedTrace_integrable (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (realizedClippedTrace n k rho)
      (stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) := by
  let F := realizedClippedTrace n k rho
  let L := Real.sqrt 2/rho
  have hLip := realizedClippedTrace_lipschitz n k hrho
  have hbound (z : EuclideanSpace ℝ (CoefficientIndex (n+1))) :
      |F z| ≤ |F 0|+L*‖z‖ := by
    have h := hLip.dist_le_mul z 0
    simp only [Real.dist_eq, dist_zero_right] at h
    rw [Real.coe_toNNReal _ (div_nonneg (Real.sqrt_nonneg 2) hrho.le)] at h
    change |F z-F 0| ≤ L*‖z‖ at h
    calc
      _ = |(F z-F 0)+F 0| := by rw [sub_add_cancel]
      _ ≤ |F z-F 0|+|F 0| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hi : Integrable (fun z : EuclideanSpace ℝ (CoefficientIndex (n+1)) => |F 0|+L*‖z‖)
      (stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) :=
    (integrable_const _).add ((IsGaussian.integrable_id.norm).const_mul L)
  exact hi.mono' hLip.continuous.aestronglyMeasurable (ae_of_all _ fun z => by
    simpa only [Real.norm_eq_abs] using hbound z)

lemma realizedClippedTrace_hasSubgaussianMGF (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    HasSubgaussianMGF
      (fun z => realizedClippedTrace n k rho z-
        ∫ w, realizedClippedTrace n k rho w
          ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1))))
      (2/rho^2).toNNReal (stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) := by
  have hL : 0 < Real.sqrt 2/rho := by positivity
  have h := SYK.product_standardGaussian_hasSubgaussianMGF
    (realizedClippedTrace n k rho) (Real.sqrt 2/rho) hL
    (realizedClippedTrace_lipschitz n k hrho)
  have hμ : SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex (n+1)) =
      stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1))) := by
    simp only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  rw [hμ] at h
  have hs : (Real.sqrt 2/rho)^2 = 2/rho^2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [hs] using h

lemma realizedClippedTrace_integral_eq (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    (∫ z, realizedClippedTrace n k rho z
      ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) =
      ∫ W, matrixClippedTrace (n+1) k rho W ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1 := by
  have hW := matrix_realization_hasLaw (n+1) (Nat.succ_pos n) (show (0 : ℝ) ≤ 1 by norm_num)
  exact hW.integral_comp (matrixClippedTrace_measurable (n+1) k hrho).aestronglyMeasurable

lemma matrixClippedTrace_integrable (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (matrixClippedTrace (n+1) k rho) (SphericalGaussianJet.goeLaw (n+1) (n+1) 1) := by
  have hW := matrix_realization_hasLaw (n+1) (Nat.succ_pos n) (show (0 : ℝ) ≤ 1 by norm_num)
  rw [← hW.map_eq]
  exact (integrable_map_measure (matrixClippedTrace_measurable (n+1) k hrho).aestronglyMeasurable
    hW.aemeasurable).mpr (realizedClippedTrace_integrable n k hrho)

lemma realizedClippedTrace_exp_integrable (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (fun z => Real.exp (realizedClippedTrace n k rho z))
      (stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) := by
  have h := ((realizedClippedTrace_hasSubgaussianMGF n k hrho).integrable_exp_mul 1).const_mul
    (Real.exp (∫ w, realizedClippedTrace n k rho w
      ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))))
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [one_mul]
  rw [← Real.exp_add]
  congr 1
  ring

lemma realizedClippedTrace_exp_mean_bound (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    (∫ z, Real.exp (realizedClippedTrace n k rho z)
      ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) ≤
      Real.exp ((∫ w, realizedClippedTrace n k rho w
        ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1))))+1/rho^2) := by
  let F := realizedClippedTrace n k rho
  let M := ∫ w, F w ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))
  have h := (realizedClippedTrace_hasSubgaussianMGF n k hrho).mgf_le 1
  simp only [mgf, one_mul, one_pow, mul_one] at h
  rw [Real.coe_toNNReal _ (by positivity)] at h
  have hc : (∫ z, Real.exp (F z-M) ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) ≤
      Real.exp (1/rho^2) := by
    simpa only [show (2/rho^2)/2 = 1/rho^2 by ring] using h
  have he : (fun z => Real.exp (F z)) = fun z => Real.exp M*Real.exp (F z-M) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ z, Real.exp (F z) ∂stdGaussian (EuclideanSpace ℝ (CoefficientIndex (n+1)))) ≤ _
  rw [he, integral_const_mul]
  apply (mul_le_mul_of_nonneg_left hc (Real.exp_pos M).le).trans_eq
  rw [← Real.exp_add]

/-- The ordinary first determinant mean under the actual standard GOE law,
with a finite correction independent of the matrix dimension. -/
theorem standard_mean_le_exp_clipped_mean (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    GOEPhysicalPotential.physicalMean n (n+1) 1 k ≤ Real.exp
      ((∫ W, matrixClippedTrace (n+1) k rho W ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)+1/rho^2) := by
  let E := EuclideanSpace ℝ (CoefficientIndex (n+1))
  let W : E → Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    fun z => gaussianToMatrix (realization (n+1) (n+1) 1 z)
  let D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ → ℝ := fun A => |(k • 1-A).det|
  have hW := matrix_realization_hasLaw (n+1) (Nat.succ_pos n) (show (0 : ℝ) ≤ 1 by norm_num)
  have hD : Measurable D := by dsimp only [D]; fun_prop
  have hdom (z : E) : D (W z) ≤ Real.exp (realizedClippedTrace n k rho z) :=
    matrixAbsoluteDet_le_exp_matrixClippedTrace (n+1) k hrho (W z)
      (realization_symmetric (n+1) (n+1) 1 z)
  have hExp := realizedClippedTrace_exp_integrable n k hrho
  have hInt : Integrable (fun z : E => D (W z)) (stdGaussian E) := by
    apply hExp.mono' (hD.comp ((gaussianToMatrix_measurable (n+1)).comp
      (realization (n+1) (n+1) 1).continuous.measurable)).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change |D (W z)| ≤ Real.exp (realizedClippedTrace n k rho z)
      simpa only [D, abs_abs] using hdom z
  have he : (∫ z : E, D (W z) ∂stdGaussian E) = GOEPhysicalPotential.physicalMean n (n+1) 1 k := by
    exact hW.integral_comp hD.aestronglyMeasurable
  rw [← he]
  apply (integral_mono hInt hExp hdom).trans
  rw [← realizedClippedTrace_integral_eq n k hrho]
  exact realizedClippedTrace_exp_mean_bound n k hrho

end
end TensorPCA.RetainedCountProofs.GOEClippedMeanProofs
