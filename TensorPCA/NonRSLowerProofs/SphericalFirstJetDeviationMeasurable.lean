-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetBudget
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import TensorPCA.NonRSUpperProofs.GaussianPerturbationDeviationBudget

/-! Joint measurability of the literal selected-coordinate deviations. The selected
energy is independent of the other coefficient amplitudes; only its full-field Gibbs
kernel varies.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalFirstJetDeviationMeasurable
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinInterpolation GaussianSpinComparison
open NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianPerturbationParameter NonRSUpperProofs.GaussianPerturbationDeviation
open NonRSUpperProofs.GaussianPerturbationIntegrated NonRSUpperProofs.GaussianPerturbationSelfAveraging
open SphericalPolynomialFirstJetBudget
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unitLinear_bounded {N K : ℕ} (a : Fin K → ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀ z : UnitSpin N, ‖unitLinear a z‖≤B := by
  refine ⟨Real.sqrt (∑ p, (a p)^2), Real.sqrt_nonneg _, ?_⟩
  intro z
  rw [unitLinear,linear,innerSL_apply_norm]
  exact feature_norm_le a (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (Finset.sum_nonneg (fun p _ ↦ sq_nonneg (a p)))]) z.val z.property

private theorem coefficientOperator_update_mask {N K : ℕ}
    (x : Fin K → ℝ) (p : Fin K) (w : PerturbationDisorder N K) :
    coefficientOperator (Function.update x p 1) (coordinateMask (degreeLabel p) true w)=
      coordinateMask (degreeLabel p) true w := by
  classical
  ext i
  simp only [coefficientOperator,diagonal_apply,coordinateMask,degreeLabel,decide_eq_true_eq]
  by_cases hi : i.1=p
  · simp [hi]
  · simp [hi]

theorem selected_energy_independent {N K : ℕ} (v : ℝ) (x : Fin K → ℝ)
    (p : Fin K) (z : UnitSpin N) (w : PerturbationDisorder N K) :
    unitLinear (coefficients v (Function.update x p 1)) z (coordinateMask (degreeLabel p) true w)=
      unitLinear (coefficients (K := K) v (fun _ ↦ 1)) z (coordinateMask (degreeLabel p) true w) := by
  rw [← unitLinear_coefficientOperator,coefficientOperator_update_mask]

/-- A fixed measurable selected energy on the disorder and spin.
-/
def selectedEnergy {N K : ℕ} (v : ℝ) (p : Fin K)
    (w : PerturbationDisorder N K) (z : UnitSpin N) : ℝ :=
  unitLinear (coefficients (K := K) v (fun _ ↦ 1)) z (coordinateMask (degreeLabel p) true w)

theorem selectedEnergy_measurable {N K : ℕ} (v : ℝ) (p : Fin K) :
    Measurable (fun q : PerturbationDisorder N K×UnitSpin N ↦ selectedEnergy v p q.1 q.2) := by
  exact (measurable_feature_evaluation _ (unitLinear_measurable _)).comp
    (((coordinateMask (degreeLabel p) true).measurable.comp measurable_fst).prodMk measurable_snd)

theorem parameterScore_eq_kernel_mean {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (x : Fin K → ℝ) (p : Fin K) (w : PerturbationDisorder N K) :
    parameterScore nu (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) w (x p)=
      ∫ z, selectedEnergy v p w z ∂parameterizedGibbsKernel nu v (x,w) := by
  let L := unitLinear (N := N) (coefficients v (Function.update x p 1))
  obtain ⟨B,hB,hbound⟩ := unitLinear_bounded (N := N) (coefficients v (Function.update x p 1))
  have hb : ∀ᵐ z ∂nu, ‖L z‖≤B := Eventually.of_forall hbound
  rw [parameterizedGibbsKernel_apply nu hv,← unitLinear_active_full v x p]
  change score nu L (parameterOperator (degreeLabel p) (x p) w) (coordinateMask (degreeLabel p) true w)=
    ∫ z, selectedEnergy v p w z ∂gibbsMeasure nu L (parameterOperator (degreeLabel p) (x p) w)
  rw [score_apply nu L (unitLinear_measurable _) hb,← integral_gibbsMeasure nu L (unitLinear_measurable _) hb]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z ↦ selected_energy_independent v x p z w)

theorem selectedScore_joint_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (p : Fin K) :
    Measurable (fun q : (Fin K → ℝ)×PerturbationDisorder N K ↦
      parameterScore nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p)) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hmap : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×UnitSpin N ↦
      (q.1.2,q.2)) := by fun_prop
  have hm := (selectedEnergy_measurable v p).comp hmap
  simp only [Function.comp_def] at hm
  have H := hm.stronglyMeasurable.integral_kernel_prod_right' (κ := parameterizedGibbsKernel nu v)
  have heq : (fun q : (Fin K → ℝ)×PerturbationDisorder N K ↦
      parameterScore nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p))=
      (fun q : (Fin K → ℝ)×PerturbationDisorder N K ↦
        ∫ z, selectedEnergy v p q.2 z ∂parameterizedGibbsKernel nu v q) := by
    funext q
    exact parameterScore_eq_kernel_mean nu hv q.1 p q.2
  rw [heq]
  exact H.measurable

theorem selectedMeanScore_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (p : Fin K) :
    Measurable (fun x : Fin K → ℝ ↦
      meanScore nu (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) (x p)) :=
  (selectedScore_joint_measurable nu hv p).stronglyMeasurable.integral_prod_right'.measurable

theorem selectedThermalDeviation_joint_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (p : Fin K) :
    Measurable (fun q : (Fin K → ℝ)×PerturbationDisorder N K ↦
      thermalDeviation nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p)) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hm : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×UnitSpin N ↦
      |selectedEnergy v p q.1.2 q.2-
        parameterScore nu (unitLinear (coefficients v (Function.update q.1.1 p 1))) (degreeLabel p) q.1.2 (q.1.1 p)|) :=
    continuous_abs.measurable.comp (((selectedEnergy_measurable v p).comp
      (show Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×UnitSpin N ↦ (q.1.2,q.2)) from by fun_prop)).sub
        ((selectedScore_joint_measurable nu hv p).comp measurable_fst))
  have H := hm.stronglyMeasurable.integral_kernel_prod_right' (κ := parameterizedGibbsKernel nu v)
  have heq (q : (Fin K → ℝ)×PerturbationDisorder N K) :
      thermalDeviation nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p)=
        ∫ z, |selectedEnergy v p q.2 z-
          parameterScore nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p)|
          ∂parameterizedGibbsKernel nu v q := by
    rw [thermalDeviation,parameterizedGibbsKernel_apply nu hv,← unitLinear_active_full v q.1 p]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z ↦ by dsimp only; rw [selected_energy_independent]; rfl)
  have heq' : (fun q : (Fin K → ℝ)×PerturbationDisorder N K ↦
      thermalDeviation nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p))=
      (fun q : (Fin K → ℝ)×PerturbationDisorder N K ↦
        ∫ z, |selectedEnergy v p q.2 z-
          parameterScore nu (unitLinear (coefficients v (Function.update q.1 p 1))) (degreeLabel p) q.2 (q.1 p)|
          ∂parameterizedGibbsKernel nu v q) := funext heq
  rw [heq']
  exact H.measurable

theorem selectedTotalDeviation_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (p : Fin K) :
    Measurable (fun x : Fin K → ℝ ↦
      totalDeviation nu (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) (x p)) := by
  have hThermal := ((selectedThermalDeviation_joint_measurable nu hv p).stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).measurable
  have hFluctuation := (continuous_abs.measurable.comp ((selectedScore_joint_measurable nu hv p).sub
    ((selectedMeanScore_measurable nu hv p).comp measurable_fst))).stronglyMeasurable.integral_prod_right'
      (ν := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) |>.measurable
  exact hThermal.add hFluctuation

theorem degreeError_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (m : ℕ) (p : Fin K) :
    Measurable (fun x : Fin K → ℝ ↦ degreeError nu v x m p) :=
  (selectedTotalDeviation_measurable nu hv p).div
    ((measurable_const.mul (measurable_pi_apply p)).mul_const _)

end
end TensorPCA.NonRSLowerProofs.SphericalFirstJetDeviationMeasurable
