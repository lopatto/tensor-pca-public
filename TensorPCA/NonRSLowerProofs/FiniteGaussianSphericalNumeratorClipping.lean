-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianNumeratorTowerContraction
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphereLogStepsCompression
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltOuter

/-! Tower contraction for the spherical Laplace numerator and its upper clipping. The
compensation exponential is not required to be at least one.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClipping
open MeasureTheory ProbabilityTheory
open FiniteGaussianNumeratorTowerContraction FiniteGaussianLogStepsCompression
open FiniteGaussianSphereLogStepsCompression OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open FiniteGaussianOrdinaryStepsExponentialGrowth
open scoped NNReal
noncomputable section
variable {M : ℕ}

theorem exp_min_log_eq {f L : ℝ} (hL : 0<L) : Real.exp (min f (Real.log L))=min (Real.exp f) L := by
  by_cases h : f≤Real.log L
  · rw [min_eq_left h,min_eq_left (by simpa only [Real.exp_log hL] using Real.exp_le_exp.mpr h)]
  · have h' := le_of_not_ge h
    rw [min_eq_right h',min_eq_right (by simpa only [Real.exp_log hL] using Real.exp_le_exp.mpr h'),Real.exp_log hL]

theorem spherical_root_clipping_bound (hM : 0<M)
    (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    (hm : ∀s∈steps,0<s.1 ∧ s.1≤1) (horder : steps.Pairwise (fun s t => s.1≤t.1))
    {L : ℝ} (hL : 1≤L) (z : Model.Vector M) :
    0≤gaussianLogSteps steps (fun y => Real.log (sphericalLaplace M y)) z-
        gaussianLogSteps steps (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)) z ∧
      gaussianLogSteps steps (fun y => Real.log (sphericalLaplace M y)) z-
        gaussianLogSteps steps (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)) z≤
      gaussianLogSteps (steps.map (fun s => (0,s.2))) (fun y => sphericalLaplace M y-min (sphericalLaplace M y) L) z := by
  have hF := log_sphericalLaplace_lipschitz hM
  have hb (y : Model.Vector M) : 0≤min (Real.log (sphericalLaplace M y)) (Real.log L) ∧
      min (Real.log (sphericalLaplace M y)) (Real.log L)≤Real.log (sphericalLaplace M y) :=
    ⟨le_min (Real.log_nonneg (one_le_sphericalLaplace hM y)) (Real.log_nonneg hL),min_le_left _ _⟩
  have H := root_contraction steps hF (hF.min_const (Real.log L)) hb hm horder z
  have HE : (fun y : Model.Vector M => Real.exp (Real.log (sphericalLaplace M y))-
      Real.exp (min (Real.log (sphericalLaplace M y)) (Real.log L)))=
      (fun y => sphericalLaplace M y-min (sphericalLaplace M y) L) := by
    funext y
    rw [exp_min_log_eq (zero_lt_one.trans_le hL),Real.exp_log (sphericalLaplace_pos hM y)]
  rw [HE] at H
  exact H

theorem spherical_tail_exponential_growth (hM : 0<M) {L : ℝ} (hL : 1≤L) (z : Model.Vector M) :
    |sphericalLaplace M z-min (sphericalLaplace M z) L|≤2*Real.exp ((2*Real.sqrt (M : ℝ))*‖z‖) := by
  have hF := log_sphericalLaplace_lipschitz hM
  have H := exp_sub_growth hF (hF.min_const (Real.log L)) z
  have hZ : sphericalLaplace M 0=1 := by simp [sphericalLaplace]
  have hC : min (Real.log (sphericalLaplace M 0)) (Real.log L)=0 := by
    rw [hZ,Real.log_one,min_eq_left (Real.log_nonneg hL)]
  have htwo : (1 : ℝ)+1=2 := by norm_num
  simpa only [exp_min_log_eq (zero_lt_one.trans_le hL),Real.exp_log (sphericalLaplace_pos hM z),hZ,
    hC,Real.log_one,min_eq_left (Real.log_nonneg hL),abs_zero,Real.exp_zero,htwo,
    Real.coe_toNNReal _ (Real.sqrt_nonneg _),← two_mul] using H

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClipping
