-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression
public import TensorPCA.NonRSLowerProofs.OneStepGaussianZeroMassMerge

/-! A finite initial block of zero-mass Gaussian means combines into one Gaussian mean
with the sum of its nonnegative variances.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianZeroMassCompression
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianStepLipschitz OneStepGaussianZeroMassMerge
open FiniteGaussianLogStepsCompression
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem gaussianLogSteps_append {N : ℕ}
    (first rest : List (ℝ×(Model.Vector N →L[ℝ] E))) (F : E → ℝ) :
    gaussianLogSteps (first++rest) F=gaussianLogSteps first (gaussianLogSteps rest F) := by
  simp only [gaussianLogSteps,List.foldr_append]

theorem gaussianLogSteps_zero_variances_merge {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E)
    (variances : List ℝ) (hvariance : ∀v∈variances,0≤v) (x : E) :
    gaussianLogSteps (variances.map (fun v ↦ (0,Real.sqrt v • T))) F x=
      gaussianLogStep (Real.sqrt variances.sum • T) 0 F x := by
  revert hvariance x
  induction variances with
  | nil =>
    intro hvariance x
    simp [gaussianLogSteps,gaussianLogStep]
  | cons v variances ih =>
    intro hvariance x
    have hv : 0≤v := hvariance v (by simp)
    have htail : ∀w∈variances,0≤w := fun w hw ↦ hvariance w (by simp [hw])
    have hsum : 0≤variances.sum := List.sum_nonneg htail
    have hrec : gaussianLogSteps (variances.map (fun w ↦ (0,Real.sqrt w • T))) F=
        gaussianLogStep (Real.sqrt variances.sum • T) 0 F := funext (ih htail)
    change gaussianLogStep (Real.sqrt v • T) 0
      (gaussianLogSteps (variances.map (fun w ↦ (0,Real.sqrt w • T))) F) x=_
    rw [hrec]
    simpa only [List.sum_cons] using gaussianLogStep_zero_merge_variances hF T hv hsum x

theorem gaussianLogSteps_initial_zero_variances_merge {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E)
    (variances : List ℝ) (hvariance : ∀v∈variances,0≤v)
    (rest : List (ℝ×(Model.Vector N →L[ℝ] E))) (x : E) :
    gaussianLogSteps ((variances.map (fun v ↦ (0,Real.sqrt v • T)))++rest) F x=
      gaussianLogStep (Real.sqrt variances.sum • T) 0 (gaussianLogSteps rest F) x := by
  rw [gaussianLogSteps_append]
  exact gaussianLogSteps_zero_variances_merge (gaussianLogSteps_lipschitz hF rest) T variances hvariance x

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianZeroMassCompression
