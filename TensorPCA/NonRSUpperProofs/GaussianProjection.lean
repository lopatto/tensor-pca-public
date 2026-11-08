-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed port of the coordinate-projection declarations from
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalGuerraBound.lean
The declaration bodies are retained, with only namespace/import adaptation.
The Gaussian interpolation and thermodynamic declarations are not imported. -/
module
public import TensorPCA.GaussianSpinComparisonProofs
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
/-- The ordinary coordinate projection from a larger Euclidean Gaussian disorder. -/
def projectGaussian {α κ : Type*} [Fintype α] (f : α → κ) (g : EuclideanSpace ℝ κ) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun i => g (f i))

theorem projectGaussian_measurable {α κ : Type*} [Fintype α] [Fintype κ] (f : α → κ) :
    Measurable (projectGaussian f) := by
  have hm : Measurable (fun g : EuclideanSpace ℝ κ => fun i => g (f i)) :=
    measurable_pi_iff.mpr (fun i => (PiLp.continuous_apply 2 (fun _ : κ => ℝ) (f i)).measurable)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.continuous.measurable.comp hm

/-- Projection to any injectively selected coordinate family preserves its independent standard Gaussian law. -/
theorem projectGaussian_hasLaw {α κ : Type*} [Fintype α] [Fintype κ]
    (f : α → κ) (hf : Function.Injective f) :
    HasLaw (projectGaussian f) (SYK.standardGaussianMeasureOnEuclidean α)
      (SYK.standardGaussianMeasureOnEuclidean κ) := by
  have hmκ : Measurable (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.continuous.measurable
  have hmα : Measurable (WithLp.toLp 2 : (α → ℝ) → EuclideanSpace ℝ α) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.continuous.measurable
  have hind : iIndepFun (fun i (z : κ → ℝ) => z (f i)) (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    (iIndepFun_pi (X := fun (_ : κ) (x : ℝ) => x)
      (fun _ => measurable_id.aemeasurable)).precomp hf
  have hlaw : HasLaw (fun z : κ → ℝ => fun i : α => z (f i))
      (Measure.pi (fun _ : α => gaussianReal 0 1)) (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    hind.hasLaw_pi (fun i => (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) (f i)).hasLaw)
  have hraw := (hasLaw_map hmα.aemeasurable).fun_comp hlaw
  refine ⟨(projectGaussian_measurable f).aemeasurable, ?_⟩
  rw [SYK.standardGaussianMeasureOnEuclidean, Measure.map_map (projectGaussian_measurable f) hmκ]
  exact hraw.map_eq

end
end TensorPCA.RetainedCountProofs.SphericalModel
