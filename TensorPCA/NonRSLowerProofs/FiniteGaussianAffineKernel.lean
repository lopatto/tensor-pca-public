-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticStep
public import Mathlib.Probability.Kernel.Composition.Prod

/-! Affine Gaussian Markov kernels and their exact composition. Independent fresh
Gaussian banks are retained until their law is evaluated.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianAffineKernel
open MeasureTheory ProbabilityTheory
open OneStepGaussianTiltJoint
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def affineKernel (M : ℕ) (a s : ℝ) : Kernel (Model.Vector M) (Model.Vector M) :=
  (Kernel.id ×ₖ Kernel.const (Model.Vector M) (stdGaussian (Model.Vector M))).map
    (fun p : Model.Vector M×Model.Vector M => a •p.1+s •p.2)

instance affineKernel_markov (M : ℕ) (a s : ℝ) : IsMarkovKernel (affineKernel M a s) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem affineKernel_apply (M : ℕ) (a s : ℝ) (h : Model.Vector M) :
    affineKernel M a s h=(stdGaussian (Model.Vector M)).map (fun g => a •h+s •g) := by
  rw [affineKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,
    Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,Measure.map_map (by fun_prop) measurable_prodMk_left]
  rfl

theorem affineKernel_comp_product_law (M : ℕ) (a s b t : ℝ) (h : Model.Vector M) :
    (affineKernel M b t ∘ₖ affineKernel M a s) h=
      ((stdGaussian (Model.Vector M)).prod (stdGaussian (Model.Vector M))).map
        (fun p : Model.Vector M×Model.Vector M => b •(a •h+s •p.1)+t •p.2) := by
  let F := fun p : Model.Vector M×Model.Vector M => b •(a •h+s •p.1)+t •p.2
  have hF : Measurable F := by fun_prop
  apply Measure.ext
  intro S hS
  rw [Kernel.comp_apply' _ _ _ hS,affineKernel_apply,
    lintegral_map ((affineKernel M b t).measurable_coe hS) (by fun_prop)]
  have hSet (z : Model.Vector M) : affineKernel M b t z S=
      (stdGaussian (Model.Vector M)) ((fun g => b •z+t •g) ⁻¹' S) := by
    rw [affineKernel_apply,Measure.map_apply (by fun_prop) hS]
  simp_rw [hSet]
  rw [Measure.map_apply hF hS,Measure.prod_apply (hF hS)]
  rfl

theorem affineKernel_comp (M : ℕ) (a s b t : ℝ) :
    affineKernel M b t ∘ₖ affineKernel M a s=
      affineKernel M (b*a) (Real.sqrt ((b*s)^2+t^2)) := by
  apply Kernel.ext
  intro h
  have H := affineKernel_comp_product_law M a s b t h
  have hFun : (fun p : Model.Vector M×Model.Vector M => b •(a •h+s •p.1)+t •p.2)=
      (fun p => (b*a) •h+(b*s) •p.1+t •p.2) := by
    funext p
    module
  rw [hFun,sum_gaussian_law] at H
  rw [affineKernel_apply]
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianAffineKernel
