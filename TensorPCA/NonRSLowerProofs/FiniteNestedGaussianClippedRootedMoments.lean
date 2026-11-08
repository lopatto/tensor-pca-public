-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedVariableHeights

/-! Common-root Gaussian transport for variable-height moment estimates. The measurable
pushforward preserves the same root scale in both the unconditional marked moments
and the clipped nonlinear tower.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedRootedMoments
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedMoments FiniteNestedMarkedMomentMeasurability
open FiniteNestedGaussianClippedVariableHeights
open FiniteGaussianLogStepsCompression OneStepGaussianTiltEndpoint
open scoped RealInnerProductSpace
noncomputable section
variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

theorem numerator_rooted_log_close {M : ℕ} (hM : 0<M) (depth : ℕ)
    (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→Model.Vector M→L[ℝ]Model.Vector M)
    {cap a : ℝ} (hc : 1≤cap) (ha : 0≤a) (ha1 : a<1) (hca : 1-1/cap≤a)
    (rho : Measure S) [IsProbabilityMeasure rho] (scale : ℝ)
    (mu : Measure V) [IsProbabilityMeasure mu] {A : V→ℝ}
    (hA : Measurable A) (hbA : ∀ᵐv∂mu,1≤A v ∧ A v≤cap) (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p : S×Model.Vector M,weightedMoment (depth+1) (j+1) (x p.1) 0 T
        (fun z => 1-min (sphericalLaplace M z) cap/cap) (scale •p.2) ∂rho.prod (stdGaussian (Model.Vector M)))|≤delta) :
    Integrable (fun v => Real.log (A v)) mu ∧
    Integrable (fun p : S×Model.Vector M => gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
      (fun z => min (Real.log (sphericalLaplace M z)) (Real.log cap)) (scale •p.2)) (rho.prod (stdGaussian (Model.Vector M))) ∧
    |(∫v,Real.log (A v) ∂mu)-
      (∫p : S×Model.Vector M,gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
        (fun z => min (Real.log (sphericalLaplace M z)) (Real.log cap)) (scale •p.2) ∂rho.prod (stdGaussian (Model.Vector M)))|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  let rootMap := fun p : S×Model.Vector M => (p.1,scale •p.2)
  let base := rho.prod (stdGaussian (Model.Vector M))
  let eta := base.map rootMap
  have hMap : Measurable rootMap := by fun_prop
  have hZ : Measurable (fun z : Model.Vector M => 1-min (sphericalLaplace M z) cap/cap) :=
    measurable_const.sub (((sphericalLaplace_measurable M).min measurable_const).div_const cap)
  have hMom (j : ℕ) (hj : j<n) : |(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T
        (fun z => 1-min (sphericalLaplace M z) cap/cap) p.2 ∂eta)|≤delta := by
    have hW := weightedMoment_params_joint_measurable (depth+1) (j+1) T hZ x (fun _ : S => (0 : ℝ)) hxs measurable_const
    rw [integral_map hMap.aemeasurable hW.aestronglyMeasurable]
    exact hmoment j hj
  have H := numerator_clipped_log_close hM depth x hxs hx hxm hx1 T hc ha ha1 hca eta mu hA hbA n hMom
  have hi := (integrable_map_measure H.2.1.aestronglyMeasurable hMap.aemeasurable).mp H.2.1
  have he := integral_map hMap.aemeasurable H.2.1.aestronglyMeasurable
  have HE := H.2.2
  rw [he] at HE
  exact ⟨H.1,hi,HE⟩

theorem compensation_rooted_log_close {N : ℕ} (depth : ℕ)
    (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→Model.Vector N→L[ℝ]Model.Vector N) (lambda : Model.Vector N)
    {b cap a : ℝ} (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap)
    (ha : 0≤a) (ha1 : a<1) (hca : 1-b/cap≤a)
    (rho : Measure S) [IsProbabilityMeasure rho] (scale : ℝ)
    (mu : Measure V) [IsProbabilityMeasure mu] {A : V→ℝ}
    (hA : Measurable A) (hbA : ∀ᵐv∂mu,b≤A v ∧ A v≤cap) (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p : S×Model.Vector N,weightedMoment (depth+1) (j+1) (x p.1) 0 T
        (fun z => 1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap) (scale •p.2) ∂rho.prod (stdGaussian (Model.Vector N)))|≤delta) :
    Integrable (fun v => Real.log (A v)) mu ∧
    Integrable (fun p : S×Model.Vector N => gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
      (fun z => Real.log (max b (min (Real.exp (inner ℝ lambda z)) cap))) (scale •p.2)) (rho.prod (stdGaussian (Model.Vector N))) ∧
    |(∫v,Real.log (A v) ∂mu)-
      (∫p : S×Model.Vector N,gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
        (fun z => Real.log (max b (min (Real.exp (inner ℝ lambda z)) cap))) (scale •p.2) ∂rho.prod (stdGaussian (Model.Vector N)))|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  let rootMap := fun p : S×Model.Vector N => (p.1,scale •p.2)
  let base := rho.prod (stdGaussian (Model.Vector N))
  let eta := base.map rootMap
  have hMap : Measurable rootMap := by fun_prop
  have hZ : Measurable (fun z : Model.Vector N => 1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap) := by fun_prop
  have hMom (j : ℕ) (hj : j<n) : |(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T
        (fun z => 1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap) p.2 ∂eta)|≤delta := by
    have hW := weightedMoment_params_joint_measurable (depth+1) (j+1) T hZ x (fun _ : S => (0 : ℝ)) hxs measurable_const
    rw [integral_map hMap.aemeasurable hW.aestronglyMeasurable]
    exact hmoment j hj
  have H := compensation_clipped_log_close depth x hxs hx hxm hx1 T lambda hb hb1 hc ha ha1 hca eta mu hA hbA n hMom
  have hi := (integrable_map_measure H.2.1.aestronglyMeasurable hMap.aemeasurable).mp H.2.1
  have he := integral_map hMap.aemeasurable H.2.1.aestronglyMeasurable
  have HE := H.2.2
  rw [he] at HE
  exact ⟨H.1,hi,HE⟩

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedRootedMoments
