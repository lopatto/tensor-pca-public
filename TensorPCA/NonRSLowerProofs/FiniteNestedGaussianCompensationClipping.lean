-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianSphericalClipping
public import TensorPCA.NonRSLowerProofs.FiniteGaussianAffineClipping

/-! The compensation exponential clipped on both sides gives a bounded deficit. Its
marked root value is the clipped Gaussian log-step tower minus log cap. The common-
field probability is integrated outside the root logarithm; the raw/clipped
compensation inequality is proved separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianCompensationClipping
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedTransforms FiniteNestedGaussianMarkedLogSteps FiniteNestedGaussianMarkedValues
open FiniteNestedGaussianSphericalClipping FiniteGaussianAffineClipping FiniteGaussianLinearLogSteps
open FiniteGaussianLogStepsCompression OneStepGaussianStepLipschitz
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem compensation_deficit_bounds {b cap s : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) :
    0≤1-max b (min (Real.exp s) cap)/cap ∧
    1-max b (min (Real.exp s) cap)/cap≤1-b/cap ∧
    0≤1-b/cap ∧ 1-b/cap<1 := by
  have hc0 : 0<cap := zero_lt_one.trans_le hcap
  have H := (div_le_one hc0).mpr (max_le (hb1.trans hcap) (min_le_right (Real.exp s) cap))
  have HB := div_le_div_of_nonneg_right (le_max_left b (min (Real.exp s) cap)) hc0.le
  have HC := (div_le_one hc0).mpr (hb1.trans hcap)
  have HP := div_pos hb hc0
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem rootLog_compensation_deficit_eq_clipped_logSteps (depth : ℕ)
    (x : Fin (depth+1)→ℝ) (T : Fin (depth+1)→Model.Vector N→L[ℝ]Model.Vector N)
    (hx : ∀j,0<x j) (lambda : Model.Vector N) {b cap : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) (z : Model.Vector N) :
    rootLog depth x T (fun y => 1-max b (min (Real.exp (inner ℝ lambda y)) cap)/cap) 1 z=
      gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j)))
        (fun y => Real.log (max b (min (Real.exp (inner ℝ lambda y)) cap))) z-Real.log cap := by
  have hc0 : 0<cap := zero_lt_one.trans_le hcap
  have hbc := hb1.trans hcap
  have hZ : Measurable (fun y : Model.Vector N => 1-max b (min (Real.exp (inner ℝ lambda y)) cap)/cap) := by fun_prop
  have ha := (compensation_deficit_bounds (s := 0) hb hb1 hcap).2.2
  have hbound (y : Model.Vector N) := compensation_deficit_bounds (s := inner ℝ lambda y) hb hb1 hcap
  rw [rootLog_eq_logSteps depth x T hZ ha.1 ha.2 (fun y => ⟨(hbound y).1,(hbound y).2.1⟩) hx z]
  have HE : (fun y : Model.Vector N => Real.log (1-(1-max b (min (Real.exp (inner ℝ lambda y)) cap)/cap)))=
      (fun y => Real.log (max b (min (Real.exp (inner ℝ lambda y)) cap))+(-Real.log cap)) := by
    funext y
    have hp : 0<max b (min (Real.exp (inner ℝ lambda y)) cap) := hb.trans_le (le_max_left _ _)
    rw [show 1-(1-max b (min (Real.exp (inner ℝ lambda y)) cap)/cap)=max b (min (Real.exp (inner ℝ lambda y)) cap)/cap by ring,
      Real.log_div hp.ne' hc0.ne']
    rfl
  have hLip : LipschitzWith ‖lambda‖₊
      (fun y : Model.Vector N => Real.log (max b (min (Real.exp (inner ℝ lambda y)) cap))) := by
    simpa only [logClamp_eq_log_mark hb hc0 hbc] using linear_logClamp_lipschitz lambda b cap
  rw [HE,gaussianLogSteps_add_const hLip]
  rfl

theorem scalar_compensation_rootLog_eq_clipped_logSteps (M depth : ℕ)
    (x : Fin (depth+1)→ℝ) (T : Fin (depth+1)→Model.Vector 1→L[ℝ]Model.Vector 1)
    (hx : ∀j,0<x j) {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) (z : Model.Vector 1) :
    rootLog depth x T (fun y => 1-max b (min (Real.exp (Real.sqrt (M : ℝ)*y 0)) cap)/cap) 1 z=
      gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j)))
        (fun y => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*y 0)) cap))) z-Real.log cap := by
  simpa only [scalarCoefficient_inner] using
    rootLog_compensation_deficit_eq_clipped_logSteps depth x T hx (scalarCoefficient M) hb hb1 hcap z

theorem expected_compensation_rootLog_eq_clipped_logSteps (depth : ℕ)
    (x : Fin (depth+1)→ℝ) (T : Fin (depth+1)→Model.Vector N→L[ℝ]Model.Vector N)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1) (lambda : Model.Vector N)
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap)
    (eta : Measure (Model.Vector N)) [IsProbabilityMeasure eta] :
    let Z := fun y => 1-max b (min (Real.exp (inner ℝ lambda y)) cap)/cap
    let clipped := gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j)))
      (fun y => Real.log (max b (min (Real.exp (inner ℝ lambda y)) cap)))
    Integrable (rootLog depth x T Z 1) eta ∧ Integrable clipped eta ∧
      (∫z,rootLog depth x T Z 1 z ∂eta)=(∫z,clipped z ∂eta)-Real.log cap := by
  let Z := fun y : Model.Vector N => 1-max b (min (Real.exp (inner ℝ lambda y)) cap)/cap
  have hZ : Measurable Z := by fun_prop
  have ha := (compensation_deficit_bounds (s := 0) hb hb1 hcap).2.2
  have hbound (y : Model.Vector N) := compensation_deficit_bounds (s := inner ℝ lambda y) hb hb1 hcap
  have hi := rootLog_integrable depth x hx hxm hx1 T hZ ha.1 ha.2
    (fun y => ⟨(hbound y).1,(hbound y).2.1⟩) eta
  have HE (z : Model.Vector N) : gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j)))
      (fun y => Real.log (max b (min (Real.exp (inner ℝ lambda y)) cap))) z=
      rootLog depth x T Z 1 z+Real.log cap := by
    have H := rootLog_compensation_deficit_eq_clipped_logSteps depth x T hx lambda hb hb1 hcap z
    change rootLog depth x T Z 1 z=_ at H
    linarith
  have hic : Integrable (gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j)))
      (fun y => Real.log (max b (min (Real.exp (inner ℝ lambda y)) cap)))) eta :=
    (hi.add (integrable_const (Real.log cap))).congr (ae_of_all _ (fun z => (HE z).symm))
  refine ⟨hi,hic,?_⟩
  rw [integral_congr_ae (ae_of_all _ HE),integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul,add_sub_cancel_right]

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianCompensationClipping
