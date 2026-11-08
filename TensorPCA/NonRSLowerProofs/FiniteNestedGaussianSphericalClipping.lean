-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedLogSteps
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClipping

/-! Bounded-deficit normalization of the clipped spherical numerator. The marked root
value equals the clipped Gaussian log-step tower minus log L; physical moment
matching is treated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianSphericalClipping
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedTransforms FiniteNestedGaussianMarkedLogSteps
open FiniteGaussianLogStepsCompression OneStepGaussianStepLipschitz
open FiniteGaussianSphereLogStepsCompression OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M : ℕ}

theorem gaussianLogSteps_add_const {K : ℝ≥0} {F : Model.Vector M→ℝ}
    (hF : LipschitzWith K F) (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    (c : ℝ) (z : Model.Vector M) :
    gaussianLogSteps steps (fun y => F y+c) z=gaussianLogSteps steps F z+c := by
  induction steps generalizing z with
  | nil => rfl
  | cons s steps ih =>
    have HE : gaussianLogSteps steps (fun y => F y+c)=(fun y => gaussianLogSteps steps F y+c) := funext ih
    change gaussianLogStep s.2 s.1 (gaussianLogSteps steps (fun y => F y+c)) z=_
    rw [HE]
    exact OneStepGaussianStepLipschitzOrder.gaussianLogStep_add_const (gaussianLogSteps_lipschitz hF steps) s.2 s.1 c z

theorem spherical_deficit_bounds (hM : 0<M) {L : ℝ} (hL : 1≤L) (y : Model.Vector M) :
    0≤1-min (sphericalLaplace M y) L/L ∧
    1-min (sphericalLaplace M y) L/L≤1-1/L ∧ 0≤1-1/L ∧ 1-1/L<1 := by
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hMin : 1≤min (sphericalLaplace M y) L := le_min (one_le_sphericalLaplace hM y) hL
  have H := (div_le_one hL0).mpr (min_le_right (sphericalLaplace M y) L)
  have HB := div_le_div_of_nonneg_right hMin hL0.le
  have HC := (div_le_one hL0).mpr hL
  have HP := div_pos (by norm_num : (0 : ℝ)<1) hL0
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem spherical_log_deficit_eq (hM : 0<M) {L : ℝ} (hL : 1≤L) (y : Model.Vector M) :
    Real.log (1-(1-min (sphericalLaplace M y) L/L))=
      min (Real.log (sphericalLaplace M y)) (Real.log L)-Real.log L := by
  have hY : 0<sphericalLaplace M y := sphericalLaplace_pos hM y
  have hL0 : 0<L := zero_lt_one.trans_le hL
  rw [show 1-(1-min (sphericalLaplace M y) L/L)=min (sphericalLaplace M y) L/L by ring,
    Real.log_div (lt_min hY hL0).ne' hL0.ne']
  congr 1
  by_cases h : sphericalLaplace M y≤L
  · rw [min_eq_left h,min_eq_left (Real.log_le_log hY h)]
  · have h' := le_of_not_ge h
    rw [min_eq_right h',min_eq_right (Real.log_le_log hL0 h')]

theorem rootLog_spherical_deficit_eq_clipped_logSteps (hM : 0<M) (depth : ℕ)
    (x : Fin (depth+1)→ℝ) (T : Fin (depth+1)→Model.Vector M→L[ℝ]Model.Vector M)
    (hx : ∀j,0<x j) {L : ℝ} (hL : 1≤L) (z : Model.Vector M) :
    rootLog depth x T (fun y => 1-min (sphericalLaplace M y) L/L) 1 z=
      gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j)))
        (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)) z-Real.log L := by
  have hZ : Measurable (fun y : Model.Vector M => 1-min (sphericalLaplace M y) L/L) :=
    measurable_const.sub (((sphericalLaplace_measurable M).min measurable_const).div_const L)
  have ha := (spherical_deficit_bounds hM hL (0 : Model.Vector M)).2.2
  have hb (y : Model.Vector M) := spherical_deficit_bounds hM hL y
  rw [rootLog_eq_logSteps depth x T hZ ha.1 ha.2 (fun y => ⟨(hb y).1,(hb y).2.1⟩) hx z]
  have HE : (fun y : Model.Vector M => Real.log (1-(1-min (sphericalLaplace M y) L/L)))=
      (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)+(-Real.log L)) := by
    funext y
    simpa only [sub_eq_add_neg] using spherical_log_deficit_eq hM hL y
  rw [HE,gaussianLogSteps_add_const ((log_sphericalLaplace_lipschitz hM).min_const (Real.log L))]
  rfl

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianSphericalClipping
