-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedValues
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression

/-! Identification with the Gaussian log-step tower `gaussianLogSteps`. The bounded
positive terminal ensures positivity of every normalizer.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedLogSteps
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedTransforms FiniteNestedGaussianMarkedIntegralStep
open FiniteGaussianLogStepsCompression OneStepGaussianStepLipschitz
noncomputable section
variable {M : ℕ}

theorem parentPower_eq_exp_logSteps (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→Model.Vector M→L[ℝ]Model.Vector M) {Z : Model.Vector M→ℝ}
    (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (hp : 0≤p) (hx : ∀j,0<x j) (z : Model.Vector M) :
    parentPower depth x p T Z 1 z=
      Real.exp (p*gaussianLogSteps (List.ofFn (fun j : Fin depth => (x j,T j))) (fun y => Real.log (1-Z y)) z) := by
  induction depth generalizing p z with
  | zero =>
    have hbase : 0<1-Z z := by linarith [(hb z).2]
    simp only [parentPower,List.ofFn_zero,gaussianLogSteps,List.foldr_nil,one_mul]
    rw [Real.rpow_def_of_pos hbase]
    congr 1
    ring
  | succ depth ih =>
    have HC (y : Model.Vector M) := ih (fun j => x j.succ) (x 0) (fun j => T j.succ)
      (hx 0).le (fun j => hx j.succ) y
    have hta : |(1 : ℝ)| *a<1 := by simpa only [abs_one,one_mul] using ha1
    have hpos := integral_child_pos depth (fun j => x j.succ) (x 0) (fun j => T j.succ)
      hZ ha hb (hx 0).le (fun j => hx j.succ) hta (T 0) z
    simp_rw [HC] at hpos
    change (∫g : Model.Vector M,parentPower depth (fun j => x j.succ) (x 0)
      (fun j => T j.succ) Z 1 (z+T 0 g) ∂stdGaussian (Model.Vector M))^(p/x 0)=_
    simp_rw [HC]
    rw [List.ofFn_succ]
    change _=Real.exp (p*gaussianLogStep (T 0) (x 0)
      (gaussianLogSteps (List.ofFn (fun j : Fin depth => (x j.succ,T j.succ))) (fun y => Real.log (1-Z y))) z)
    rw [gaussianLogStep,if_neg (ne_of_gt (hx 0))]
    unfold gaussianNormalizer
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    ring

theorem rootLog_eq_logSteps (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (T : Fin (depth+1)→Model.Vector M→L[ℝ]Model.Vector M) {Z : Model.Vector M→ℝ}
    (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (hx : ∀j,0<x j) (z : Model.Vector M) :
    rootLog depth x T Z 1 z=
      gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x j,T j))) (fun y => Real.log (1-Z y)) z := by
  rw [List.ofFn_succ]
  change Real.log (∫g : Model.Vector M,parentPower depth (fun j => x j.succ) (x 0)
    (fun j => T j.succ) Z 1 (z+T 0 g) ∂stdGaussian (Model.Vector M))/(x 0)=
      gaussianLogStep (T 0) (x 0)
        (gaussianLogSteps (List.ofFn (fun j : Fin depth => (x j.succ,T j.succ))) (fun y => Real.log (1-Z y))) z
  rw [gaussianLogStep,if_neg (ne_of_gt (hx 0))]
  unfold gaussianNormalizer
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ (fun g => parentPower_eq_exp_logSteps depth (fun j => x j.succ) (x 0)
    (fun j => T j.succ) hZ ha ha1 hb (hx 0).le (fun j => hx j.succ) (z+T 0 g))

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedLogSteps
