-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepSmallMass
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitzOrder

/-! A finite literal list of Gaussian log steps, with a quantitative bound
when selected nonnegative masses are replaced by zero. No hierarchy law or
positive lower bound on the masses is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianStepLipschitz OneStepGaussianStepLipschitzOrder
open OneStepGaussianStepSmallMass
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def gaussianLogSteps {N : ℕ} (steps : List (ℝ × (Model.Vector N →L[ℝ] E)))
    (F : E → ℝ) : E → ℝ :=
  steps.foldr (fun step H ↦ gaussianLogStep step.2 step.1 H) F

theorem gaussianLogSteps_lipschitz {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (steps : List (ℝ × (Model.Vector N →L[ℝ] E))) :
    LipschitzWith L (gaussianLogSteps steps F) := by
  induction steps with
  | nil => exact hF
  | cons a steps ih => exact gaussianLogStep_lipschitz ih a.2 a.1

theorem gaussianLogSteps_compress_bounds {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (steps : List (ℝ × (Model.Vector N →L[ℝ] E)))
    (select : ℝ × (Model.Vector N →L[ℝ] E) → Bool)
    (hmass : ∀a∈steps,0≤a.1) (x : E) :
    0≤gaussianLogSteps steps F x-
      gaussianLogSteps (steps.map (fun a ↦ (if select a then 0 else a.1,a.2))) F x ∧
    gaussianLogSteps steps F x-
      gaussianLogSteps (steps.map (fun a ↦ (if select a then 0 else a.1,a.2))) F x≤
        (steps.map (fun a ↦ if select a then a.1*(L : ℝ)^2*‖a.2‖^2/2 else 0)).sum := by
  revert hmass x
  induction steps with
  | nil => intro hmass x; simp [gaussianLogSteps]
  | cons a steps ih =>
    intro hmass x
    have hm : 0≤a.1 := hmass a (by simp)
    have htail : ∀b∈steps,0≤b.1 := fun b hb ↦ hmass b (by simp [hb])
    let original := gaussianLogSteps steps F
    let compressed := gaussianLogSteps
      (steps.map (fun b ↦ (if select b then 0 else b.1,b.2))) F
    let cost := (steps.map (fun b ↦ if select b then b.1*(L : ℝ)^2*‖b.2‖^2/2 else 0)).sum
    have ho : LipschitzWith L original := gaussianLogSteps_lipschitz hF steps
    have hc : LipschitzWith L compressed := gaussianLogSteps_lipschitz hF _
    have hI : ∀y,0≤original y-compressed y ∧ original y-compressed y≤cost := ih htail
    change 0≤gaussianLogStep a.2 a.1 original x-
        gaussianLogStep a.2 (if select a then 0 else a.1) compressed x ∧
      gaussianLogStep a.2 a.1 original x-
        gaussianLogStep a.2 (if select a then 0 else a.1) compressed x≤
        (if select a then a.1*(L : ℝ)^2*‖a.2‖^2/2 else 0)+cost
    by_cases hs : select a=true
    · simp only [hs,↓reduceIte]
      have hSmall := gaussianLogStep_sub_zero_bounds ho a.2 hm x
      have hMono := gaussianLogStep_mono hc ho a.2 (show (0 : ℝ)≤0 from le_rfl)
        (fun y ↦ sub_nonneg.mp (hI y).1) x
      have hStable := gaussianLogStep_sub_le ho hc a.2 (show (0 : ℝ)≤0 from le_rfl)
        (fun y ↦ (hI y).2) x
      constructor <;> linarith
    · simp only [hs,Bool.false_eq_true,↓reduceIte,zero_add]
      have hMono := gaussianLogStep_mono hc ho a.2 hm
        (fun y ↦ sub_nonneg.mp (hI y).1) x
      have hStable := gaussianLogStep_sub_le ho hc a.2 hm (fun y ↦ (hI y).2) x
      exact ⟨sub_nonneg.mpr hMono,hStable⟩

theorem gaussianLogSteps_compress_small_bounds {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (steps : List (ℝ × (Model.Vector N →L[ℝ] E)))
    (select : ℝ × (Model.Vector N →L[ℝ] E) → Bool)
    (hmass : ∀a∈steps,0≤a.1) {delta : ℝ} (hdelta : 0≤delta)
    (hselect : ∀a∈steps,select a=true → a.1≤delta) (x : E) :
    0≤gaussianLogSteps steps F x-
      gaussianLogSteps (steps.map (fun a ↦ (if select a then 0 else a.1,a.2))) F x ∧
    gaussianLogSteps steps F x-
      gaussianLogSteps (steps.map (fun a ↦ (if select a then 0 else a.1,a.2))) F x≤
        delta*(L : ℝ)^2*(steps.map (fun a ↦ ‖a.2‖^2)).sum/2 := by
  have H := gaussianLogSteps_compress_bounds hF steps select hmass x
  refine ⟨H.1,H.2.trans ?_⟩
  have hs : (steps.map (fun a ↦ if select a then a.1*(L : ℝ)^2*‖a.2‖^2/2 else 0)).sum≤
      (steps.map (fun a ↦ delta*(L : ℝ)^2*‖a.2‖^2/2)).sum := by
    apply List.sum_le_sum
    intro a ha
    by_cases hsel : select a=true
    · simp only [hsel,↓reduceIte]
      gcongr
      exact hselect a ha hsel
    · simp only [hsel,Bool.false_eq_true,↓reduceIte]
      positivity
  have heq : (steps.map (fun a ↦ delta*(L : ℝ)^2*‖a.2‖^2/2)).sum=
      delta*(L : ℝ)^2*(steps.map (fun a ↦ ‖a.2‖^2)).sum/2 := by
    clear H hs hmass hselect
    induction steps with
    | nil => simp
    | cons a steps ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      ring
  exact hs.trans_eq heq

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression
