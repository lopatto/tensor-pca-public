-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalShell
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticLogSteps
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphereLogStepsCompression
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltOuter

/-! Spherical suffix log steps: recursion, Lipschitz growth, exponential integrability
and nonnegativity.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalStages
open MeasureTheory ProbabilityTheory
open FiniteGaussianLogStepsCompression FiniteGaussianSphereLogStepsCompression
open FiniteGaussianQuadraticStep FiniteGaussianQuadraticLogSteps
open OneStepGaussianStepLipschitz OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sphericalStage {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) (i : ℕ) : Model.Vector M→ℝ :=
  gaussianLogSteps ((quadraticSteps M x Delta).drop i) (fun h => Real.log (sphericalLaplace M h))

def stageMass {d : ℕ} (x : Fin d→ℝ) (i : ℕ) : ℝ :=
  if hi : i< d then x ⟨i,hi⟩ else 1

theorem stageMass_terminal {d : ℕ} (x : Fin d→ℝ) : stageMass x d=1 := by simp [stageMass]

theorem stageMass_self {d : ℕ} (x : Fin d→ℝ) (j : Fin d) : stageMass x j=x j := by
  simp only [stageMass,dif_pos j.isLt]

theorem stageMass_pos {d : ℕ} {x : Fin d→ℝ} (hx : ∀j,0< x j) (i : ℕ) : 0< stageMass x i := by
  unfold stageMass
  split_ifs
  · exact hx _
  · norm_num

theorem stageMass_next_ge {d : ℕ} {x : Fin d→ℝ}
    (hMono : Monotone x) (hx1 : ∀j,x j≤1) (j : Fin d) : x j≤stageMass x ((j : ℕ)+1) := by
  unfold stageMass
  split_ifs with h
  · exact hMono (show j≤(⟨(j : ℕ)+1,h⟩ : Fin d) by change (j : ℕ)≤(j : ℕ)+1; omega)
  · exact hx1 j

theorem sphericalStage_terminal {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) :
    sphericalStage M x Delta d=(fun h => Real.log (sphericalLaplace M h)) := by
  have H : (quadraticSteps M x Delta).drop d=[] := List.drop_eq_nil_of_le (by simp [quadraticSteps])
  rw [sphericalStage,H]
  rfl

theorem sphericalStage_step {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ) (j : Fin d) :
    sphericalStage M x Delta j=
      gaussianLogStep (shift M (Delta j)) (x j) (sphericalStage M x Delta ((j : ℕ)+1)) := by
  have hj : (j : ℕ)< (quadraticSteps M x Delta).length := by simpa [quadraticSteps] using j.isLt
  rw [sphericalStage,List.drop_eq_getElem_cons hj]
  change gaussianLogStep ((quadraticSteps M x Delta)[(j : ℕ)]).2 ((quadraticSteps M x Delta)[(j : ℕ)]).1
    (sphericalStage M x Delta ((j : ℕ)+1))=_
  simp only [quadraticSteps,List.getElem_ofFn]

theorem sphericalStage_lipschitz {d M : ℕ} (hM : 0< M) (x Delta : Fin d→ℝ) (i : ℕ) :
    LipschitzWith (Real.sqrt (M : ℝ)).toNNReal (sphericalStage M x Delta i) :=
  gaussianLogSteps_lipschitz (log_sphericalLaplace_lipschitz hM) _

theorem sphericalStage_exp_integrable {d M : ℕ} (hM : 0< M) (x Delta : Fin d→ℝ)
    (i : ℕ) (T : Model.Vector M→L[ℝ] Model.Vector M) (mass : ℝ) (h : Model.Vector M) :
    Integrable (fun g : Model.Vector M => Real.exp (mass*sphericalStage M x Delta i (h+T g)))
      (stdGaussian (Model.Vector M)) :=
  shifted_exp_integrable (sphericalStage_lipschitz hM x Delta i) T mass h

theorem gaussianLogStep_nonneg {M : ℕ} {L : ℝ≥0} {F : Model.Vector M→ℝ}
    (hF : LipschitzWith L F) (hF0 : ∀h,0≤F h) (T : Model.Vector M→L[ℝ] Model.Vector M)
    {mass : ℝ} (hm : 0≤ mass) (h : Model.Vector M) : 0≤gaussianLogStep T mass F h := by
  by_cases hz : mass=0
  · simp only [gaussianLogStep,if_pos hz]
    exact integral_nonneg (fun g => hF0 _)
  · have hZ : 1≤gaussianNormalizer T mass F h := by
      have H := integral_mono (integrable_const (1 : ℝ)) (shifted_exp_integrable hF T mass h)
        (fun g => Real.one_le_exp (mul_nonneg hm (hF0 _)))
      simpa only [gaussianNormalizer,integral_const,probReal_univ,one_smul] using H
    simp only [gaussianLogStep,if_neg hz]
    exact div_nonneg (Real.log_nonneg hZ) hm

theorem gaussianLogSteps_nonneg {M : ℕ} {L : ℝ≥0} {F : Model.Vector M→ℝ}
    (hF : LipschitzWith L F) (hF0 : ∀h,0≤F h)
    (steps : List (ℝ×(Model.Vector M→L[ℝ] Model.Vector M)))
    (hm : ∀a∈steps,0≤a.1) (h : Model.Vector M) : 0≤gaussianLogSteps steps F h := by
  induction steps generalizing h with
  | nil => exact hF0 h
  | cons a steps ih =>
    have H (z : Model.Vector M) := ih (fun b hb => hm b (by simp [hb])) z
    exact gaussianLogStep_nonneg (gaussianLogSteps_lipschitz hF steps) H a.2 (hm a (by simp)) h

theorem sphericalStage_nonneg {d M : ℕ} (hM : 0< M) {x Delta : Fin d→ℝ}
    (hx : ∀j,0≤ x j) (i : ℕ) (h : Model.Vector M) : 0≤sphericalStage M x Delta i h := by
  apply gaussianLogSteps_nonneg (log_sphericalLaplace_lipschitz hM)
    (fun z => Real.log_nonneg (one_le_sphericalLaplace hM z))
  intro a ha
  have HM := List.mem_of_mem_drop ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp HM
  exact hx j

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalStages
