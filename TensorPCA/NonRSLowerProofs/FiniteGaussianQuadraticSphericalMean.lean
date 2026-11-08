-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalLower
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticGoodRootMean

/-! A finite-dimensional averaged spherical endpoint lower bound. Every bad-root, shell,
probability-recursion and integrability input is proved.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalMean
open MeasureTheory ProbabilityTheory Set
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticStep FiniteGaussianQuadraticLogSteps
open FiniteGaussianQuadraticSphericalStages FiniteGaussianQuadraticSphericalLower
open FiniteGaussianQuadraticTerminalGood FiniteGaussianQuadraticRootEnvelope
open FiniteGaussianQuadraticGoodRootMean OneStepGaussianStepLipschitz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem expected_sphericalStage_lower {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B y0 Bmax C eps : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (hMax : B≤Bmax) (hC : 0≤ C) (hCgap : Bmax^2< C^2) (heps : 0< eps) :
    let K := ((B-1)/2-eps*(C+|B-1|/2))-Real.log 2/((M : ℝ)*stageMass x 0)
    let c := profileConstant 1 x Delta B 0+K
    let a := y0/(2*precision x Delta B 0)
    let eta := 2*(4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2)+4/((M : ℝ)*eps^2))
    c+a-Real.sqrt (2*c^2+6*a^2)*Real.sqrt eta≤
      ∫g : Model.Vector M,sphericalStage M x Delta 0 (Real.sqrt y0 •g)/(M : ℝ)
        ∂stdGaussian (Model.Vector M) := by
  let K := ((B-1)/2-eps*(C+|B-1|/2))-Real.log 2/((M : ℝ)*stageMass x 0)
  let c := profileConstant 1 x Delta B 0+K
  let a := y0/(2*precision x Delta B 0)
  let eta := 2*(4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2)+4/((M : ℝ)*eps^2))
  let F := fun g : Model.Vector M => sphericalStage M x Delta 0 (Real.sqrt y0 •g)/(M : ℝ)
  let bad := {g : Model.Vector M |
    terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g)< (1 : ℝ)/2}
  change c+a-Real.sqrt (2*c^2+6*a^2)*Real.sqrt eta≤∫g,F g∂stdGaussian (Model.Vector M)
  have hFI : Integrable F (stdGaussian (Model.Vector M)) := by
    have H := (shifted_integrable (sphericalStage_lipschitz hM x Delta 0)
      (shift M y0) (0 : Model.Vector M)).div_const (M : ℝ)
    simpa only [F,zero_add,shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using H
  have hF0 (g : Model.Vector M) : 0≤F g :=
    div_nonneg (sphericalStage_nonneg hM (fun j => (hx j).le) 0 _) (Nat.cast_nonneg M)
  have hbad : MeasurableSet bad := measurableSet_lt
    ((terminalGoodProbability_measurable M hx hDelta hB C eps).comp (by fun_prop)) measurable_const
  have hmass : (stdGaussian (Model.Vector M)).real bad≤eta :=
    terminalGoodProbability_bad_root_mass hM hx hDelta hB hy hroot hMax hCgap heps
  apply goodRoot_mean_lower hM c a F hFI hF0 hbad hmass
  intro g hg
  have hgood : (1 : ℝ)/2≤terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g) := by
    change ¬terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g)< (1 : ℝ)/2 at hg
    exact le_of_not_gt hg
  have HG := normalized_spherical_root_lower_of_good hM hx hMono hx1 hDelta hB hC heps.le _ hgood
  have HE : c+a*‖g‖^2/(M : ℝ)=envelope M x Delta B 0 (Real.sqrt y0 •g)/(M : ℝ)+K := by
    exact (normalized_root_eq hM x Delta B hy K g).symm
  rw [HE]
  dsimp only [F,K]
  linarith only [HG]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalMean
