-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalMean

/-! Explicit dimension-uniform finite endpoint errors from bounded scalar
coefficients. Their depth-free analytic bounds are discharged separately. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformError
open MeasureTheory ProbabilityTheory Set
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticLogSteps
open FiniteGaussianQuadraticSpine FiniteGaussianQuadraticSphericalStages
open FiniteGaussianQuadraticSphericalMean
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem stageMass_lower {d : ℕ} {x : Fin d→ℝ} {delta : ℝ}
    (hdelta1 : delta≤1) (hx : ∀j,delta≤x j) (i : ℕ) : delta≤stageMass x i := by
  unfold stageMass
  split_ifs
  · exact hx _
  · exact hdelta1

theorem expected_sphericalStage_uniform_error {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B y0 Bmax delta eps Cmax Amax : ℝ}
    (hx : ∀j,0< x j) (hMono : Monotone x) (hx1 : ∀j,x j≤1)
    (hDelta : ∀j,0≤ Delta j) (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (hMax : B≤Bmax) (hdelta : 0< delta) (hMass : delta≤stageMass x 0) (heps : 0< eps)
    (hCmax : |profileConstant 1 x Delta B 0|≤Cmax)
    (hAmax : y0/(2*precision x Delta B 0)≤Amax) :
    let R := Cmax+(Bmax+1)*(1+2*eps)+Real.log 2/delta
    let L := Real.sqrt (2*R^2+6*Amax^2)
    let Q := 8*Bmax^4+8/eps^2
    profileConstant 1 x Delta B 0+y0/(2*precision x Delta B 0)+(B-1)/2-
      eps*(3*(Bmax+1)/2)-Real.log 2/((M : ℝ)*delta)-L*Real.sqrt (Q/(M : ℝ))≤
      ∫g : Model.Vector M,sphericalStage M x Delta 0 (Real.sqrt y0 •g)/(M : ℝ)
        ∂stdGaussian (Model.Vector M) := by
  let C := Bmax+1
  let loss := Real.log 2/((M : ℝ)*stageMass x 0)
  let c := profileConstant 1 x Delta B 0+(((B-1)/2-eps*(C+|B-1|/2))-loss)
  let a := y0/(2*precision x Delta B 0)
  let eta := 2*(4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2)+4/((M : ℝ)*eps^2))
  let R := Cmax+(Bmax+1)*(1+2*eps)+Real.log 2/delta
  let L := Real.sqrt (2*R^2+6*Amax^2)
  let Q := 8*Bmax^4+8/eps^2
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hMone : (1 : ℝ)≤M := by exact_mod_cast hM
  have hBp := precision_B_pos hx hDelta hB
  have hBmax : 0≤Bmax := hBp.le.trans hMax
  have hC : 0≤ C := by dsimp only [C]; linarith only [hBmax]
  have hCgap : Bmax^2< C^2 := by dsimp only [C]; nlinarith only [hBmax]
  have hA0 : 0≤a := div_nonneg hy (mul_nonneg (by norm_num) (precision_pos hx hDelta hB 0).le)
  have hAmax0 : 0≤Amax := hA0.trans hAmax
  have hCmax0 : 0≤Cmax := (abs_nonneg _).trans hCmax
  have hMass0 : 0< stageMass x 0 := stageMass_pos hx 0
  have hLog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hLoss0 : 0≤loss := div_nonneg hLog (mul_pos hMr hMass0).le
  have hLoss : loss≤Real.log 2/((M : ℝ)*delta) :=
    div_le_div_of_nonneg_left hLog (mul_pos hMr hdelta) (mul_le_mul_of_nonneg_left hMass hMr.le)
  have hLossMax : loss≤Real.log 2/delta := by
    apply hLoss.trans
    apply div_le_div_of_nonneg_left hLog hdelta
    nlinarith only [hMone,hdelta]
  have hAbsB : |B-1|≤Bmax+1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hBp,hMax,hBmax]
  have hShell : eps*(C+|B-1|/2)≤eps*(3*(Bmax+1)/2) := by
    apply mul_le_mul_of_nonneg_left _ heps.le
    dsimp only [C]
    linarith only [hAbsB]
  have hcb : |c|≤R := by
    have HC := abs_le.mp hCmax
    have HB := abs_le.mp hAbsB
    have hShell0 : 0≤eps*(C+|B-1|/2) := mul_nonneg heps.le (by positivity)
    apply abs_le.mpr
    dsimp only [c,R]
    constructor <;> nlinarith only [HC.1,HC.2,HB.1,HB.2,hShell,hShell0,hLoss0,hLossMax,hBmax,heps]
  have hR0 : 0≤R := (abs_nonneg c).trans hcb
  have hCoeff : 2*c^2+6*a^2≤2*R^2+6*Amax^2 := by
    have HC := (sq_le_sq₀ (abs_nonneg c) hR0).mpr hcb
    rw [sq_abs] at HC
    have HA : a^2≤Amax^2 := (sq_le_sq₀ hA0 hAmax0).mpr hAmax
    linarith only [HC,HA]
  have hGap : 1≤(C^2-Bmax^2)^2 := by
    dsimp only [C]
    nlinarith only [hBmax,sq_nonneg Bmax]
  have hEta : eta≤Q/(M : ℝ) := by
    have HField : 4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2)≤4*Bmax^4/(M : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hMr (by nlinarith only [hGap,hMr])
    have HRewrite : (4*Bmax^4/(M : ℝ)+4/((M : ℝ)*eps^2))*2=Q/(M : ℝ) := by
      dsimp only [Q]
      field_simp
      <;> ring
    dsimp only [eta]
    nlinarith only [HField,HRewrite]
  have hRootLoss : Real.sqrt (2*c^2+6*a^2)*Real.sqrt eta≤L*Real.sqrt (Q/(M : ℝ)) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hCoeff) (Real.sqrt_le_sqrt hEta) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have HM := expected_sphericalStage_lower hM hx hMono hx1 hDelta hB hy hroot hMax hC hCgap heps
  change c+a-Real.sqrt (2*c^2+6*a^2)*Real.sqrt eta≤_ at HM
  change profileConstant 1 x Delta B 0+a+(B-1)/2-eps*(3*(Bmax+1)/2)-
    Real.log 2/((M : ℝ)*delta)-L*Real.sqrt (Q/(M : ℝ))≤_
  dsimp only [c] at HM
  linarith only [HM,hLoss,hShell,hRootLoss]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformError
