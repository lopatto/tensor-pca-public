-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticCompactParameters
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticCoefficientBounds

/-! One cavity-dimension threshold works uniformly over all finite depths and hierarchy
parameters in the spherical endpoint bound. Coefficient and Gaussian shell estimates
supply the threshold.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformEndpoint
open MeasureTheory ProbabilityTheory Filter
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticSphericalStages
open FiniteGaussianQuadraticUniformError FiniteGaussianQuadraticUniformThreshold
open FiniteGaussianQuadraticCompactParameters FiniteGaussianQuadraticCoefficientBounds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem uniform_spherical_endpoint {ymin Y delta error : ℝ}
    (hymin : 0< ymin) (hdelta : 0< delta) (hdelta1 : delta≤1) (herror : 0< error) :
    ∀ᶠ M : ℕ in atTop,∀(d : ℕ) (x Delta : Fin d→ℝ) (B y0 : ℝ),
      (∀j,delta≤x j)→Monotone x→(∀j,x j≤1)→(∀j,0≤ Delta j)→
      tail (fun j => x j*Delta j) 0< B→ymin≤y0→y0+∑j : Fin d,Delta j≤Y→
      y0/(precision x Delta B 0)^2+
        (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B→
      depthCost x Delta y0 B/2-error≤
        ∫g : Model.Vector M,sphericalStage M x Delta 0 (Real.sqrt y0 •g)/(M : ℝ)
          ∂stdGaussian (Model.Vector M) := by
  let Ybar := max Y 0
  let Bmax := 2+3*Ybar
  let Dmin := Real.sqrt ymin
  let Cmax := Real.log Bmax/2+Ybar/(2*Dmin)
  let Amax := Ybar/(2*Dmin)
  have hYbar : 0≤Ybar := le_max_right Y 0
  have hBmax : 0≤Bmax := by dsimp only [Bmax]; linarith only [hYbar]
  have hDmin : 0< Dmin := Real.sqrt_pos.mpr hymin
  have HT := uniform_sphericalStage_threshold (Bmax := Bmax) (Cmax := Cmax) (Amax := Amax)
    hBmax hdelta herror
  filter_upwards [HT] with M HM
  intro d x Delta B y0 hxLower hMono hx1 hDelta hB hyLower hY hroot
  have hx : ∀j,0< x j := fun j => hdelta.trans_le (hxLower j)
  obtain ⟨hy,hY0,hB1,hBupper,hDlower,hSum,hYupper⟩ :=
    root_compact_bounds hx hx1 hDelta hB hymin hyLower hY hroot
  have hMax : B≤Bmax := by
    have H : Y≤Ybar := le_max_left Y 0
    dsimp only [Bmax]
    linarith only [hBupper,H]
  have hMass : delta≤stageMass x 0 := stageMass_lower hdelta1 hxLower 0
  have hCoeff : |FiniteGaussianQuadraticLogSteps.profileConstant 1 x Delta B 0|≤Cmax :=
    abs_profileConstant_one_le hx hDelta hB hDmin hDlower hB1 hMax
      (hSum.trans (le_max_left Y 0))
  have hSlope : y0/(2*precision x Delta B 0)≤Amax :=
    (quadraticRootSlope_mem_Icc x Delta B hDmin hDlower hy
      (hYupper.trans (le_max_left Y 0))).2
  have HP := HM d x Delta B y0 hx hMono hx1 hDelta hB hy hroot hMax hMass hCoeff hSlope
  rw [gaussian_root_value_eq_half_depthCost hx hDelta hB y0] at HP
  exact HP

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformEndpoint
