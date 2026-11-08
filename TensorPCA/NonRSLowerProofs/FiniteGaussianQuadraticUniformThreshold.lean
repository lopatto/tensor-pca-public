-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformError
public import Mathlib.Analysis.SpecificLimits.Basic

/-! One cavity-dimension threshold works uniformly over all finite ordered-chain
parameters. Its hypotheses are scalar coefficient bounds; shell probabilities are
estimated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformThreshold
open MeasureTheory ProbabilityTheory Filter
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticLogSteps
open FiniteGaussianQuadraticSphericalStages FiniteGaussianQuadraticUniformError
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem uniform_sphericalStage_threshold {Bmax delta Cmax Amax error : ℝ}
    (hBmax : 0≤ Bmax) (hdelta : 0< delta) (herror : 0< error) :
    ∀ᶠ M : ℕ in atTop,∀(d : ℕ) (x Delta : Fin d→ℝ) (B y0 : ℝ),
      (∀j,0< x j)→Monotone x→(∀j,x j≤1)→(∀j,0≤ Delta j)→
      tail (fun j => x j*Delta j) 0< B→0≤ y0→
      y0/(precision x Delta B 0)^2+
        (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B→
      B≤Bmax→delta≤stageMass x 0→|profileConstant 1 x Delta B 0|≤Cmax→
      y0/(2*precision x Delta B 0)≤Amax→
      profileConstant 1 x Delta B 0+y0/(2*precision x Delta B 0)+(B-1)/2-error≤
        ∫g : Model.Vector M,sphericalStage M x Delta 0 (Real.sqrt y0 •g)/(M : ℝ)
          ∂stdGaussian (Model.Vector M) := by
  let D := 3*(Bmax+1)/2
  have hD : 0< D := by dsimp only [D]; linarith only [hBmax]
  let eps := error/(2*D)
  have heps : 0< eps := div_pos herror (mul_pos (by norm_num) hD)
  let R := Cmax+(Bmax+1)*(1+2*eps)+Real.log 2/delta
  let L := Real.sqrt (2*R^2+6*Amax^2)
  let Q := 8*Bmax^4+8/eps^2
  have hFirst : Tendsto (fun M : ℕ => Real.log 2/((M : ℝ)*delta)) atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (Real.log 2/delta) using 1
    funext M
    ring
  have hSecond : Tendsto (fun M : ℕ => L*Real.sqrt (Q/(M : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := L)).mul
        ((Real.continuous_sqrt.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat Q))
  have hTotal : Tendsto (fun M : ℕ => Real.log 2/((M : ℝ)*delta)+L*Real.sqrt (Q/(M : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by simpa only [zero_add] using hFirst.add hSecond
  have hSmall := (tendsto_order.1 hTotal).2 (error/2) (half_pos herror)
  filter_upwards [hSmall,eventually_ge_atTop (1 : ℕ)] with M hSmall hM
  intro d x Delta B y0 hx hMono hx1 hDelta hB hy hroot hMax hMass hCmax hAmax
  have hMpos : 0< M := Nat.lt_of_lt_of_le (by decide) hM
  have HP := expected_sphericalStage_uniform_error hMpos hx hMono hx1 hDelta hB hy hroot
    hMax hdelta hMass heps hCmax hAmax
  change profileConstant 1 x Delta B 0+y0/(2*precision x Delta B 0)+(B-1)/2-
    eps*D-Real.log 2/((M : ℝ)*delta)-L*Real.sqrt (Q/(M : ℝ))≤_ at HP
  have hShell : eps*D=error/2 := by dsimp only [eps]; field_simp
  rw [hShell] at HP
  linarith only [HP,hSmall]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformThreshold
