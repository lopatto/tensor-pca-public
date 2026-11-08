-- SPDX-License-Identifier: Apache-2.0
/- Attributed exact finite physical-intensity normalization source from
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/SphericalLatitudeIntensityBounds.lean. The actual score
   denominator and finite intensity identity are retained verbatim. The sharp
   GOE leading bound and radial-tail inequalities remain genuine separate
   obligations; no such bound is assumed here. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SphericalLatitudePhysicalIntensity
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet GOEPhysicalPotential
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def latitudeScoreDenominator {P : ℕ} (c : Degree P → ℝ) (q : ℝ) : ℝ :=
  2*Real.pi*Real.sqrt (latitudeScoreCovariance c q).det

theorem center_latitudeScoreDenominator_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) :
    0 < latitudeScoreDenominator (centerCoefficients (mixtureCoefficients μ) Q) q := by
  unfold latitudeScoreDenominator
  exact mul_pos (by positivity) (Real.sqrt_pos.mpr (center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1))

theorem physicalMean_nonneg (n N : ℕ) (b k : ℝ) : 0 ≤ physicalMean n N b k :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem latitudePhysicalIntensity_eq_ofReal (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) (h k : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let b := latitudeCurvatureVariance c q
    let v := latitudeConditionalValueVariance c q
    latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) =
      ENNReal.ofReal (latitudeGeometricFactor n a *
        (((n+3 : ℕ) : ℝ)/latitudeScoreDenominator c q)*
          Real.exp (-((n+3 : ℕ) : ℝ)/2*(k^2/(a+b)+(h-a*k/(a+b))^2/v))*
            physicalMean n (n+3) b k) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have ha := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hD := center_latitudeScoreDenominator_pos μ hQ hq0 hq1
  unfold latitudePhysicalIntensity latitudePhysicalScorePdf
  rw [center_latitude_score_precision μ hQ hq0 hq1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hg := (latitudeGeometricFactor_pos n ha).le
  rw [← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [latitudeScoreDenominator]
  ring


end
end TensorPCA.RetainedCountProofs.SphericalLatitudeChartKacRice
