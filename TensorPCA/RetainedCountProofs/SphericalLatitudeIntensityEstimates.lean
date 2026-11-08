-- SPDX-License-Identifier: Apache-2.0
/- Attributed actual affine-latitude estimate source from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/SphericalLatitudeIntensityBounds.lean (estimate tail).
   Actual intensities and proof bodies retained; actual sharp and crude
   matrix-mean estimates are proved imports. The accepted finite density
   prefix is imported unchanged. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SphericalLatitudeIntensityBounds
public import TensorPCA.RetainedCountProofs.GOEFirstMeanTheorems
public import TensorPCA.RetainedCountProofs.GOECrudeDeterminant
public import TensorPCA.RetainedCountProofs.StrongFieldComplexity
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet GOEPhysicalPotential StrongFieldComplexity
open SemicirclePotential GaussianCrudeDeterminant
open scoped ENNReal Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudePhysicalIntensity_eventually_compact_upper
    (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let b := latitudeCurvatureVariance c q
    let v := latitudeConditionalValueVariance c q
    ∃ B : ℝ, 0 < B ∧ ∀ {Z ε : ℝ}, 0 ≤ Z → 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ h k : ℝ, |k| ≤ Z →
        latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) ≤
          ENNReal.ofReal (B*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*(exponent a b v h k+ε))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let v := latitudeConditionalValueVariance c q
  let D := latitudeScoreDenominator c q
  have ha : 0 < a := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hb : 0 < b := center_latitudeCurvatureVariance_pos μ hQ hq1
  have hD : 0 < D := center_latitudeScoreDenominator_pos μ hQ hq0 hq1
  obtain ⟨C,hC,hgeo⟩ := latitudeGeometricFactor_upper ha
  refine ⟨C/D*Real.exp (1+|Real.log b|), by positivity, ?_⟩
  intro Z ε hZ hε
  filter_upwards [GOEFirstMeanTheorems.physical_mean_leading_upper_uniform 2 hb hZ hε] with n hn
  intro h k hk
  rw [latitudePhysicalIntensity_eq_ofReal n μ hQ hq0 hq1 h k]
  apply ENNReal.ofReal_le_ofReal
  change latitudeGeometricFactor n a*((n+3 : ℕ)/D)*
    Real.exp (-((n+3 : ℕ) : ℝ)/2*(k^2/(a+b)+(h-a*k/(a+b))^2/v))*physicalMean n (n+3) b k ≤ _
  have hG : 0 ≤ C*Real.exp (((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)) := by positivity
  have hN : 0 ≤ ((n+3 : ℕ) : ℝ)/D := by positivity
  let E := -((n+3 : ℕ) : ℝ)/2*(k^2/(a+b)+(h-a*k/(a+b))^2/v)
  have hP := mul_le_mul (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hgeo n) hN) (Real.exp_pos E).le)
    (hn k hk) (physicalMean_nonneg _ _ _ _) (mul_nonneg (mul_nonneg hG hN) (Real.exp_pos E).le)
  apply hP.trans_eq
  have hexp : ((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)+E+
      (((n+3 : ℕ) : ℝ)*(Real.log b/2+potential (k/Real.sqrt b)+ε)+2*(1+|Real.log b|)/2) =
        ((n+3 : ℕ) : ℝ)*(exponent a b v h k+ε)+(1+|Real.log b|) := by
    dsimp only [E]
    rw [exponent, Real.log_div hb.ne' ha.ne']
    simp only [div_mul_eq_div_div]
    ring
  calc
    _ = (C/D*((n+3 : ℕ) : ℝ))*Real.exp
        (((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)+E+
          (((n+3 : ℕ) : ℝ)*(Real.log b/2+potential (k/Real.sqrt b)+ε)+2*(1+|Real.log b|)/2)) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by
      rw [hexp, Real.exp_add]
      ring

/-- Every radial shift is controlled by the true crude GOE determinant
bound together with both Gaussian score penalties. -/
theorem latitudePhysicalIntensity_crude_upper (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let b := latitudeCurvatureVariance c q
    let v := latitudeConditionalValueVariance c q
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (h k : ℝ),
      latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) ≤
        ENNReal.ofReal (B*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*
          ((1-Real.log a)/2+crudeConstant b+|k|-k^2/(2*(a+b))-(h-a*k/(a+b))^2/(2*v)))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let v := latitudeConditionalValueVariance c q
  let D := latitudeScoreDenominator c q
  have ha : 0 < a := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hb : 0 < b := center_latitudeCurvatureVariance_pos μ hQ hq1
  have hD : 0 < D := center_latitudeScoreDenominator_pos μ hQ hq0 hq1
  obtain ⟨C,hC,hgeo⟩ := latitudeGeometricFactor_upper ha
  refine ⟨C/D, by positivity, ?_⟩
  intro n h k
  rw [latitudePhysicalIntensity_eq_ofReal n μ hQ hq0 hq1 h k]
  apply ENNReal.ofReal_le_ofReal
  change latitudeGeometricFactor n a*((n+3 : ℕ)/D)*
    Real.exp (-((n+3 : ℕ) : ℝ)/2*(k^2/(a+b)+(h-a*k/(a+b))^2/v))*physicalMean n (n+3) b k ≤ _
  let E := -((n+3 : ℕ) : ℝ)/2*(k^2/(a+b)+(h-a*k/(a+b))^2/v)
  have hG : 0 ≤ C*Real.exp (((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)) := by positivity
  have hN : 0 ≤ ((n+3 : ℕ) : ℝ)/D := by positivity
  have hP := mul_le_mul (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hgeo n) hN) (Real.exp_pos E).le)
    (GOECrudeDeterminant.physical_crude_mean n (n+3) (by omega) hb k).2
    (physicalMean_nonneg _ _ _ _) (mul_nonneg (mul_nonneg hG hN) (Real.exp_pos E).le)
  apply hP.trans_eq
  have hexp : ((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)+E+
      ((n+3 : ℕ) : ℝ)*(crudeConstant b+|k|) =
        ((n+3 : ℕ) : ℝ)*((1-Real.log a)/2+crudeConstant b+|k|-k^2/(2*(a+b))-(h-a*k/(a+b))^2/(2*v)) := by
    dsimp only [E]
    simp only [div_mul_eq_div_div]
    ring
  calc
    _ = (C/D*((n+3 : ℕ) : ℝ))*Real.exp
        (((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)+E+((n+3 : ℕ) : ℝ)*(crudeConstant b+|k|)) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by rw [hexp]

end
end TensorPCA.RetainedCountProofs.SphericalLatitudeChartKacRice
