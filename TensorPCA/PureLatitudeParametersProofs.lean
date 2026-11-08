-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.RetainedCountProofs.SphericalLatitudeScorePrecision
public import TensorPCA.VariationalProofs

/-! Finite pure-latitude variance parameters at unit center
scale. The RS inequality uses the slice-polynomial criterion; no physical ground-state statement is assumed. -/
@[expose] public section
namespace TensorPCA.PureLatitudeParametersProofs
noncomputable section
open Set RetainedCountProofs SphericalModel SphericalGaussianJet SphericalLatitudeChartKacRice
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma pure_latitudeDerivativeVariance (k : ℕ) (hk : 2≤k) (q : ℝ) :
    latitudeDerivativeVariance
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1) q =
        (k : ℝ)*(1-q^2) := by
  rw [latitudeDerivativeVariance,firstCovariance_center,firstCovariance_mixture]
  simp [FiniteMixture.xi1,FiniteMixture.pure,mul_comm]

lemma pure_latitudeCurvatureVariance (k : ℕ) (hk : 2≤k) (q : ℝ) :
    latitudeCurvatureVariance
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1) q =
        (k : ℝ)*((k : ℝ)-1)*(1-q^2)^2 := by
  rw [latitudeCurvatureVariance,secondCovariance_center,secondCovariance_mixture]
  simp [FiniteMixture.xi2,FiniteMixture.curvatureCoeff,FiniteMixture.pure,
    Nat.cast_sub (show 1≤k by omega)]
  ring

/-- The exact reviewed RS overlap cutoff gives the actual source b<=a,
including its boundary and both signed endpoints. -/
theorem pure_latitude_RS_criterion (k : ℕ) (hk : 3≤k) {q : ℝ}
    (hq : q ∈ Icc (-1 : ℝ) 1)
    (hlarge : Real.sqrt (1-1/((k : ℝ)-1))≤|q|) :
    latitudeCurvatureVariance
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k (by omega) 1 zero_lt_one)) 1) q ≤
    latitudeDerivativeVariance
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k (by omega) 1 zero_lt_one)) 1) q := by
  rw [pure_latitudeCurvatureVariance,pure_latitudeDerivativeVariance]
  simpa only [VariationalProofs.secondDeriv_xiSlice_one (by omega : 1≤k),
    VariationalProofs.deriv_xiSlice_one] using VariationalProofs.xiSlice_rs_criterion hk hq hlarge

end
end TensorPCA.PureLatitudeParametersProofs
