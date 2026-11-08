-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Exact one-point normalization uses SphericalGeometricPrefactorRates.lean
from pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e.
Only the indicated finite prefactor body is retained. The pure upper reduction
uses the actual one-point count intensity and explicit reviewed scalar rate;
no physical determinant asymptotic is postulated. Apache-2.0; see LICENSE. -/
module
public import TensorPCA.PureComplexityProofs
public import TensorPCA.RetainedCountProofs.SphericalScoreDensityRates

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.SphericalMarkedWindows
open SphericalModel SphericalGaussianJet WholeFieldRegression SphereChartVolume SphericalSequentialRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma sphereKRPrefactor_log (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    Real.log (sphereKRPrefactor (n+1) μ Q).toReal =
      Real.log (manuscriptRoundVolume (n+1) univ).toReal -
        (n+1 : ℝ)/2 * Real.log (2 * Real.pi * (Q * μ.xi1 Q)) := by
  have ha : 0 < 2 * Real.pi * (Q * μ.xi1 Q) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (mul_pos hQ (mixture_xi1_pos μ hQ))
  have hv := ENNReal.toReal_pos (manuscriptRoundVolume_mass_ne_zero (n+1))
    (manuscriptRoundVolume_mass_ne_top (n+1))
  rw [sphereKRPrefactor_physical (n+1) μ hQ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ha _).le,
    Real.log_mul hv.ne' (Real.rpow_pos_of_pos ha _).ne', Real.log_rpow ha]
  push_cast
  ring
end TensorPCA.RetainedCountProofs.SphericalMarkedWindows

namespace TensorPCA.PureIntensityUpperProofs
open RetainedCountProofs SphericalMarkedWindows SphericalModel SphericalGaussianJet GOEPhysicalPotential
open SphereChartVolume SphericalSequentialRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma unit_pure_xi1 (k : ℕ) (hk : 2 ≤ k) :
    (FiniteMixture.pure k hk 1 zero_lt_one).xi1 1 = k := by
  simp [FiniteMixture.xi1,FiniteMixture.pure]

lemma unit_pure_xi2 (k : ℕ) (hk : 2 ≤ k) :
    (FiniteMixture.pure k hk 1 zero_lt_one).xi2 1 = (k : ℝ)*((k : ℝ)-1) := by
  simp [FiniteMixture.xi2,FiniteMixture.curvatureCoeff,FiniteMixture.pure,
    Nat.cast_sub (show 1 ≤ k by omega)]

/-- The true pure intensity, with its ordinary determinant mean factored out. -/
lemma pureCriticalIntensity_toReal (n k : ℕ) (hk : 2 ≤ k) (e : ℝ) :
    (pureCriticalIntensity n k hk 1 zero_lt_one 1 e).toReal =
      (sphereKRPrefactor (n+1) (FiniteMixture.pure k hk 1 zero_lt_one) 1).toReal *
      (physicalValuePdf (n+2) (FiniteMixture.pure k hk 1 zero_lt_one) 1 e).toReal *
        physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) ((k : ℝ)*e) := by
  have hn : 0 ≤ physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) ((k : ℝ)*e) := by
    unfold physicalMean GOERawMoments.matrixAbsoluteDet
    exact integral_nonneg (fun _ => abs_nonneg _)
  simp only [pureCriticalIntensity,one_pow,one_mul,unit_pure_xi2,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hn]

/-- Exact logarithmic Gaussian/geometric part before any GOE estimate. -/
lemma pure_prefactor_value_log (n k : ℕ) (hk : 2 ≤ k) (e : ℝ) :
    Real.log ((sphereKRPrefactor (n+1) (FiniteMixture.pure k hk 1 zero_lt_one) 1).toReal *
      (physicalValuePdf (n+2) (FiniteMixture.pure k hk 1 zero_lt_one) 1 e).toReal) =
        Real.log (manuscriptRoundVolume (n+1) univ).toReal -
          (n+1 : ℝ)/2 * Real.log (2*Real.pi*(k : ℝ)) +
          (Real.log (n+2 : ℕ)-Real.log (2*Real.pi))/2 - (n+2 : ℕ)*e^2/2 := by
  have hp := ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1)
    (FiniteMixture.pure k hk 1 zero_lt_one) zero_lt_one)
    (sphereKRPrefactor_ne_top (n+1) (FiniteMixture.pure k hk 1 zero_lt_one) 1)
  have hd := physicalValuePdf_toReal_pos (n+2) (by omega)
    (FiniteMixture.pure k hk 1 zero_lt_one) zero_lt_one e
  rw [Real.log_mul hp.ne' hd.ne',sphereKRPrefactor_log n _ zero_lt_one,
    physicalValuePdf_log (n+2) (by omega) _ zero_lt_one e]
  simp only [unit_pure_xi1,FiniteMixture.pure_xi,one_pow,one_mul,mul_one]
  ring

lemma pure_prefactor_value_pos (n k : ℕ) (hk : 2 ≤ k) (e : ℝ) :
    0 < (sphereKRPrefactor (n+1) (FiniteMixture.pure k hk 1 zero_lt_one) 1).toReal *
      (physicalValuePdf (n+2) (FiniteMixture.pure k hk 1 zero_lt_one) 1 e).toReal := by
  apply mul_pos
  · exact ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1)
      (FiniteMixture.pure k hk 1 zero_lt_one) zero_lt_one)
      (sphereKRPrefactor_ne_top (n+1) (FiniteMixture.pure k hk 1 zero_lt_one) 1)
  · exact physicalValuePdf_toReal_pos (n+2) (by omega)
      (FiniteMixture.pure k hk 1 zero_lt_one) zero_lt_one e

/-- Exact cancellation of all physical Gaussian and spherical leading terms. -/
lemma pure_intensity_log_cancellation (n k : ℕ) (hk : 3 ≤ k) (e eps D : ℝ) :
    Real.log ((sphereKRPrefactor (n+1) (FiniteMixture.pure k (by omega) 1 zero_lt_one) 1).toReal *
      (physicalValuePdf (n+2) (FiniteMixture.pure k (by omega) 1 zero_lt_one) 1 e).toReal) +
      ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
        SemicirclePotential.potential ((k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D) =
      (n+2 : ℕ)*(PureComplexityProofs.pureComplexity k e+eps) +
        Real.log (n+2 : ℕ)/2+Real.log (k : ℝ)/2+D +
          (Real.log (manuscriptRoundVolume (n+1) univ).toReal-
            (n+2 : ℕ)*((1+Real.log (2*Real.pi))/2)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hk1 : 0 < (k : ℝ)-1 := by
    have h : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [pure_prefactor_value_log n k (by omega) e,
    Real.log_mul (mul_pos (by norm_num) Real.pi_pos).ne' hk0.ne',
    Real.log_mul hk0.ne' hk1.ne']
  unfold PureComplexityProofs.pureComplexity
  push_cast
  ring

/-- A genuine intermediate determinant estimate transfers to the literal
actual count intensity, with all finite normalization errors retained. -/
theorem pureCriticalIntensity_upper_of_detMean_upper (n k : ℕ) (hk : 3 ≤ k) (e eps D : ℝ)
    (hmean : physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) ((k : ℝ)*e) ≤
      Real.exp ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
        SemicirclePotential.potential ((k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D)) :
    (pureCriticalIntensity n k (by omega) 1 zero_lt_one 1 e).toReal ≤
      Real.exp ((n+2 : ℕ)*(PureComplexityProofs.pureComplexity k e+eps) +
        Real.log (n+2 : ℕ)/2+Real.log (k : ℝ)/2+D +
          (Real.log (manuscriptRoundVolume (n+1) univ).toReal-
            (n+2 : ℕ)*((1+Real.log (2*Real.pi))/2))) := by
  rw [pureCriticalIntensity_toReal n k (by omega) e]
  have hp := pure_prefactor_value_pos n k (by omega) e
  calc
    _ ≤ ((sphereKRPrefactor (n+1) (FiniteMixture.pure k (by omega) 1 zero_lt_one) 1).toReal *
      (physicalValuePdf (n+2) (FiniteMixture.pure k (by omega) 1 zero_lt_one) 1 e).toReal) *
        Real.exp ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
        SemicirclePotential.potential ((k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D) :=
          mul_le_mul_of_nonneg_left hmean hp.le
    _ = _ := by
      rw [← Real.exp_log hp,← Real.exp_add]
      congr 1
      exact pure_intensity_log_cancellation n k hk e eps D


end TensorPCA.PureIntensityUpperProofs
