-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.SphericalParisiGlobalPrimalDual
public import TensorPCA.PlateauVariationalTrialProofs

/-! Literal normalization bridge from the source one-step primal functional
to the variational profile class. No physical upper or lower limit is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSSphericalGroundPrimalDualProofs
open Set MeasureTheory
open NonRSUpperProofs
noncomputable section

theorem profile_eq_fourParameterProfile (delta b s t : ℝ) :
    LatitudeGroundTrial.profile (delta + b * (1 - s)) b s t =
      Scalar.fourParameterProfile delta 0 b s t := by
  unfold LatitudeGroundTrial.profile Scalar.fourParameterProfile
  by_cases ht : t ≤ s
  · rw [max_eq_right ht, max_eq_right (sub_nonpos.mpr ht)]
    ring
  · rw [max_eq_left (le_of_not_ge ht), max_eq_left (sub_nonneg.mpr (le_of_not_ge ht))]
    ring

theorem functional_eq_half_parisiFunctional (xi : ℝ → ℝ)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    {delta b s : ℝ} (hd : 0 < delta) (hb : 0 ≤ b) (hs : s ∈ Icc (0 : ℝ) 1) :
    LatitudeGroundTrial.functional (deriv xi) (deriv (deriv xi))
      (delta + b * (1 - s)) b s =
      (1 / 2 : ℝ) * Scalar.parisiFunctional xi 0
        (Scalar.fourParameterProfile delta 0 b s) := by
  let p := Scalar.fourParameterProfile delta 0 b s
  have hp : Scalar.AdmissibleProfile p :=
    VariationalProofs.fourParameterProfile_admissible _ _ _ _ ⟨hd, le_rfl, hb, hs⟩
  have hweight : IntervalIntegrable (fun t => deriv (deriv xi) t * p t) volume 0 1 :=
    (hxi.mul hp.1).intervalIntegrable_of_Icc zero_le_one
  have hinv : IntervalIntegrable (fun t => (p t)⁻¹) volume 0 1 :=
    (hp.1.inv₀ (fun t ht => (hp.2.2.2 t ht).ne')).intervalIntegrable_of_Icc zero_le_one
  have hp0 : p 0 = delta + b * (1 - s) := by
    simp only [p, Scalar.fourParameterProfile, zero_mul, add_zero, max_eq_right hs.1]
  unfold LatitudeGroundTrial.functional Scalar.parisiFunctional
  simp_rw [profile_eq_fourParameterProfile]
  change (deriv xi 0 * (delta + b * (1 - s)) +
      (∫ t in (0 : ℝ)..1, deriv (deriv xi) t * p t) +
      (∫ t in (0 : ℝ)..1, (p t)⁻¹)) / 2 = _
  simp only [one_div, zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [intervalIntegral.integral_add hweight hinv]
  rw [show Scalar.fourParameterProfile delta 0 b s 0 = delta + b * (1 - s) from hp0]
  ring

end
end TensorPCA.NonRSSphericalGroundPrimalDualProofs

