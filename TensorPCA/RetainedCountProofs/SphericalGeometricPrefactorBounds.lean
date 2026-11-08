-- SPDX-License-Identifier: Apache-2.0
/- Attributed actual sphere-area logarithmic normalization source port from
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e:
   SphericalGeometricPrefactorRates.lean (exact log mass) and
   SphericalGeometricPrefactorBounds.lean (first bounded-error theorem).
   Only these actual finite normalization APIs are needed by the latitude;
   no unrelated score/count asymptotic theorem is imported. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GammaHalfStirling
public import TensorPCA.RetainedCountProofs.RoundSphereArea
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalMarkedWindows
open MeasureTheory Set SphereChartVolume SphereAreaAsymptotics
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma manuscriptRoundVolume_log_mass (n : ℕ) :
    Real.log (manuscriptRoundVolume (n+1) univ).toReal =
      ((n+2 : ℝ)+1)/2 * Real.log (n+2 : ℝ) +
      (n+2 : ℝ)/2 * Real.log Real.pi - Real.log (Real.Gamma ((n+2 : ℝ)/2+1)) := by
  rw [manuscriptRoundVolume_mass_gamma]
  have hN : (0 : ℝ) < n+2 := by positivity
  have hG : 0 < Real.Gamma ((n+2 : ℝ)/2+1) := Real.Gamma_pos_of_pos (by positivity)
  simp only [Nat.cast_add, Nat.cast_one, show (n:ℝ)+1+1=n+2 by ring]
  rw [ENNReal.toReal_ofReal (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hN.ne', Real.log_pow, Real.log_div (by positivity) hG.ne',
    Real.log_pow, Real.log_sqrt hN.le, Real.log_sqrt Real.pi_pos.le]
  push_cast
  ring

theorem manuscriptRoundVolume_log_error_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      |Real.log (manuscriptRoundVolume (n+1) univ).toReal -
        (n+2 : ℕ) * ((1 + Real.log (2 * Real.pi))/2)| ≤ B := by
  obtain ⟨B,hB,hΓ⟩ := gamma_half_integer_log_remainder_bound
  refine ⟨|Real.log 2|/2+B, by positivity, ?_⟩
  intro n
  have h := hΓ (n+2) (by omega)
  rw [manuscriptRoundVolume_log_mass n,
    Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
  have hN : (0 : ℝ) < n+2 := by positivity
  rw [Real.log_div (by positivity : ((n+2:ℕ):ℝ)≠0) (by norm_num : (2:ℝ)≠0)] at h
  push_cast at h ⊢
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [le_abs_self (Real.log 2), neg_le_abs (Real.log 2)]


end
end TensorPCA.RetainedCountProofs.SphericalMarkedWindows
