-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianTwoStrengthCalculusProofs
public import TensorPCA.GaussianZeroChannelProofs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Endpoint regularity and the closed-interval derivative comparison for the Bayesian cavity interpolation. Differentiability of sqrt at zero is
never required: the raw channel-strength map is continuous and endpoint values
are the exact zero-channel identities. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityPathProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs
open GaussianTwoChannelFreeEnergyProofs GaussianTwoStrengthCalculusProofs GaussianZeroChannelProofs
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega E D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

def guerraPath (mu : Measure Omega) (A : Omega → E) (B : Omega → D) (t : ℝ) : ℝ :=
  twoChannelFreeEnergy mu (fun x ↦ Real.sqrt t • A x) (fun x ↦ Real.sqrt (1-t) • B x)

theorem guerraPath_continuous (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hbA : ∀ᵐ x ∂mu, ‖A x‖ ≤ CA) (hbB : ∀ᵐ x ∂mu, ‖B x‖ ≤ CB) :
    Continuous (guerraPath mu A B) := by
  have hraw : Continuous (fun q : ℝ × ℝ ↦
      twoChannelFreeEnergy mu (fun x ↦ q.1 • A x) (fun x ↦ q.2 • B x)) :=
    continuous_iff_continuousAt.mpr fun q ↦
      (differentiableAt_twoChannelFreeEnergy mu A B hA hB hCA hCB hbA hbB q).continuousAt
  exact hraw.comp (Real.continuous_sqrt.prodMk
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))

omit [BorelSpace E] in
theorem guerraPath_zero (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hB : Measurable B) :
    guerraPath mu A B 0 = mixtureFreeEnergy mu B := by
  simp only [guerraPath,Real.sqrt_zero,sub_zero,Real.sqrt_one,zero_smul,one_smul]
  exact twoChannelFreeEnergy_zero_left mu B hB

theorem guerraPath_one (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) :
    guerraPath mu A B 1 = mixtureFreeEnergy mu A := by
  simp only [guerraPath,Real.sqrt_one,sub_self,Real.sqrt_zero,zero_smul,one_smul]
  exact twoChannelFreeEnergy_zero_right mu A hA

/-- Uniform interior derivative bounds control endpoint differences under
closed-interval continuity alone. No endpoint derivatives are hypotheses. -/
theorem abs_sub_le_of_continuousOn_hasDerivAt_bound {f df : ℝ → ℝ} {C : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hdf : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (df t) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |df t| ≤ C) : |f 1-f 0| ≤ C := by
  have hplus : MonotoneOn (fun t ↦ f t+C*t) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hf.add (continuous_const.mul continuous_id).continuousOn) (f' := fun t ↦ df t+C)
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      have H := (hdf t ht').add ((hasDerivAt_id t).const_mul C)
      convert H.hasDerivWithinAt using 1
      simp only [mul_one]
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      linarith [(abs_le.mp (hb t ht')).1]
  have hminus : MonotoneOn (fun t ↦ C*t-f t) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((continuous_const.mul continuous_id).continuousOn.sub hf) (f' := fun t ↦ C-df t)
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      have H := ((hasDerivAt_id t).const_mul C).sub (hdf t ht')
      convert H.hasDerivWithinAt using 1
      simp only [mul_one]
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      linarith [(abs_le.mp (hb t ht')).2]
  have hp := hplus (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) zero_le_one
  have hm := hminus (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) zero_le_one
  simp only [mul_zero,mul_one,add_zero,zero_sub] at hp hm
  apply abs_le.mpr
  constructor <;> linarith

/-- A bounded genuine derivative of the actual two-channel path compares the
two actual Gaussian-channel free energies. -/
theorem abs_freeEnergy_sub_le_of_guerraPath_derivative
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hbA : ∀ᵐ x ∂mu, ‖A x‖ ≤ CA) (hbB : ∀ᵐ x ∂mu, ‖B x‖ ≤ CB)
    {df : ℝ → ℝ} {C : ℝ}
    (hdf : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (guerraPath mu A B) (df t) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |df t| ≤ C) :
    |mixtureFreeEnergy mu A-mixtureFreeEnergy mu B| ≤ C := by
  have H := abs_sub_le_of_continuousOn_hasDerivAt_bound
    (guerraPath_continuous mu A B hA hB hCA hCB hbA hbB).continuousOn hdf hb
  simpa only [guerraPath_one mu A B hA,guerraPath_zero mu A B hB] using H

end
end TensorPCA.FinitePriorCavityPathProofs
