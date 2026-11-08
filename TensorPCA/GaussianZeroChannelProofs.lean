-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianTwoStrengthPathProofs

/-! # Gaussian two-channel endpoints when one signal vanishes -/
@[expose] public section

namespace TensorPCA.GaussianZeroChannelProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianSideChannelProofs
open GaussianTwoChannelFreeEnergyProofs GaussianTwoStrengthPathProofs

variable {Omega E D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
theorem combinedLikelihood_zero_left (mu : Measure Omega) (B : Omega → D) (y : E) (v : D) :
    combinedLikelihood mu (fun _ ↦ (0:E)) B y v = mixtureLikelihood mu B v := by
  simp only [combinedLikelihood, mixtureLikelihood, mixtureWeight, inner_zero_left, norm_zero,
    zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, sub_self, Real.exp_zero, one_mul]

omit [BorelSpace E] in
theorem twoChannelFreeEnergy_zero_left (mu : Measure Omega) [IsProbabilityMeasure mu]
    (B : Omega → D) (hB : Measurable B) :
    twoChannelFreeEnergy mu (fun _ ↦ (0:E)) B = mixtureFreeEnergy mu B := by
  unfold twoChannelFreeEnergy
  simp_rw [combinedLikelihood_zero_left]
  rw [integral_fun_fst (fun z : Omega × D ↦ Real.log (mixtureLikelihood mu B (B z.1+z.2)))]
  simp only [probReal_univ, one_smul]
  exact (mixtureFreeEnergy_eq_integral_experiment mu B hB).symm

theorem twoChannelFreeEnergy_zero_right (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) :
    twoChannelFreeEnergy mu A (fun _ ↦ (0:D)) = mixtureFreeEnergy mu A := by
  rw [twoChannelFreeEnergy_swap mu A (fun _ ↦ (0:D)) hA measurable_const,
    twoChannelFreeEnergy_zero_left mu A hA]


end TensorPCA.GaussianZeroChannelProofs
