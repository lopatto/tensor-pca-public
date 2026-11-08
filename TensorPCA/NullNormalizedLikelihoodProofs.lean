-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.NullLikelihoodRateProofs
public import TensorPCA.TotalVariationVarianceProofs

/-! Normalized null log-likelihood mean and variance. Canonical Gaussian
reflection preserves the thermal free-energy variance, so its coarse vanishing
needs no subcriticality or physical interpolation hypothesis. -/

@[expose] public section
namespace TensorPCA.NullNormalizedLikelihoodProofs
open MeasureTheory ProbabilityTheory Set Filter NullLikelihoodRateProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- The normalized likelihood keeps the reflected thermal exponent explicitly. -/
theorem normalizedNullLogLikelihood_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    Statistical.nullLogLikelihood N k lam w/(N : ℝ) = Model.freeEnergy N k lam (-w)-lam^2/2 := by
  rw [nullLogLikelihood_eq hN lam w]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')

/-- The actual normalized null mean is the thermal mean deficit. -/
theorem nullNormalizedLogMean_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Statistical.nullNormalizedLogMean N k lam = Coupled.meanNullFE N k lam-lam^2/2 := by
  unfold Statistical.nullNormalizedLogMean
  simp_rw [normalizedNullLogLikelihood_eq hN lam]
  have hc : Continuous (fun w : Model.Tensor N k ↦ Model.freeEnergy N k lam w-lam^2/2) :=
    (FreeEnergyProofs.freeEnergy_contDiff hN lam).continuous.sub continuous_const
  rw [integral_noise_neg _ hc]
  have hi := (FreeEnergyProofs.freeEnergy_memLp (k := k) hN lam 1 (by norm_num)).integrable le_rfl
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  rfl

/-- Normalized null log likelihood has exactly the thermal free-energy variance. -/
theorem nullNormalizedLogVariance_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Statistical.nullNormalizedLogVariance N k lam = Coupled.varNullFE N k lam := by
  unfold Statistical.nullNormalizedLogVariance
  rw [nullNormalizedLogMean_eq hN lam]
  simp_rw [normalizedNullLogLikelihood_eq hN lam]
  calc
    _ = ∫ w, (Model.freeEnergy N k lam (-w)-Coupled.meanNullFE N k lam)^2 ∂Model.noiseLaw N k := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro w
      dsimp only
      congr 1
      ring
    _ = ∫ w, (Model.freeEnergy N k lam w-Coupled.meanNullFE N k lam)^2 ∂Model.noiseLaw N k :=
      integral_noise_neg _ (((FreeEnergyProofs.freeEnergy_contDiff hN lam).continuous.sub continuous_const).pow 2)
    _ = _ := rfl

/-- Unconditional finite variance bound for the actual normalized likelihood. -/
theorem nullNormalizedLogVariance_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Statistical.nullNormalizedLogVariance N k lam ≤ lam^2/(N : ℝ) := by
  rw [nullNormalizedLogVariance_eq hN lam]
  exact NullVarianceProofs.varNullFE_le hN lam

/-- Actual normalized null likelihood fluctuations vanish in L2 for every
order and strength, without a ground-state or coupled-interpolation premise. -/
theorem nullNormalizedLogVarianceLimit (k : ℕ) (lam : ℝ) :
    Statistical.NullNormalizedLogVarianceLimit k lam := by
  unfold Statistical.NullNormalizedLogVarianceLimit
  have hd : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ by exact_mod_cast (Nat.le_succ n))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero (fun n ↦ integral_nonneg (fun w ↦ sq_nonneg
      (Statistical.nullLogLikelihood (n+1) k lam w/(n+1 : ℕ)-Statistical.nullNormalizedLogMean (n+1) k lam)))
    (fun n ↦ nullNormalizedLogVariance_le (Nat.succ_pos n) lam)
  exact hd.const_div_atTop (lam^2)

/-- A genuine eventual negative thermal mean gap suffices for supercritical
separation. The mean gap itself is not asserted here. -/
theorem testingDistance_tendsto_one_of_thermal_gap {k : ℕ} {lam a : ℝ} (ha : 0 < a)
    (hgap : ∀ᶠ n : ℕ in atTop, Coupled.meanNullFE (n+1) k lam-lam^2/2 ≤ -2*a) :
    Tendsto (fun n : ℕ ↦ Model.testingDistance (n+1) k lam) atTop (𝓝 1) := by
  apply Statistical.testingDistance_tendsto_one_of_logVariance
    (TotalVariationVarianceProofs.finiteTVVarianceBound_of_eventual_negative_mean_gap ha ?_)
    (nullNormalizedLogVarianceLimit k lam)
  filter_upwards [hgap] with n hn
  rw [nullNormalizedLogMean_eq (Nat.succ_pos n) lam]
  exact hn

end
end TensorPCA.NullNormalizedLikelihoodProofs
