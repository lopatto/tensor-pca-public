-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianBoundedIMMSEProofs

/-! # Averaged posterior second moment is bounded by the prior moment -/
@[expose] public section

namespace TensorPCA.GaussianPosteriorSecondMomentProofs

open MeasureTheory ProbabilityTheory GaussianPosteriorProofs

variable {Omega E V : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- This is an averaged bound for the actual conditional mean. It makes no
pointwise assertion about a posterior overlap center. -/
theorem integral_posteriorMean_norm_sq_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (A : Omega → V)
    (hA : StronglyMeasurable A) (hA2 : MemLp A 2 mu) :
    (∫ z : Omega × E, ‖posteriorMean mu F A (F z.1+z.2)‖^2 ∂mu.prod (stdGaussian E)) ≤
      ∫ x, ‖A x‖^2 ∂mu := by
  let base := mu.prod (stdGaussian E)
  let obs : Omega × E → E := fun z ↦ F z.1+z.2
  let latent : Omega × E → V := fun z ↦ A z.1
  have hlatent : MemLp latent 2 base := hA2.comp_fst (stdGaussian E)
  have hsq : Integrable (fun z ↦ ‖latent z‖^(2:ℝ)) base := by
    simpa only [Real.rpow_two] using hlatent.integrable_norm_pow (by decide : 2 ≠ 0)
  have hj := integral_norm_condExp_rpow_le (μ := base) (m := MeasurableSpace.comap obs (inferInstance : MeasurableSpace E)) (by norm_num : 1 ≤ (2:ℝ)) hsq
  have hce := posteriorMean_ae_eq_condExp mu F hF A hA (hA2.integrable (by norm_num))
  calc
    _ = ∫ z, ‖base[latent | MeasurableSpace.comap obs (inferInstance : MeasurableSpace E)] z‖^2 ∂base := by
      apply integral_congr_ae
      filter_upwards [hce] with z hz
      rw [hz]
    _ ≤ ∫ z, ‖latent z‖^2 ∂base := by simpa only [Real.rpow_two] using hj
    _ = _ := by
      rw [integral_fun_fst (fun x ↦ ‖A x‖^2)]
      simp only [probReal_univ, one_smul]


end TensorPCA.GaussianPosteriorSecondMomentProofs
