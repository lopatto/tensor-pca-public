-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorChannelProofs
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Exact scalar product-channel endpoint for a finite product prior -/
@[expose] public section

namespace TensorPCA.FinitePriorScalarEndpointProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianTwoChannelFreeEnergyProofs
open FinitePriorChannelProofs GaussianTensorMomentProofs
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N : ℕ}

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem scalarVector_weight (a : S → ℝ) (c : ℝ) (x : Fin N → S) (y : Model.Vector N) :
    mixtureWeight (c • configurationVector a x) y =
      ∏ i, mixtureWeight (c*a (x i)) (y i) := by
  unfold mixtureWeight
  rw [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.smul_apply, configurationVector, smul_eq_mul, Real.inner_apply]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_div]
  simp only [Real.norm_eq_abs, sq_abs]

omit [Fintype S] [MeasurableSingletonClass S] in
theorem scalarVector_likelihood (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (c : ℝ) (y : Model.Vector N) :
    mixtureLikelihood (configurationPrior p N) (fun x ↦ c • configurationVector a x) y =
      ∏ i, mixtureLikelihood p (fun s ↦ c*a s) (y i) := by
  unfold mixtureLikelihood
  simp_rw [scalarVector_weight]
  exact integral_fintype_prod_eq_prod (fun i s ↦ mixtureWeight (c*a s) (y i))

theorem scalarVector_logLikelihood (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (c : ℝ) (y : Model.Vector N) :
    Real.log (mixtureLikelihood (configurationPrior p N) (fun x ↦ c • configurationVector a x) y) =
      ∑ i, Real.log (mixtureLikelihood p (fun s ↦ c*a s) (y i)) := by
  rw [scalarVector_likelihood]
  exact Real.log_prod (fun i _ ↦ (mixtureLikelihood_pos p _ (measurable_of_finite _) (y i)).ne')

theorem scalarVector_freeEnergy (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (c : ℝ) :
    mixtureFreeEnergy (configurationPrior p N) (fun x ↦ c • configurationVector a x) =
      (N:ℝ)*mixtureFreeEnergy p (fun s ↦ c*a s) := by
  let f : S × ℝ → ℝ := fun z ↦ Real.log (mixtureLikelihood p (fun s ↦ c*a s) (c*a z.1+z.2))
  obtain ⟨K,_,hK⟩ := finite_signal_bound (fun s ↦ c*a s)
  have hf : Integrable f (p.prod (stdGaussian ℝ)) :=
    integrable_logLikelihood_experiment p _ (measurable_of_finite _) (.of_forall hK)
  have hp (i : Fin N) : MeasurePreserving (fun z : (Fin N → S) × Model.Vector N ↦ (z.1 i,z.2 i))
      ((configurationPrior p N).prod (stdGaussian (Model.Vector N))) (p.prod (stdGaussian ℝ)) := by
    have hnoise : MeasurePreserving (fun w : Model.Vector N ↦ w i)
        (stdGaussian (Model.Vector N)) (stdGaussian ℝ) :=
      ⟨(PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).measurable, gaussian_coordinate_law i⟩
    convert (measurePreserving_eval (fun _ : Fin N ↦ p) i).prod hnoise using 1 <;> rfl
  have hi (i : Fin N) : Integrable
      (fun z : (Fin N → S) × Model.Vector N ↦ f (z.1 i,z.2 i))
      ((configurationPrior p N).prod (stdGaussian (Model.Vector N))) :=
    (hp i).integrable_comp_of_integrable hf
  have heq (i : Fin N) : (∫ z : (Fin N → S) × Model.Vector N, f (z.1 i,z.2 i)
      ∂(configurationPrior p N).prod (stdGaussian (Model.Vector N))) =
      mixtureFreeEnergy p (fun s ↦ c*a s) := by
    rw [mixtureFreeEnergy_eq_integral_experiment p _ (measurable_of_finite _)]
    have h := integral_map (hp i).measurable.aemeasurable
      (hf.aestronglyMeasurable.mono_measure (by rw [(hp i).map_eq]))
    rw [(hp i).map_eq] at h
    exact h.symm
  rw [mixtureFreeEnergy_eq_integral_experiment _ _ (measurable_of_finite _)]
  simp_rw [scalarVector_logLikelihood]
  change (∫ z : (Fin N → S) × Model.Vector N, ∑ i, f (z.1 i,z.2 i)
    ∂(configurationPrior p N).prod (stdGaussian (Model.Vector N))) = _
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem scalarSignal_freeEnergy (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (N k : ℕ) (gamma m : ℝ) :
    mixtureFreeEnergy (configurationPrior p N) (scalarSignal a N k gamma m) =
      (N:ℝ)*mixtureFreeEnergy p (fun s ↦ Real.sqrt ((k:ℝ)*gamma*m^(k-1))*a s) :=
  scalarVector_freeEnergy p a _

theorem normalized_scalarSignal_freeEnergy (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (hN : 0 < N) (k : ℕ) (gamma m : ℝ) :
    mixtureFreeEnergy (configurationPrior p N) (scalarSignal a N k gamma m)/(N:ℝ) =
      mixtureFreeEnergy p (fun s ↦ Real.sqrt ((k:ℝ)*gamma*m^(k-1))*a s) := by
  rw [scalarSignal_freeEnergy]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')


end TensorPCA.FinitePriorScalarEndpointProofs
