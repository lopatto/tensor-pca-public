-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianReplicaTransportProofs
public import TensorPCA.TensorOrbitAggregationProofs
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Finite scalar product-prior tensor and scalar channels

The tensor signal is the same unordered channel already related exactly to
the ordered Gaussian model. A finite alphabet is embedded by its real coordinate values; no coordinate independence is assumed of the posterior.
-/
@[expose] public section

namespace TensorPCA.FinitePriorChannelProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianReplicaTransportProofs
open TensorOrbitCountProofs GaussianTwoChannelFreeEnergyProofs
open scoped RealInnerProductSpace

variable {S : Type*} [MeasurableSpace S]

noncomputable def configurationPrior (p : Measure S) (N : ℕ) : Measure (Fin N → S) :=
  Measure.pi (fun _ : Fin N ↦ p)

noncomputable def configurationVector {N : ℕ} (a : S → ℝ) (x : Fin N → S) : Model.Vector N :=
  WithLp.toLp 2 (fun i ↦ a (x i))

noncomputable def tensorSignal (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) :
    EuclideanSpace ℝ (KSubset N k) :=
  TensorOrbitAggregationProofs.unorderedSignal N k gamma (configurationVector a x)

noncomputable def scalarSignal (a : S → ℝ) (N k : ℕ) (gamma q : ℝ) (x : Fin N → S) : Model.Vector N :=
  Real.sqrt ((k:ℝ)*gamma*q^(k-1)) • configurationVector a x

noncomputable def freeEnergy (p : Measure S) (a : S → ℝ) (N k : ℕ) (gamma : ℝ) : ℝ :=
  mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma) / N

noncomputable def scalarPotential (p : Measure S) (a : S → ℝ) (k : ℕ) (gamma q : ℝ) : ℝ :=
  mixtureFreeEnergy p (fun s ↦ Real.sqrt ((k:ℝ)*gamma*q^(k-1)) * a s) -
    ((k-1:ℕ):ℝ)*gamma*q^k/2

noncomputable def interpolatingFreeEnergy (p : Measure S) (a : S → ℝ) (N k : ℕ)
    (gamma q t : ℝ) : ℝ :=
  twoChannelFreeEnergy (configurationPrior p N)
    (fun x ↦ Real.sqrt t • tensorSignal a N k gamma x)
    (fun x ↦ Real.sqrt (1-t) • scalarSignal a N k gamma q x) / N

instance configurationPrior_probability (p : Measure S) [IsProbabilityMeasure p] (N : ℕ) :
    IsProbabilityMeasure (configurationPrior p N) := by
  unfold configurationPrior
  infer_instance

theorem measurable_configurationVector [Fintype S] [MeasurableSingletonClass S]
    (a : S → ℝ) (N : ℕ) : Measurable (configurationVector (N := N) a) :=
  measurable_of_finite _

theorem measurable_tensorSignal [Fintype S] [MeasurableSingletonClass S]
    (a : S → ℝ) (N k : ℕ) (gamma : ℝ) : Measurable (tensorSignal a N k gamma) :=
  measurable_of_finite _

theorem measurable_scalarSignal [Fintype S] [MeasurableSingletonClass S]
    (a : S → ℝ) (N k : ℕ) (gamma q : ℝ) : Measurable (scalarSignal a N k gamma q) :=
  measurable_of_finite _

theorem finite_signal_bound {Omega V : Type*} [Fintype Omega] [NormedAddCommGroup V] (F : Omega → V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖F x‖ ≤ K := by
  classical
  refine ⟨∑ x, ‖F x‖, Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _), fun x ↦ ?_⟩
  exact Finset.single_le_sum (fun y _ ↦ norm_nonneg (F y)) (Finset.mem_univ x)

/-- The genuine finite product-prior interpolation has the checked full
posterior derivative. Finiteness discharges every analytic boundedness premise;
no limit or overlap concentration is assumed. -/
theorem finite_guerraPath_hasDerivAt [Fintype S] [MeasurableSingletonClass S]
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma q : ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (interpolatingFreeEnergy p a N k gamma q)
      (((1/2:ℝ) * ∫ z, ‖combinedMean (configurationPrior p N)
          (fun x ↦ Real.sqrt t • tensorSignal a N k gamma x)
          (fun x ↦ Real.sqrt (1-t) • scalarSignal a N k gamma q x) (tensorSignal a N k gamma) z‖^2
          ∂pairObservationLaw (configurationPrior p N)
            (fun x ↦ Real.sqrt t • tensorSignal a N k gamma x)
            (fun x ↦ Real.sqrt (1-t) • scalarSignal a N k gamma q x) -
       (1/2:ℝ) * ∫ z, ‖combinedMean (configurationPrior p N)
          (fun x ↦ Real.sqrt t • tensorSignal a N k gamma x)
          (fun x ↦ Real.sqrt (1-t) • scalarSignal a N k gamma q x) (scalarSignal a N k gamma q) z‖^2
          ∂pairObservationLaw (configurationPrior p N)
            (fun x ↦ Real.sqrt t • tensorSignal a N k gamma x)
            (fun x ↦ Real.sqrt (1-t) • scalarSignal a N k gamma q x)) / (N:ℝ)) t := by
  obtain ⟨KA,hKA,hAB⟩ := finite_signal_bound (tensorSignal a N k gamma)
  obtain ⟨KB,hKB,hBB⟩ := finite_signal_bound (scalarSignal a N k gamma q)
  have h := hasDerivAt_guerraPath_commonPosterior (configurationPrior p N)
    (tensorSignal a N k gamma) (scalarSignal a N k gamma q)
    (measurable_tensorSignal a N k gamma) (measurable_scalarSignal a N k gamma q)
    hKA hKB (.of_forall hAB) (.of_forall hBB) ht0 ht1
  convert h.div_const (N:ℝ) using 1
  rfl


end TensorPCA.FinitePriorChannelProofs
