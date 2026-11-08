-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationScalarProofs

/-! The finite alphabet is the subtype range of the explicit quantizer.
Its lifted Gaussian law, coordinate values and channel pushforwards are
identified exactly, preserving the full nonunit Gaussian likelihood penalty. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationAlphabetProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianFinitePriorApproximationProofs
open GaussianFinitePriorApproximationScalarProofs GaussianPriorTransferProofs FinitePriorChannelProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

abbrev QuantizedAlphabet (j : ℕ) := ↥(Set.range (gaussianQuantizer j))

instance quantizedAlphabet_fintype (j : ℕ) : Fintype (QuantizedAlphabet j) :=
  (gaussianQuantizer_finite_range j).fintype

def liftedQuantizer (j : ℕ) (x : ℝ) : QuantizedAlphabet j := ⟨gaussianQuantizer j x,⟨x,rfl⟩⟩

def liftedGaussianPrior (j : ℕ) : Measure (QuantizedAlphabet j) :=
  (stdGaussian ℝ).map (liftedQuantizer j)

theorem liftedQuantizer_measurable (j : ℕ) : Measurable (liftedQuantizer j) :=
  Measurable.subtype_mk (gaussianQuantizer_measurable j)

instance liftedGaussianPrior_probability (j : ℕ) : IsProbabilityMeasure (liftedGaussianPrior j) := by
  unfold liftedGaussianPrior
  exact (Measure.isProbabilityMeasure_map_iff (liftedQuantizer_measurable j).aemeasurable).mpr inferInstance

/-- Actual scalar values of the lifted law reproduce the quantized real law. -/
theorem liftedGaussianPrior_map_coe (j : ℕ) :
    (liftedGaussianPrior j).map (Subtype.val : QuantizedAlphabet j → ℝ) = finiteGaussianPrior j := by
  rw [liftedGaussianPrior,Measure.map_map measurable_subtype_coe (liftedQuantizer_measurable j)]
  rfl

theorem alphabet_value_bound (j : ℕ) (s : QuantizedAlphabet j) : |(s : ℝ)| ≤ (j : ℝ)+1 := by
  obtain ⟨x,hx⟩ := s.property
  rw [← hx]
  exact gaussianQuantizer_abs_le_bound j x

theorem liftedGaussianPrior_second_moment_le_one (j : ℕ) :
    (∫ s : QuantizedAlphabet j,(s : ℝ)^2 ∂liftedGaussianPrior j) ≤ 1 := by
  have H := integral_map (μ := liftedGaussianPrior j)
    measurable_subtype_coe.aemeasurable (show AEStronglyMeasurable (fun x : ℝ ↦ x^2)
      ((liftedGaussianPrior j).map (Subtype.val : QuantizedAlphabet j → ℝ)) by fun_prop)
  rw [liftedGaussianPrior_map_coe] at H
  exact H ▸ finiteGaussianPrior_second_moment_le_one j

section ValueTransport
variable {S : Type*} [MeasurableSpace S]

/-- Product-prior output free energy depends on the actual scalar value law. -/
theorem freeEnergy_value_pushforward (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (ha : Measurable a) (N k : ℕ) (gamma : ℝ) :
    freeEnergy p a N k gamma = freeEnergy (p.map a) id N k gamma := by
  have : IsProbabilityMeasure (p.map a) := (Measure.isProbabilityMeasure_map_iff ha.aemeasurable).mpr inferInstance
  let f : (Fin N → S) → (Fin N → ℝ) := fun x i ↦ a (x i)
  have hf : Measurable f := measurable_pi_iff.mpr (fun i ↦ ha.comp (measurable_pi_apply i))
  have hprior : (configurationPrior p N).map f = configurationPrior (p.map a) N :=
    Measure.pi_map_pi (fun _i : Fin N ↦ ha.aemeasurable)
  have hsignal : Measurable (tensorSignal (id : ℝ → ℝ) N k gamma) :=
    (TensorOrbitAggregationProofs.measurable_unorderedSignal N k gamma).comp
      (PiLp.continuous_toLp 2 (fun _ : Fin N ↦ ℝ)).measurable
  unfold freeEnergy
  rw [← hprior,mixtureFreeEnergy_map_prior (configurationPrior p N) f hf _ hsignal]
  rfl

theorem scalarPotential_value_pushforward (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (ha : Measurable a) (k : ℕ) (gamma q : ℝ) :
    scalarPotential p a k gamma q = scalarPotential (p.map a) id k gamma q := by
  unfold scalarPotential
  simp only [id_eq]
  rw [mixtureFreeEnergy_map_prior p a ha (fun x : ℝ ↦ Real.sqrt ((k : ℝ)*gamma*q^(k-1))*x) (by fun_prop)]
  rfl
end ValueTransport

/-- Exact finite-alphabet tensor channel, with its full original signal. -/
theorem lifted_freeEnergy_eq (j N k : ℕ) (gamma : ℝ) :
    freeEnergy (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma =
      freeEnergy (finiteGaussianPrior j) id N k gamma := by
  rw [freeEnergy_value_pushforward _ _ measurable_subtype_coe,liftedGaussianPrior_map_coe]

/-- Exact finite-alphabet scalar potential, with no recentering/penalty change. -/
theorem lifted_scalarPotential_eq (j k : ℕ) (gamma q : ℝ) :
    scalarPotential (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) k gamma q =
      scalarPotential (finiteGaussianPrior j) id k gamma q := by
  rw [scalarPotential_value_pushforward _ _ measurable_subtype_coe,liftedGaussianPrior_map_coe]

/-- The actual finite-alphabet RS potential inherits the uniform approximation. -/
theorem lifted_scalarPotential_uniform_approx (k : ℕ) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (j : ℕ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    |scalarPotential (stdGaussian ℝ) id k gamma q-
      scalarPotential (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) k gamma q| ≤
        scalarApproximationError k gamma j := by
  rw [lifted_scalarPotential_eq]
  exact scalarPotential_uniform_approx k hgamma j hq

end
end TensorPCA.GaussianFinitePriorApproximationAlphabetProofs
