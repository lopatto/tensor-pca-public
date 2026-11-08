-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureRSSliceGroundFromStrongProofs
public import TensorPCA.RetainedCountProofs.SphericalLatitudeStrongFieldMaximum
public import TensorPCA.SliceDecompositionProofs
public import TensorPCA.Reduction
public import TensorPCA.MaximumProofs
public import TensorPCA.FourParameterReductionProofs

/-! Replica-symmetric ground-energy and constrained limits. Every source probability
estimate is proved; no strict-field, count, mean or physical-limit parameter
remains. The analytic identity and four-parameter clause retain their variational meanings, while the constrained theorem explicitly supplies physical backing. -/
@[expose] public section
namespace TensorPCA.RSGroundStateProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open RetainedCountProofs SphericalModel SphericalGaussianJet SphericalLatitudeChartKacRice
open scoped Topology RealInnerProductSpace
universe u

theorem sliceGroundLimit_rs (k : ℕ) (hk : 3 ≤ k) (m : ℝ)
    (hm : m ∈ Icc (-1 : ℝ) 1)
    (hlarge : Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m|) : GroundState.SliceGroundLimit k m := by
  apply PureRSSliceGroundFromStrongProofs.sliceGroundLimit_rs_of_strong k hk _ m hm hlarge
  dsimp only
  intro r hr hab delta hdelta
  simpa only [latitudeField] using
    latitude_strongField_maximum_lower (FiniteMixture.pure k (by omega) 1 zero_lt_one)
      (Q := 1) zero_lt_one (ne_of_gt hr.1)
      (by simpa only [abs_of_pos hr.1] using hr.2) hab hdelta

theorem energy_eq_rs (k : ℕ) (hk : 3 ≤ k) (lam m : ℝ)
    (hm : m ∈ Icc (-1 : ℝ) 1)
    (hlarge : Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m|) :
    Scalar.energy k lam m = Scalar.rsEnergy k lam m := by
  unfold Scalar.energy Scalar.rsEnergy
  rw [GroundState.rsSlice_of_general RSVariationalProof.generalRSVariationalLaw
    VariationalProofs.slicePolynomialFacts k hk m hm hlarge]

/-- Both expected and almost-sure physical limits, pointwise in fixed strength
and overlap, with arbitrary across-dimension physical coupling. -/
theorem constrainedLimit_rs (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) (_hlam : 0 ≤ lam)
    (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1)
    (hlarge : Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m|) :
    (Tendsto (fun n : ℕ => ∫ z, Model.constrainedMaximum lam z.1 z.2 m
      ∂Model.experimentLaw (n+2) k) atTop (nhds (Scalar.rsEnergy k lam m))) ∧
    (∀ (Omega : Type u) [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
      (E : Statements.PhysicalSequence k Omega mu),
      ∀ᵐ omega ∂mu, Tendsto (fun n : ℕ => Model.constrainedMaximum lam
        (E.sample (n+1) omega).1 (E.sample (n+1) omega).2 m) atTop
          (nhds (Scalar.rsEnergy k lam m))) := by
  have hg := sliceGroundLimit_rs k hk m hm hlarge
  have hs := SliceDecompositionProofs.sliceDecomposition k lam hm
  have he := energy_eq_rs k hk lam m hm hlarge
  constructor
  · simpa only [he] using Reduction.constrained_mean_at hg hs
  · intro Omega _ mu _ E
    simpa only [he] using (Reduction.constrained_at E hg hs
      (MaximumProofs.sampleConstrainedMaximum_centered_ae E lam m (abs_le.mpr hm))).2

theorem variationalConclusions : Statements.VariationalConclusions := by
  intro k hk
  constructor
  · intro lam _ m hm hlarge
    exact energy_eq_rs k hk lam m hm hlarge
  · intro m hm
    exact FourParameterReductionProofs.fourParameterReduction k hk hm

end
end TensorPCA.RSGroundStateProofs
