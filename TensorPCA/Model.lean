/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.Probability.Independence.Basic

/-!
# The finite tensor experiment and its statistical functionals

All measures and functions below are concrete. In particular, the posterior is
Mathlib's vector-valued conditional expectation under the product prior
and Gaussian noise law. The Gaussian radial definition of `spherePrior` sends
zero to zero; in positive dimension its exceptional origin has Gaussian measure
zero. Its sphere support, rotation invariance, and radial-law identification are
separate proof obligations, not assumptions used in these definitions.

The natural-number parameter `N` is the ambient dimension. Principal
asymptotic statements use positive dimensions; no assertion about a sphere in
zero-dimensional space is intended. Real `sSup`, integral, and conditional
expectation use Mathlib's total conventions; nonemptiness, boundedness and
integrability must be proved where they are applied.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace

namespace TensorPCA.Model

/-- Physical vectors with the Euclidean norm. -/
abbrev Vector (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- All ordered tensor coordinates, with the Euclidean/Frobenius norm. -/
abbrev Tensor (N k : ℕ) := EuclideanSpace ℝ (Fin k → Fin N)

/-- Genuine coordinate product, including the ordinary empty-product convention. -/
noncomputable def feature {N : ℕ} (k : ℕ) (x : Vector N) : Tensor N k :=
  WithLp.toLp 2 (fun i ↦ ∏ j, x (i j))

/-- The actual unit sphere as an ambient set, rather than an abstract state space. -/
def unitSphere (N : ℕ) : Set (Vector N) := {x | ‖x‖ = 1}

/-- Radial normalization; the value at the origin is zero. -/
noncomputable def normalize {N : ℕ} (x : Vector N) : Vector N := ‖x‖⁻¹ • x

/-- Away from the explicitly documented origin convention, radial normalization
really lands on the unit sphere. -/
theorem norm_normalize {N : ℕ} (x : Vector N) (hx : x ≠ 0) : ‖normalize x‖ = 1 := by
  simp [normalize, norm_smul, norm_inv, norm_ne_zero_iff.mpr hx]

/-- The concrete radial map is measurable, so its pushforward is a genuine law. -/
theorem measurable_normalize (N : ℕ) : Measurable (normalize (N := N)) := by
  exact measurable_norm.inv.smul measurable_id

/-- Normalized Gaussian angular law. Its identification with uniform sphere
probability for `0 < N` is a required supporting obligation. -/
noncomputable def spherePrior (N : ℕ) : Measure (Vector N) :=
  (stdGaussian (Vector N)).map normalize

/-- Independent standard Gaussian tensor entries. -/
noncomputable def noiseLaw (N k : ℕ) : Measure (Tensor N k) :=
  stdGaussian (Tensor N k)

/-- Joint law of the independent uniform planted vector and tensor noise. -/
noncomputable def experimentLaw (N k : ℕ) : Measure (Vector N × Tensor N k) :=
  (spherePrior N).prod (noiseLaw N k)

/-- The observation in equation (1.1), with the manuscript's exact scaling. -/
noncomputable def observation {N k : ℕ} (lam : ℝ)
    (z : Vector N × Tensor N k) : Tensor N k :=
  (lam * Real.sqrt N) • feature k z.1 + z.2

/-- Null and alternative laws are the cases `lam = 0` and general `lam`. -/
noncomputable def observationLaw (N k : ℕ) (lam : ℝ) : Measure (Tensor N k) :=
  (experimentLaw N k).map (observation lam)

/-- Probability-normalized total variation, taking values in `[0,1]` for
probability measures. Mathlib's `MeasureTheory.tvDist` has twice this normalization. -/
noncomputable def testingDistance (N k : ℕ) (lam : ℝ) : ℝ :=
  MeasureTheory.tvDist (observationLaw N k 0) (observationLaw N k lam) / 2

/-- The unnormalized likelihood objective. -/
noncomputable def score {N k : ℕ} (y : Tensor N k) (x : Vector N) : ℝ :=
  inner ℝ (feature k x) y

/-- The actual normalized maximum from the main MLE-value conclusion. -/
noncomputable def normalizedMaximum {N k : ℕ} (y : Tensor N k) : ℝ :=
  sSup (score y '' unitSphere N) / Real.sqrt N

/-- Null spherical Hamiltonian, with the sign convention of equation `ham-def`. -/
noncomputable def hamiltonian {N k : ℕ} (w : Tensor N k) (x : Vector N) : ℝ :=
  Real.sqrt N * score w x

/-- The actual planted Hamiltonian used in the estimation section. -/
noncomputable def plantedHamiltonian {N k : ℕ} (lam : ℝ)
    (x : Vector N) (w : Tensor N k) (v : Vector N) : ℝ :=
  lam * N * (inner ℝ v x) ^ k + hamiltonian w v

/-- The normalized sphere-slice maximum. For `N ≥ 2`, unit `x` and `m ∈ [-1,1]`
the constraint is nonempty. Such facts are supporting obligations. -/
noncomputable def constrainedMaximum {N k : ℕ} (lam : ℝ)
    (x : Vector N) (w : Tensor N k) (m : ℝ) : ℝ :=
  sSup ((fun v ↦ lam * m ^ k + score w v / Real.sqrt N) ''
    {v ∈ unitSphere N | inner ℝ v x = m})

/-- Null partition function with exactly the manuscript's negative-temperature
exponent `exp (-lam * H)` (Gaussian symmetry is not silently applied). -/
noncomputable def partitionFunction (N k : ℕ) (lam : ℝ) (w : Tensor N k) : ℝ :=
  ∫ x, Real.exp (-lam * hamiltonian w x) ∂spherePrior N

/-- Free energy per physical coordinate. -/
noncomputable def freeEnergy (N k : ℕ) (lam : ℝ) (w : Tensor N k) : ℝ :=
  Real.log (partitionFunction N k lam w) / N

/-- The Gaussian likelihood ratio, integrated over the actual planted prior. -/
noncomputable def likelihoodRatio (N k : ℕ) (lam : ℝ) (y : Tensor N k) : ℝ :=
  ∫ x, Real.exp (lam * Real.sqrt N * score y x - N * lam ^ 2 / 2) ∂spherePrior N

/-- The sub-σ-algebra generated by the observed tensor, with its canonical Borel
measurable structure. It is not the whole latent experiment σ-algebra. -/
@[instance_reducible] noncomputable def observedSigma (N k : ℕ) (lam : ℝ) : MeasurableSpace (Vector N × Tensor N k) :=
  MeasurableSpace.comap (observation lam) (inferInstance : MeasurableSpace (Tensor N k))

/-- A version of the conditional mean of the actual planted feature given `Y`. -/
noncomputable def posteriorTensor (N k : ℕ) (lam : ℝ) :
    Vector N × Tensor N k → Tensor N k :=
  MeasureTheory.condExp (observedSigma N k lam) (experimentLaw N k)
    (fun z ↦ feature k z.1)

/-- The finite tensor MMSE, with squared Frobenius loss. -/
noncomputable def tensorMMSE (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ z, ‖feature k z.1 - posteriorTensor N k lam z‖ ^ 2 ∂experimentLaw N k

/-- A unit-vector estimator may use an arbitrary independent auxiliary space. -/
abbrev Estimator (N k : ℕ) (A : Type*) := Tensor N k → A → Vector N

/-- Borel measurability and the unit-vector codomain are part of estimator meaning. -/
def IsUnitEstimator {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (est : Estimator N k A) : Prop :=
  Measurable (Function.uncurry est) ∧ ∀ y a, ‖est y a‖ = 1

/-- The estimator actually attains the likelihood maximum, almost surely for
observation and independent auxiliary law. Fair-sign randomization, when needed
for signed statements, is specified separately by `HasSymmetricOutputLaw`. -/
def IsMLE (N k : ℕ) (lam : ℝ) {A : Type*} [MeasurableSpace A]
    (est : Estimator N k A) (ν : Measure A) : Prop :=
  IsUnitEstimator est ∧
    ∀ᵐ z ∂(observationLaw N k lam).prod ν,
      ∀ x ∈ unitSphere N, score z.1 x ≤ score z.1 (est z.1 z.2)

/-- Symmetric sign selection, as required by the paper's even-order MLE
convention. When the maximizing set is an antipodal pair this is the fair law. -/
def HasSymmetricOutputLaw {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (est : Estimator N k A) (ν : Measure A) : Prop :=
  ∀ y, ν.map (est y) = ν.map (fun a ↦ -est y a)

/-- Expected absolute overlap power under independent estimator randomization. -/
noncomputable def expectedOverlapPower (N k : ℕ) (lam : ℝ) {A : Type*}
    [MeasurableSpace A] (est : Estimator N k A) (ν : Measure A) (p : ℕ) : ℝ :=
  ∫ z, |inner ℝ (est (observation lam z.1) z.2) z.1.1| ^ p
    ∂(experimentLaw N k).prod ν

/-- Expected planted maximum in the manuscript's normalization. -/
noncomputable def expectedMaximum (N k : ℕ) (lam : ℝ) : ℝ :=
  ∫ z, normalizedMaximum (observation lam z) ∂experimentLaw N k

/-- The concrete angular map defines a probability law; support on the unit
sphere in positive dimension is a separate identification obligation. -/
instance spherePrior_probability (N : ℕ) : IsProbabilityMeasure (spherePrior N) := by
  exact (Measure.isProbabilityMeasure_map_iff (measurable_normalize N).aemeasurable).2 inferInstance

instance noiseLaw_probability (N k : ℕ) : IsProbabilityMeasure (noiseLaw N k) := by
  unfold noiseLaw
  infer_instance

instance experimentLaw_probability (N k : ℕ) : IsProbabilityMeasure (experimentLaw N k) := by
  unfold experimentLaw
  infer_instance

theorem continuous_feature (N k : ℕ) : Continuous (feature (N := N) k) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fun_prop

theorem measurable_observation (N k : ℕ) (lam : ℝ) :
    Measurable (observation (N := N) (k := k) lam) := by
  have hc : Continuous (fun _ : Vector N × Tensor N k ↦ lam * Real.sqrt N) := continuous_const
  exact ((hc.smul ((continuous_feature N k).comp continuous_fst)).add
    continuous_snd).measurable

instance observationLaw_probability (N k : ℕ) (lam : ℝ) :
    IsProbabilityMeasure (observationLaw N k lam) := by
  exact (Measure.isProbabilityMeasure_map_iff (measurable_observation N k lam).aemeasurable).2
    inferInstance

end TensorPCA.Model
