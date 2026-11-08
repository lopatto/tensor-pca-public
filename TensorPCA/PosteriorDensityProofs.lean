-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianChannelProofs
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# The normalized likelihood kernel and posterior tensor

The normalized likelihood is an explicit kernel on the physical vector prior.
Its identification with the posterior uses the joint law and
Mathlib's disintegration uniqueness, followed by the conditional-expectation
integral formula. No individual observation is conditioned on as an event.
-/
@[expose] public section

namespace TensorPCA.PosteriorDensityProofs

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace ProbabilityTheory

noncomputable def posteriorWeight (N k : ℕ) (lam : ℝ)
    (y : Model.Tensor N k) (x : Model.Vector N) : ℝ :=
  (Model.likelihoodRatio N k lam y)⁻¹ * GaussianChannelProofs.likelihoodWeight N k lam y x

noncomputable def posteriorKernel (N k : ℕ) (lam : ℝ) :
    Kernel (Model.Tensor N k) (Model.Vector N) :=
  (Kernel.const (Model.Tensor N k) (Model.spherePrior N)).withDensity
    (fun y x ↦ ENNReal.ofReal (posteriorWeight N k lam y x))

theorem measurable_posteriorWeight (N k : ℕ) (lam : ℝ) :
    Measurable (Function.uncurry (fun y x ↦ ENNReal.ofReal (posteriorWeight N k lam y x))) := by
  change Measurable (fun z : Model.Tensor N k × Model.Vector N ↦
    ENNReal.ofReal ((Model.likelihoodRatio N k lam z.1)⁻¹ *
      GaussianChannelProofs.likelihoodWeight N k lam z.1 z.2))
  have hZ : Measurable (fun z : Model.Tensor N k × Model.Vector N ↦
      (Model.likelihoodRatio N k lam z.1)⁻¹) :=
    ((GaussianChannelProofs.measurable_likelihoodRatio N k lam).comp measurable_fst).inv
  have hw : Measurable (fun z : Model.Tensor N k × Model.Vector N ↦
      GaussianChannelProofs.likelihoodWeight N k lam z.1 z.2) :=
    ((GaussianChannelProofs.continuous_joint_likelihoodWeight N k lam).comp continuous_swap).measurable
  exact (hZ.mul hw).ennreal_ofReal

theorem posteriorWeight_pos {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) (x : Model.Vector N) : 0 < posteriorWeight N k lam y x :=
  mul_pos (inv_pos.2 (GaussianChannelProofs.likelihoodRatio_pos hN lam y))
    (GaussianChannelProofs.likelihoodWeight_pos N k lam y x)

theorem integrable_posteriorWeight {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    Integrable (posteriorWeight N k lam y) (Model.spherePrior N) :=
  (GaussianChannelProofs.integrable_likelihoodWeight hN lam y).const_mul _

theorem integral_posteriorWeight_eq_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    (∫ x, posteriorWeight N k lam y x ∂Model.spherePrior N) = 1 := by
  unfold posteriorWeight
  rw [integral_const_mul, ← GaussianChannelProofs.likelihoodRatio_eq_integral_weight,
    inv_mul_cancel₀ (GaussianChannelProofs.likelihoodRatio_pos hN lam y).ne']

theorem posteriorKernel_apply (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) :
    posteriorKernel N k lam y = (Model.spherePrior N).withDensity
      (fun x ↦ ENNReal.ofReal (posteriorWeight N k lam y x)) := by
  rw [posteriorKernel, Kernel.withDensity_apply _ (measurable_posteriorWeight N k lam),
    Kernel.const_apply]

theorem posteriorKernel_isMarkov {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    IsMarkovKernel (posteriorKernel N k lam) := by
  refine ⟨fun y ↦ ⟨?_⟩⟩
  rw [posteriorKernel_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_posteriorWeight hN lam y)
      (Filter.Eventually.of_forall fun x ↦ (posteriorWeight_pos hN lam y x).le),
    integral_posteriorWeight_eq_one hN lam y]
  simp

/-- A concrete weighted tensor integral, before normalization. -/
noncomputable def gibbsTensorNumerator (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) : Model.Tensor N k :=
  ∫ x, GaussianChannelProofs.likelihoodWeight N k lam y x • Model.feature k x ∂Model.spherePrior N

/-- The normalized weighted tensor mean; its equality with the actual conditional
expectation is a theorem below, not part of this definition. -/
noncomputable def gibbsTensorMean (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) : Model.Tensor N k :=
  (Model.likelihoodRatio N k lam y)⁻¹ • gibbsTensorNumerator N k lam y

theorem integrable_gibbsTensorNumerator_integrand {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (y : Model.Tensor N k) :
    Integrable (fun x ↦ GaussianChannelProofs.likelihoodWeight N k lam y x • Model.feature k x)
      (Model.spherePrior N) := by
  have hc := (GaussianChannelProofs.continuous_likelihoodWeight N k lam y).smul
    (Model.continuous_feature N k)
  apply (integrable_const (Real.exp (|lam * Real.sqrt N| * ‖y‖ - N * lam ^ 2 / 2))).mono'
    hc.measurable.aestronglyMeasurable
  filter_upwards [GaussianChannelProofs.likelihoodWeight_le_ae hN lam y,
    Geometry.spherePrior_norm_ae hN] with x hw hx
  simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs,
    abs_of_pos (GaussianChannelProofs.likelihoodWeight_pos N k lam y x),
    Geometry.feature_unit_norm (k := k) x hx, mul_one] using hw

theorem measurable_gibbsTensorNumerator (N k : ℕ) (lam : ℝ) :
    Measurable (gibbsTensorNumerator N k lam) := by
  have hm : StronglyMeasurable (fun z : Model.Tensor N k × Model.Vector N ↦
      GaussianChannelProofs.likelihoodWeight N k lam z.1 z.2 • Model.feature k z.2) :=
    (((GaussianChannelProofs.continuous_joint_likelihoodWeight N k lam).comp continuous_swap).smul
      ((Model.continuous_feature N k).comp continuous_snd)).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := Model.spherePrior N)).measurable

theorem measurable_gibbsTensorMean (N k : ℕ) (lam : ℝ) :
    Measurable (gibbsTensorMean N k lam) := by
  change Measurable (fun y ↦ (Model.likelihoodRatio N k lam y)⁻¹ • gibbsTensorNumerator N k lam y)
  exact Continuous.measurable2 continuous_smul
    (GaussianChannelProofs.measurable_likelihoodRatio N k lam).inv
    (measurable_gibbsTensorNumerator N k lam)

theorem norm_gibbsTensorNumerator_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    ‖gibbsTensorNumerator N k lam y‖ ≤ Model.likelihoodRatio N k lam y := by
  rw [GaussianChannelProofs.likelihoodRatio_eq_integral_weight]
  calc
    _ ≤ ∫ x, ‖GaussianChannelProofs.likelihoodWeight N k lam y x • Model.feature k x‖
        ∂Model.spherePrior N := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_pos (GaussianChannelProofs.likelihoodWeight_pos N k lam y x),
        Geometry.feature_unit_norm (k := k) x hx, mul_one]

theorem norm_gibbsTensorMean_le_one {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    ‖gibbsTensorMean N k lam y‖ ≤ 1 := by
  have hz := GaussianChannelProofs.likelihoodRatio_pos hN lam y
  rw [gibbsTensorMean, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
  calc
    _ ≤ (Model.likelihoodRatio N k lam y)⁻¹ * Model.likelihoodRatio N k lam y :=
      mul_le_mul_of_nonneg_left (norm_gibbsTensorNumerator_le hN lam y) (inv_nonneg.2 hz.le)
    _ = 1 := inv_mul_cancel₀ hz.ne'

theorem integral_feature_posteriorKernel {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    (∫ x, Model.feature k x ∂posteriorKernel N k lam y) = gibbsTensorMean N k lam y := by
  have hw : Measurable (fun x : Model.Vector N ↦ ENNReal.ofReal (posteriorWeight N k lam y x)) :=
    Measurable.of_uncurry_left (x := y) (measurable_posteriorWeight N k lam)
  rw [posteriorKernel_apply,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun x : Model.Vector N ↦ ENNReal.ofReal (posteriorWeight N k lam y x)) hw
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (Model.feature k)]
  have htoReal (x : Model.Vector N) :
      (ENNReal.ofReal (posteriorWeight N k lam y x)).toReal = posteriorWeight N k lam y x :=
    ENNReal.toReal_ofReal (posteriorWeight_pos hN lam y x).le
  simp_rw [htoReal, posteriorWeight, mul_smul]
  rw [integral_smul]
  rfl

theorem observedLatent_map_eq_withDensity {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (Model.experimentLaw N k).map (fun z ↦ (Model.observation lam z, z.1)) =
      ((Model.noiseLaw N k).prod (Model.spherePrior N)).withDensity
        (fun z ↦ ENNReal.ofReal (GaussianChannelProofs.likelihoodWeight N k lam z.1 z.2)) := by
  have hObs : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      (z.1, Model.observation lam z)) := measurable_fst.prodMk (Model.measurable_observation N k lam)
  have hd := GaussianChannelProofs.map_withDensity_equiv
    (MeasurableEquiv.prodComm : Model.Vector N × Model.Tensor N k ≃ᵐ Model.Tensor N k × Model.Vector N)
    (Model.experimentLaw N k)
    (fun z ↦ ENNReal.ofReal (GaussianChannelProofs.likelihoodWeight N k lam z.2 z.1))
    (GaussianChannelProofs.continuous_joint_likelihoodWeight N k lam).measurable.ennreal_ofReal
  rw [← GaussianChannelProofs.jointObservation_map_eq_withDensity hN lam,
    Measure.map_map MeasurableEquiv.prodComm.measurable hObs] at hd
  change (Model.experimentLaw N k).map (fun z ↦ (Model.observation lam z, z.1)) =
    ((Model.experimentLaw N k).map Prod.swap).withDensity
      (fun z ↦ ENNReal.ofReal (GaussianChannelProofs.likelihoodWeight N k lam z.1 z.2)) at hd
  simpa only [Model.experimentLaw, Measure.prod_swap] using hd

/-- The explicit normalized likelihood kernel reconstructs the actual joint
law of observation and planted vector. -/
theorem observation_compProd_posteriorKernel {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (Model.observationLaw N k lam) ⊗ₘ (posteriorKernel N k lam) =
      (Model.experimentLaw N k).map (fun z ↦ (Model.observation lam z, z.1)) := by
  have : IsMarkovKernel ((Kernel.const (Model.Tensor N k) (Model.spherePrior N)).withDensity
      (fun y x ↦ ENNReal.ofReal (posteriorWeight N k lam y x))) := posteriorKernel_isMarkov hN lam
  rw [GaussianChannelProofs.observationLaw_eq_withDensity hN lam, posteriorKernel,
    Measure.withDensity_compProd_withDensity
      (GaussianChannelProofs.measurable_likelihoodRatio N k lam).ennreal_ofReal
      (measurable_posteriorWeight N k lam), Measure.compProd_const,
    observedLatent_map_eq_withDensity hN lam]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (GaussianChannelProofs.likelihoodRatio_pos hN lam z.1).le]
  congr 1
  rw [posteriorWeight, ← mul_assoc,
    mul_inv_cancel₀ (GaussianChannelProofs.likelihoodRatio_pos hN lam z.1).ne', one_mul]

theorem condDistrib_eq_posteriorKernel {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    condDistrib (Prod.fst : Model.Vector N × Model.Tensor N k → Model.Vector N)
      (Model.observation lam) (Model.experimentLaw N k) =ᵐ[Model.observationLaw N k lam]
      posteriorKernel N k lam := by
  have : IsMarkovKernel (posteriorKernel N k lam) := posteriorKernel_isMarkov hN lam
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (Model.measurable_observation N k lam) measurable_fst
    (observation_compProd_posteriorKernel hN lam).symm

/-- The explicit Gibbs tensor mean is the reviewed conditional expectation
given the actual observation σ-algebra, under the actual experiment law. -/
theorem gibbsTensorMean_ae_eq_posteriorTensor {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (fun z : Model.Vector N × Model.Tensor N k ↦ gibbsTensorMean N k lam (Model.observation lam z))
      =ᵐ[Model.experimentLaw N k] Model.posteriorTensor N k lam := by
  have hce : Model.posteriorTensor N k lam =ᵐ[Model.experimentLaw N k]
      (fun z ↦ ∫ x, Model.feature k x ∂condDistrib
        (Prod.fst : Model.Vector N × Model.Tensor N k → Model.Vector N)
        (Model.observation lam) (Model.experimentLaw N k) (Model.observation lam z)) :=
    condExp_ae_eq_integral_condDistrib (Model.measurable_observation N k lam)
      measurable_fst.aemeasurable (Model.continuous_feature N k).stronglyMeasurable
      ((PosteriorProofs.latent_memLp_two (k := k) hN).integrable (by norm_num))
  have hk := ae_of_ae_map (Model.measurable_observation N k lam).aemeasurable
    (condDistrib_eq_posteriorKernel hN lam)
  filter_upwards [hce, hk] with z hcz hkz
  rw [hcz, hkz, integral_feature_posteriorKernel hN lam]


end TensorPCA.PosteriorDensityProofs
