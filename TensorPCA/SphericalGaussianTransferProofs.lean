-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianMixtureStabilityProofs
public import TensorPCA.Statistical

/-!
# Spherical/Gaussian tensor-prior free-energy transfer

The common latent variable is an N-dimensional standard Gaussian. One
feature uses G/sqrt(N), the other its radial normalization. Channel scaling is
sqrt(gamma)*sqrt(N), and free energy is divided by physical N.
-/
@[expose] public section

namespace TensorPCA.SphericalGaussianTransferProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
  GaussianMixtureStabilityProofs Filter
open scoped ENNReal RealInnerProductSpace Topology

noncomputable def gaussianFeature (N k : ℕ) (g : Model.Vector N) : Model.Tensor N k :=
  Model.feature k ((Real.sqrt N)⁻¹ • g)

noncomputable def sphericalFeature (N k : ℕ) (g : Model.Vector N) : Model.Tensor N k :=
  Model.feature k (Model.normalize g)

noncomputable def gaussianPriorFreeEnergy (N k : ℕ) (gamma : ℝ) : ℝ :=
  mixtureFreeEnergy (stdGaussian (Model.Vector N))
    (fun g ↦ (Real.sqrt gamma * Real.sqrt N) • gaussianFeature N k g) / N

theorem measurable_gaussianFeature (N k : ℕ) : Measurable (gaussianFeature N k) :=
  (Model.continuous_feature N k).measurable.comp (continuous_const_smul ((Real.sqrt N)⁻¹)).measurable

theorem measurable_sphericalFeature (N k : ℕ) : Measurable (sphericalFeature N k) :=
  (Model.continuous_feature N k).measurable.comp (Model.measurable_normalize N)

theorem sphericalFeature_norm_ae {N k : ℕ} (hN : 0 < N) :
    ∀ᵐ g ∂stdGaussian (Model.Vector N), ‖sphericalFeature N k g‖ = 1 :=
  (Geometry.gaussian_ne_zero_ae hN).mono fun g hg ↦
    Geometry.feature_unit_norm (Model.normalize g) (Model.norm_normalize g hg)

theorem sphericalFeature_memLp_two {N k : ℕ} (hN : 0 < N) :
    MemLp (sphericalFeature N k) 2 (stdGaussian (Model.Vector N)) :=
  MemLp.of_bound (measurable_sphericalFeature N k).aestronglyMeasurable 1
    ((sphericalFeature_norm_ae hN).mono fun _g hg ↦ hg.le)

theorem feature_discrepancy_memLp_two {N k : ℕ} (hN : 0 < N) :
    MemLp (fun g ↦ gaussianFeature N k g-sphericalFeature N k g) 2
      (stdGaussian (Model.Vector N)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((measurable_gaussianFeature N k).sub (measurable_sphericalFeature N k)).aestronglyMeasurable).mpr
  exact GaussianMomentProofs.tensor_radial_error_integrable hN k

theorem gaussianFeature_memLp_two {N k : ℕ} (hN : 0 < N) :
    MemLp (gaussianFeature N k) 2 (stdGaussian (Model.Vector N)) := by
  have h := (feature_discrepancy_memLp_two (k := k) hN).add (sphericalFeature_memLp_two (k := k) hN)
  have heq : ((fun g ↦ gaussianFeature N k g-sphericalFeature N k g) + sphericalFeature N k) =
      gaussianFeature N k := by funext g; exact sub_add_cancel _ _
  exact heq ▸ h

theorem mixtureLaw_map_prior {Omega Delta E : Type*} [MeasurableSpace Omega] [MeasurableSpace Delta]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure Omega) (f : Omega → Delta)
    (hf : Measurable f) (F : Delta → E) (hF : Measurable F) :
    mixtureLaw (mu.map f) F = mixtureLaw mu (F ∘ f) := by
  have hp : (mu.map f).prod (stdGaussian E) =
      (mu.prod (stdGaussian E)).map (Prod.map f id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map mu (stdGaussian E) hf measurable_id
  have hObs : Measurable (fun z : Delta × E ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  rw [mixtureLaw, hp, Measure.map_map hObs (hf.prodMap measurable_id)]
  rfl

theorem spherical_mixtureLaw (N k : ℕ) (lam : ℝ) :
    mixtureLaw (stdGaussian (Model.Vector N)) (fun g ↦ (lam * Real.sqrt N) • sphericalFeature N k g) =
      Model.observationLaw N k lam := by
  have h := mixtureLaw_map_prior (stdGaussian (Model.Vector N)) Model.normalize
    (Model.measurable_normalize N) (fun x ↦ (lam * Real.sqrt N) • Model.feature k x)
    ((Model.continuous_feature N k).fun_const_smul (lam * Real.sqrt N)).measurable
  exact h.symm

theorem actualFreeEnergy_eq_klDiv {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (klDiv (Model.observationLaw N k lam) (Model.noiseLaw N k)).toReal =
      ∫ z, Real.log (Model.likelihoodRatio N k lam (Model.observation lam z)) ∂Model.experimentLaw N k := by
  have hAC : Model.observationLaw N k lam ≪ Model.noiseLaw N k := by
    rw [GaussianChannelProofs.observationLaw_eq_withDensity hN lam]
    exact withDensity_absolutelyContinuous _ _
  have hRN := Measure.rnDeriv_withDensity (Model.noiseLaw N k)
    (GaussianChannelProofs.measurable_likelihoodRatio N k lam).ennreal_ofReal
  rw [← GaussianChannelProofs.observationLaw_eq_withDensity hN lam] at hRN
  have hllr : llr (Model.observationLaw N k lam) (Model.noiseLaw N k) =ᵐ[
      Model.observationLaw N k lam] fun y ↦ Real.log (Model.likelihoodRatio N k lam y) := by
    filter_upwards [hRN.filter_mono hAC.ae_le] with y hy
    rw [llr, hy, ENNReal.toReal_ofReal (GaussianChannelProofs.likelihoodRatio_pos hN lam y).le]
  rw [toReal_klDiv_of_measure_eq hAC (by simp), integral_congr_ae hllr,
    Model.observationLaw, integral_map (Model.measurable_observation N k lam).aemeasurable
      (GaussianChannelProofs.measurable_likelihoodRatio N k lam).log.aestronglyMeasurable]

theorem spherical_freeEnergy_eq {N k : ℕ} (hN : 0 < N) (gamma : ℝ) :
    mixtureFreeEnergy (stdGaussian (Model.Vector N))
      (fun g ↦ (Real.sqrt gamma * Real.sqrt N) • sphericalFeature N k g) / N =
        Statistical.sphericalBayesFreeEnergy N k gamma := by
  rw [mixtureFreeEnergy, spherical_mixtureLaw]
  exact congrArg (fun t : ℝ ↦ t / N) (actualFreeEnergy_eq_klDiv hN (Real.sqrt gamma))

theorem integral_feature_discrepancy_norm_le {N k : ℕ} (hN : 0 < N) :
    (∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ∂stdGaussian (Model.Vector N)) ≤
      Real.sqrt (∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ^ 2
        ∂stdGaussian (Model.Vector N)) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := stdGaussian (Model.Vector N)) (p := 2) (q := 2)
    (f := fun g ↦ ‖gaussianFeature N k g-sphericalFeature N k g‖) (g := fun _ ↦ (1 : ℝ))
    (by norm_num [Real.holderConjugate_iff])
    (.of_forall fun _ ↦ norm_nonneg _) (.of_forall fun _ ↦ zero_le_one)
    (by simpa using (feature_discrepancy_memLp_two (k := k) hN).norm)
    (by simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : Model.Vector N ↦ (1 : ℝ)) 2 (stdGaussian (Model.Vector N))))
  rw [Real.sqrt_eq_rpow]
  simpa [Real.rpow_two] using h

/-- Quantitative transfer with the actual normalized Gaussian tensor prior.
The feature coupling is inside the integral and needs no radius-angle
independence assumption. -/
theorem freeEnergy_transfer_bound {N k : ℕ} (hN : 0 < N) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    |gaussianPriorFreeEnergy N k gamma-Statistical.sphericalBayesFreeEnergy N k gamma| ≤
      gamma * Real.sqrt (∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ^ 2
        ∂stdGaussian (Model.Vector N)) +
      gamma / 2 * ∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ^ 2
        ∂stdGaussian (Model.Vector N) := by
  let t := Real.sqrt gamma * Real.sqrt N
  let F := t • gaussianFeature N k
  let G := t • sphericalFeature N k
  have ht : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg gamma) (Real.sqrt_nonneg N)
  have hF : Measurable F := (measurable_gaussianFeature N k).const_smul t
  have hG : Measurable G := (measurable_sphericalFeature N k).const_smul t
  have hF2 : MemLp F 2 (stdGaussian (Model.Vector N)) := (gaussianFeature_memLp_two hN).const_smul t
  have hG2 : MemLp G 2 (stdGaussian (Model.Vector N)) := (sphericalFeature_memLp_two hN).const_smul t
  have hGb : ∀ᵐ g ∂stdGaussian (Model.Vector N), ‖G g‖ ≤ t := by
    filter_upwards [sphericalFeature_norm_ae (k := k) hN] with g hg
    change ‖t • sphericalFeature N k g‖ ≤ t
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hg, mul_one, le_refl]
  have hstab := abs_mixtureFreeEnergy_sub_le (stdGaussian (Model.Vector N)) F G hF hG hF2 hG2 hGb
  have hnorm (g : Model.Vector N) : ‖F g-G g‖ = t * ‖gaussianFeature N k g-sphericalFeature N k g‖ := by
    change ‖t • gaussianFeature N k g-t • sphericalFeature N k g‖ = _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  simp_rw [hnorm, mul_pow] at hstab
  rw [integral_const_mul, integral_const_mul] at hstab
  have ht2 : t ^ 2 = gamma * (N : ℝ) := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt hgamma, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hraw : |gaussianPriorFreeEnergy N k gamma-Statistical.sphericalBayesFreeEnergy N k gamma| ≤
      gamma * (∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ∂stdGaussian (Model.Vector N)) +
      gamma / 2 * ∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ^ 2
        ∂stdGaussian (Model.Vector N) := by
    rw [gaussianPriorFreeEnergy, ← spherical_freeEnergy_eq hN gamma, ← sub_div, abs_div,
      abs_of_pos hNpos]
    apply (div_le_iff₀ hNpos).mpr
    calc
      _ ≤ _ := hstab
      _ = _ := by
        calc
          _ = t ^ 2 * ((∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖
              ∂stdGaussian (Model.Vector N)) +
              (∫ g, ‖gaussianFeature N k g-sphericalFeature N k g‖ ^ 2
                ∂stdGaussian (Model.Vector N)) / 2) := by ring
          _ = _ := by rw [ht2]; ring
  exact hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_left (integral_feature_discrepancy_norm_le hN) hgamma) le_rfl)

/-- Spherical and normalized Gaussian tensor priors have the same limiting
free energy at every fixed nonnegative strength. This transfers values only;
it does not assume or prove the separate nonlinear Gaussian-prior limit. -/
theorem gaussianPriorFreeEnergy_sub_spherical_tendsto (k : ℕ) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    Tendsto (fun n : ℕ ↦ gaussianPriorFreeEnergy (n+1) k gamma -
      Statistical.sphericalBayesFreeEnergy (n+1) k gamma) atTop (𝓝 0) := by
  have he := GaussianMomentProofs.tensor_radial_error_tendsto k
  have hb := ((he.sqrt).const_mul gamma).add (he.const_mul (gamma / 2))
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hb
  apply squeeze_zero_norm _ hb
  intro n
  exact freeEnergy_transfer_bound (Nat.succ_pos n) hgamma


end TensorPCA.SphericalGaussianTransferProofs
