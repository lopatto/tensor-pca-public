-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Model
public import TensorPCA.GaussianDensityProofs
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The angular law and radial/angular independence of the Gaussian.
The polar homeomorphism is only used off the origin; the ambient direction map
retains the manuscript's total value zero at the origin. -/
@[expose] public section
namespace TensorPCA.SpherePolarProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem measurePreserving_withDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {μ : Measure X} {ν : Measure Y} (hf : MeasurePreserving f μ ν)
    (ρ : Y → ℝ≥0∞) (hρ : Measurable ρ) :
    MeasurePreserving f (μ.withDensity (ρ ∘ f)) (ν.withDensity ρ) := by
  refine ⟨hf.measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hf.measurable]
  change (∫⁻ a, (g ∘ f) a ∂μ.withDensity (ρ ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hρ.comp hf.measurable) (hg.comp hf.measurable),
    lintegral_withDensity_eq_lintegral_mul ν hρ hg]
  simpa only [Function.comp_def, Pi.mul_apply] using hf.lintegral_comp (hρ.mul hg)

section General
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

abbrev Sphere := Metric.sphere (0 : E) 1
abbrev PositiveRadius := Ioi (0 : ℝ)

def surfaceMeasure : Measure (Sphere E) := (volume : Measure E).toSphere

def radialPowerMeasure : Measure PositiveRadius := Measure.volumeIoiPow (Module.finrank ℝ E-1)

def radialWeight (r : PositiveRadius) : ℝ≥0∞ :=
  ENNReal.ofReal (GaussianDensityProofs.normalizer E * Real.exp (-(1/2 : ℝ)*(r.1)^2))

def weightedRadius : Measure PositiveRadius := (radialPowerMeasure E).withDensity (radialWeight E)

def polarExpand (p : Sphere E × PositiveRadius) : E := p.2.1 • p.1.1

def direction (x : E) : E := ‖x‖⁻¹ • x

omit [Nontrivial E] in
theorem measurable_direction : Measurable (direction E) := by
  unfold direction
  exact measurable_norm.inv.smul measurable_id

omit [Nontrivial E] in
theorem measurable_polarExpand : Measurable (polarExpand E) := by
  unfold polarExpand
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem measurable_radialWeight : Measurable (radialWeight E) := by
  unfold radialWeight
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem norm_polarExpand (p : Sphere E × PositiveRadius) : ‖polarExpand E p‖ = p.2.1 := by
  have hu : ‖(p.1 : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property
  simp only [polarExpand, norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property, hu, mul_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem direction_polarExpand (p : Sphere E × PositiveRadius) : direction E (polarExpand E p) = p.1.1 := by
  unfold direction
  rw [norm_polarExpand, polarExpand, smul_smul, inv_mul_cancel₀ p.2.property.ne', one_smul]

instance surfaceMeasure_finite : IsFiniteMeasure (surfaceMeasure E) := by
  unfold surfaceMeasure
  infer_instance

instance radialPowerMeasure_sigmaFinite : SigmaFinite (radialPowerMeasure E) := by
  unfold radialPowerMeasure
  infer_instance

instance weightedRadius_sfinite : SFinite (weightedRadius E) := by
  unfold weightedRadius
  infer_instance

theorem surfaceMeasure_ne_zero : surfaceMeasure E ≠ 0 := by
  exact Measure.toSphere_ne_zero (volume : Measure E)

/-- Canonical Haar polar integration as a measure-preserving map into the
ambient space. Removing the origin is harmless because Haar gives it mass zero. -/
theorem polarExpand_preserves_volume :
    MeasurePreserving (polarExpand E) ((surfaceMeasure E).prod (radialPowerMeasure E))
      (volume : Measure E) := by
  let e := (homeomorphUnitSphereProd E).toMeasurableEquiv
  have he : MeasurePreserving e ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      ((surfaceMeasure E).prod (radialPowerMeasure E)) :=
    Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
  have hi : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
      ((volume : Measure E).comap Subtype.val) volume := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton (0 : E)).compl]
    exact restrict_compl_singleton (0 : E)
  have h := hi.comp (MeasurePreserving.symm e he)
  have hfun : (Subtype.val ∘ e.symm) = polarExpand E := by
    funext p
    simp [e, polarExpand, homeomorphUnitSphereProd_symm_apply_coe]
  rwa [hfun] at h

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem density_polarExpand (p : Sphere E × PositiveRadius) :
    ENNReal.ofReal (GaussianDensityProofs.density (polarExpand E p)) = radialWeight E p.2 := by
  simp only [GaussianDensityProofs.density, norm_polarExpand, radialWeight]

/-- The actual standard Gaussian is the image of the Haar surface measure and
the Gaussian-weighted radial power measure. Neither factor is assumed normalized. -/
theorem polarExpand_preserves_gaussian :
    MeasurePreserving (polarExpand E) ((surfaceMeasure E).prod (weightedRadius E))
      (stdGaussian E) := by
  have h := measurePreserving_withDensity (polarExpand_preserves_volume E)
    (fun x : E ↦ ENNReal.ofReal (GaussianDensityProofs.density x))
    GaussianDensityProofs.density_continuous.measurable.ennreal_ofReal
  rw [← GaussianDensityProofs.stdGaussian_eq_withDensity] at h
  have hs : (surfaceMeasure E).prod (weightedRadius E) =
      ((surfaceMeasure E).prod (radialPowerMeasure E)).withDensity
        ((fun x : E ↦ ENNReal.ofReal (GaussianDensityProofs.density x)) ∘ polarExpand E) := by
    rw [weightedRadius, prod_withDensity_right (measurable_radialWeight E)]
    apply withDensity_congr_ae
    exact Eventually.of_forall fun p ↦ (density_polarExpand E p).symm
  rwa [hs]

instance polarProduct_probability :
    IsProbabilityMeasure ((surfaceMeasure E).prod (weightedRadius E)) := by
  have h := polarExpand_preserves_gaussian E
  have : IsProbabilityMeasure
      (((surfaceMeasure E).prod (weightedRadius E)).map (polarExpand E)) := by
    rw [h.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map h.measurable.aemeasurable

theorem surfaceMeasure_mass_ne_zero : surfaceMeasure E univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 (surfaceMeasure_ne_zero E)

omit [Nontrivial E] in
theorem surfaceMeasure_mass_ne_top : surfaceMeasure E univ ≠ ∞ := measure_ne_top _ _

/-- Haar surface probability on the sphere subtype. -/
def normalizedSurface : Measure (Sphere E) :=
  (surfaceMeasure E univ)⁻¹ • surfaceMeasure E

/-- The radial probability, with its normalization fixed by the actual
Gaussian product mass, rather than by a gamma-function identity. -/
def normalizedRadius : Measure PositiveRadius :=
  surfaceMeasure E univ • weightedRadius E

instance normalizedSurface_probability : IsProbabilityMeasure (normalizedSurface E) where
  measure_univ := by
    rw [normalizedSurface, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (surfaceMeasure_mass_ne_zero E) (surfaceMeasure_mass_ne_top E)

instance normalizedRadius_probability : IsProbabilityMeasure (normalizedRadius E) where
  measure_univ := by
    rw [normalizedRadius, Measure.smul_apply, smul_eq_mul]
    have h := measure_univ (μ := (surfaceMeasure E).prod (weightedRadius E))
    simpa only [← univ_prod_univ, Measure.prod_prod] using h

theorem normalized_product :
    (normalizedSurface E).prod (normalizedRadius E) =
      (surfaceMeasure E).prod (weightedRadius E) := by
  rw [normalizedSurface, normalizedRadius, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ENNReal.inv_mul_cancel (surfaceMeasure_mass_ne_zero E)
      (surfaceMeasure_mass_ne_top E), one_smul]

theorem polarExpand_preserves_gaussian_probability :
    MeasurePreserving (polarExpand E) ((normalizedSurface E).prod (normalizedRadius E))
      (stdGaussian E) := by
  rw [normalized_product]
  exact polarExpand_preserves_gaussian E

/-- Ambient version of normalized Haar sphere probability. It is distinct from
the measure on the sphere subtype, though the inclusion is measure-preserving. -/
def angularLaw : Measure E := (normalizedSurface E).map Subtype.val

def radialLaw : Measure ℝ := (normalizedRadius E).map Subtype.val

instance angularLaw_probability : IsProbabilityMeasure (angularLaw E) := by
  unfold angularLaw
  infer_instance

instance radialLaw_probability : IsProbabilityMeasure (radialLaw E) := by
  unfold radialLaw
  infer_instance

/-- The actual joint Gaussian direction/radius law, including its ambient
zero-origin convention. The polar map itself is used only at positive radii. -/
theorem stdGaussian_direction_norm_law :
    (stdGaussian E).map (fun x ↦ (direction E x, ‖x‖)) =
      (angularLaw E).prod (radialLaw E) := by
  rw [← (polarExpand_preserves_gaussian_probability E).map_eq,
    Measure.map_map ((measurable_direction E).prodMk measurable_norm)
      (measurable_polarExpand E)]
  have hfun : (fun x : E ↦ (direction E x, ‖x‖)) ∘ polarExpand E =
      Prod.map (Subtype.val : Sphere E → E) (Subtype.val : PositiveRadius → ℝ) := by
    funext p
    exact Prod.ext (direction_polarExpand E p) (norm_polarExpand E p)
  rw [hfun]
  exact (Measure.map_prod_map (normalizedSurface E) (normalizedRadius E)
    measurable_subtype_coe measurable_subtype_coe).symm

theorem stdGaussian_direction_law :
    (stdGaussian E).map (direction E) = angularLaw E := by
  have h := congrArg (Measure.map Prod.fst) (stdGaussian_direction_norm_law E)
  simpa only [Measure.map_map measurable_fst
      ((measurable_direction E).prodMk measurable_norm),
    Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h

theorem stdGaussian_norm_law :
    (stdGaussian E).map (fun x ↦ ‖x‖) = radialLaw E := by
  have h := congrArg (Measure.map Prod.snd) (stdGaussian_direction_norm_law E)
  simpa only [Measure.map_map measurable_snd
      ((measurable_direction E).prodMk measurable_norm),
    Function.comp_def, Measure.map_snd_prod, measure_univ, one_smul] using h

theorem stdGaussian_direction_indep_norm :
    IndepFun (direction E) (fun x : E ↦ ‖x‖) (stdGaussian E) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (measurable_direction E).aemeasurable measurable_norm.aemeasurable,
    stdGaussian_direction_law, stdGaussian_norm_law]
  exact stdGaussian_direction_norm_law E

/-- Independently sampling the Haar direction and the actual Gaussian radius
reconstructs the actual Gaussian by ordinary scalar multiplication. -/
theorem gaussian_radial_reconstruction :
    MeasurePreserving (fun p : E × ℝ ↦ p.2 • p.1)
      ((angularLaw E).prod (radialLaw E)) (stdGaussian E) := by
  refine ⟨measurable_snd.smul measurable_fst, ?_⟩
  rw [angularLaw, radialLaw, Measure.map_prod_map (normalizedSurface E)
    (normalizedRadius E) measurable_subtype_coe measurable_subtype_coe,
    Measure.map_map (show Measurable (fun p : E × ℝ ↦ p.2 • p.1) by fun_prop)
      (measurable_subtype_coe.prodMap measurable_subtype_coe)]
  exact (polarExpand_preserves_gaussian_probability E).map_eq

end General

/-- The paper's concrete prior is exactly ambient normalized Haar sphere
probability in every positive dimension, including dimension one. -/
theorem spherePrior_eq_angularLaw {N : ℕ} (hN : 0 < N) :
    Model.spherePrior N = angularLaw (Model.Vector N) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact stdGaussian_direction_law (Model.Vector N)

theorem normalize_indep_norm {N : ℕ} (hN : 0 < N) :
    IndepFun (Model.normalize (N := N)) (fun x : Model.Vector N ↦ ‖x‖)
      (stdGaussian (Model.Vector N)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact stdGaussian_direction_indep_norm (Model.Vector N)

theorem spherePrior_gaussian_radial_reconstruction {N : ℕ} (hN : 0 < N) :
    MeasurePreserving (fun p : Model.Vector N × ℝ ↦ p.2 • p.1)
      ((Model.spherePrior N).prod
        ((stdGaussian (Model.Vector N)).map (fun x ↦ ‖x‖)))
      (stdGaussian (Model.Vector N)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [spherePrior_eq_angularLaw hN, stdGaussian_norm_law]
  exact gaussian_radial_reconstruction (Model.Vector N)

end
end TensorPCA.SpherePolarProofs
