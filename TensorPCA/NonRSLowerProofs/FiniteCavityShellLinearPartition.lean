-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceLaw
public import TensorPCA.RetainedCountProofs.SphereLinear

/-! A finite lower bound for the Gaussian-annulus linear partition. The comparison
sphere has radius sqrt(M), and its normalized angular prior is exactly
Model.spherePrior M. No field-norm or free-energy premise is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityShellLinearPartition
open MeasureTheory ProbabilityTheory Set
open FiniteCavityReferenceLaw
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def gaussianAnnulus (M : ℕ) (delta : ℝ) : Set (Model.Vector M) :=
  {eta | (M : ℝ)≤‖eta‖^2 ∧ ‖eta‖^2≤(M : ℝ)*(1+delta)}

private def radiusAnnulus (M : ℕ) (delta : ℝ) : Set ℝ :=
  {r | (M : ℝ)≤r^2 ∧ r^2≤(M : ℝ)*(1+delta)}

theorem gaussianAnnulus_measurableSet (M : ℕ) (delta : ℝ) : MeasurableSet (gaussianAnnulus M delta) :=
  (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet.inter
    (isClosed_le (continuous_norm.pow 2) continuous_const).measurableSet

private theorem radiusAnnulus_measurableSet (M : ℕ) (delta : ℝ) : MeasurableSet (radiusAnnulus M delta) :=
  (isClosed_le continuous_const (continuous_id.pow 2)).measurableSet.inter
    (isClosed_le (continuous_id.pow 2) continuous_const).measurableSet

private theorem spherePrior_eq_directionLaw {M : ℕ} (hM : 0<M) :
    Model.spherePrior M=RetainedCountProofs.SphereLinear.directionLaw (Model.Vector M) := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  rw [Model.spherePrior,RetainedCountProofs.SphereLinear.directionLaw_eq_gaussian]
  congr 1
  funext x
  simp only [RetainedCountProofs.SphereVolume.normalize,one_div,Model.normalize]

theorem angular_linear_partition_mono {M : ℕ} (hM : 0<M) (h : Model.Vector M)
    {r s : ℝ} (hr : 0≤r) (hrs : r≤s) :
    (∫u,Real.exp (inner ℝ h (r • u))∂Model.spherePrior M)≤
      ∫u,Real.exp (inner ℝ h (s • u))∂Model.spherePrior M := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  simp only [real_inner_smul_right,spherePrior_eq_directionLaw hM]
  exact RetainedCountProofs.SphereLinear.partition_mono_radius h hr hrs

private theorem radius_annulus_mass (M : ℕ) (delta : ℝ) :
    (radiusLaw M).real (radiusAnnulus M delta)=
      (stdGaussian (Model.Vector M)).real (gaussianAnnulus M delta) := by
  change (((stdGaussian (Model.Vector M)).map (fun g => ‖g‖)) (radiusAnnulus M delta)).toReal=_
  rw [Measure.map_apply measurable_norm (radiusAnnulus_measurableSet M delta)]
  rfl

theorem gaussian_annulus_linear_partition_lower {M : ℕ} (hM : 0<M) (delta : ℝ)
    (hdelta : 0≤delta) (h : Model.Vector M) :
    (stdGaussian (Model.Vector M)).real (gaussianAnnulus M delta)*
        (∫u,Real.exp (inner ℝ h (Real.sqrt (M : ℝ) • u))∂Model.spherePrior M)≤
      ∫eta in gaussianAnnulus M delta,Real.exp (inner ℝ h eta)∂stdGaussian (Model.Vector M) := by
  let A := gaussianAnnulus M delta
  let S := radiusAnnulus M delta
  let F : Model.Vector M→ℝ := A.indicator (fun eta => Real.exp (inner ℝ h eta))
  let P : ℝ→ℝ := fun r => ∫u,Real.exp (inner ℝ h (r • u))∂Model.spherePrior M
  have hA : MeasurableSet A := gaussianAnnulus_measurableSet M delta
  have hS : MeasurableSet S := radiusAnnulus_measurableSet M delta
  have hExp : Integrable (fun eta => Real.exp (inner ℝ h eta)) (stdGaussian (Model.Vector M)) := by
    rw [← GaussianDensityProofs.densityLaw_eq_stdGaussian]
    exact GaussianDensityProofs.densityLaw_exp_integrable h
  have hF : Integrable F (stdGaussian (Model.Vector M)) := hExp.indicator hA
  have hRecon : MeasurePreserving (fun p : Model.Vector M×ℝ => p.2 • p.1)
      ((Model.spherePrior M).prod (radiusLaw M)) (stdGaussian (Model.Vector M)) :=
    SpherePolarProofs.spherePrior_gaussian_radial_reconstruction hM
  have hFP : Integrable (fun p : Model.Vector M×ℝ => F (p.2 • p.1))
      ((Model.spherePrior M).prod (radiusLaw M)) := hRecon.integrable_comp_of_integrable hF
  have hInner (r : ℝ) : (∫u,F (r • u)∂Model.spherePrior M)=S.indicator P r := by
    have hpoint : ∀ᵐ u∂Model.spherePrior M,F (r • u)=
        S.indicator (fun r => Real.exp (inner ℝ h (r • u))) r := by
      filter_upwards [Geometry.spherePrior_norm_ae hM] with u hu
      have hnorm : ‖r • u‖^2=r^2 := by
        rw [norm_smul,Real.norm_eq_abs,hu,mul_one,sq_abs]
      have hmem : r • u∈A↔r∈S := by
        change ((M : ℝ)≤‖r • u‖^2 ∧ ‖r • u‖^2≤(M : ℝ)*(1+delta))↔
          ((M : ℝ)≤r^2 ∧ r^2≤(M : ℝ)*(1+delta))
        rw [hnorm]
      dsimp only [F]
      by_cases hrc : r∈S
      · rw [Set.indicator_of_mem (hmem.2 hrc),Set.indicator_of_mem hrc]
      · rw [Set.indicator_of_notMem (fun huA => hrc (hmem.1 huA)),Set.indicator_of_notMem hrc]
    rw [integral_congr_ae hpoint]
    by_cases hrc : r∈S
    · simp only [Set.indicator_of_mem hrc,P]
    · simp only [Set.indicator_of_notMem hrc,integral_zero]
  have hRadial : Integrable (S.indicator P) (radiusLaw M) := by
    have hi := hFP.integral_prod_right
    simpa only [hInner] using hi
  have hIntegral : (∫eta in A,Real.exp (inner ℝ h eta)∂stdGaussian (Model.Vector M))=
      ∫r,S.indicator P r∂radiusLaw M := by
    rw [← integral_indicator hA]
    change (∫eta,F eta∂stdGaussian (Model.Vector M))=_
    have hFmap : AEStronglyMeasurable F
        (((Model.spherePrior M).prod (radiusLaw M)).map (fun p => p.2 • p.1)) := by
      rw [hRecon.map_eq]
      exact hF.aestronglyMeasurable
    have hm := integral_map hRecon.measurable.aemeasurable hFmap
    rw [hRecon.map_eq] at hm
    rw [hm,integral_prod_symm _ hFP]
    exact integral_congr_ae (.of_forall hInner)
  have hConst : Integrable (S.indicator (fun _ => P (Real.sqrt (M : ℝ)))) (radiusLaw M) :=
    (integrable_const _).indicator hS
  have hLower := integral_mono_ae hConst hRadial (show ∀ᵐ r∂radiusLaw M,
      S.indicator (fun _ => P (Real.sqrt (M : ℝ))) r≤S.indicator P r from by
    filter_upwards [radiusLaw_pos_ae hM] with r hr
    by_cases hrs : r∈S
    · rw [Set.indicator_of_mem hrs,Set.indicator_of_mem hrs]
      apply angular_linear_partition_mono hM h (Real.sqrt_nonneg _)
      exact (Real.sqrt_le_left hr.le).2 hrs.1
    · rw [Set.indicator_of_notMem hrs,Set.indicator_of_notMem hrs])
  rw [integral_indicator_const _ hS,smul_eq_mul,radius_annulus_mass M delta] at hLower
  rw [hIntegral]
  exact hLower


end
end TensorPCA.NonRSLowerProofs.FiniteCavityShellLinearPartition
