-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedMass
public import Mathlib.Probability.ConditionalProbability

/-! The normalized retained reference prior. Both independent radial restrictions retain
their true outside masses.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityRetainedPrior
open MeasureTheory ProbabilityTheory Set
open FiniteCavityReferenceLaw FiniteCavityRetainedMass FiniteCavityShellLinearPartition
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def retainedRegion (N M : ℕ) (e delta : ℝ) : Set (Model.Vector N×(ℝ×Model.Vector M)) :=
  Set.univ ×ˢ (radiusBox N e ×ˢ gaussianAnnulus M delta)

def retainedPrior (N M : ℕ) (e delta : ℝ) : Measure (Model.Vector N×(ℝ×Model.Vector M)) :=
  (Model.spherePrior N).prod
    ((ProbabilityTheory.cond (radiusLaw N) (radiusBox N e)).prod
      (ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)))

instance retainedPrior_finite (N M : ℕ) (e delta : ℝ) : IsFiniteMeasure (retainedPrior N M e delta) := by
  unfold retainedPrior
  infer_instance

theorem retainedRegion_measurableSet (N M : ℕ) (e delta : ℝ) :
    MeasurableSet (retainedRegion N M e delta) :=
  MeasurableSet.univ.prod ((radiusBox_measurableSet N e).prod (gaussianAnnulus_measurableSet M delta))

theorem retainedPrior_probability {N M : ℕ} (hN : 0<N) (hM : 0<M)
    {e delta : ℝ} (he : 0<e) (hdelta : 0<delta) : IsProbabilityMeasure (retainedPrior N M e delta) := by
  have hR : (radiusLaw N) (radiusBox N e) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (radiusBoxMass_pos hN he)).1.ne'
  have hA : (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (annulusMass_pos hM hdelta)).1.ne'
  letI := cond_isProbabilityMeasure hR
  letI := cond_isProbabilityMeasure hA
  unfold retainedPrior
  infer_instance

theorem retainedPrior_absolutelyContinuous (N M : ℕ) (e delta : ℝ) :
    retainedPrior N M e delta ≪ referenceLaw N M := by
  exact Measure.AbsolutelyContinuous.rfl.prod
    (cond_absolutelyContinuous.prod cond_absolutelyContinuous)

theorem retainedPrior_support_ae {N M : ℕ} (hN : 0<N) (e delta : ℝ) :
    ∀ᵐ z∂retainedPrior N M e delta,
      ‖z.1‖=1 ∧ 0<z.2.1 ∧ z.2.1∈radiusBox N e ∧ z.2.2∈gaussianAnnulus M delta := by
  have hx : ∀ᵐ z∂retainedPrior N M e delta,‖z.1‖=1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hrpos : ∀ᵐ r∂ProbabilityTheory.cond (radiusLaw N) (radiusBox N e),0<r :=
    cond_absolutelyContinuous.ae_le (radiusLaw_pos_ae hN)
  have hr : ∀ᵐ p∂(ProbabilityTheory.cond (radiusLaw N) (radiusBox N e)).prod
      (ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)),
      0<p.1 ∧ p.1∈radiusBox N e :=
    Measure.quasiMeasurePreserving_fst.ae
      (hrpos.and (ae_cond_mem (radiusBox_measurableSet N e)))
  have ha : ∀ᵐ p∂(ProbabilityTheory.cond (radiusLaw N) (radiusBox N e)).prod
      (ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)),
      p.2∈gaussianAnnulus M delta :=
    Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (gaussianAnnulus_measurableSet M delta))
  have hrest : ∀ᵐ z∂retainedPrior N M e delta,
      (0<z.2.1 ∧ z.2.1∈radiusBox N e) ∧ z.2.2∈gaussianAnnulus M delta :=
    Measure.quasiMeasurePreserving_snd.ae (hr.and ha)
  filter_upwards [hx,hrest] with z hx hz
  exact ⟨hx,hz.1.1,hz.1.2,hz.2⟩

theorem retained_reference_norm_ae {N M : ℕ} (hN : 0<N) (e delta : ℝ) :
    ∀ᵐ z∂retainedPrior N M e delta,‖cavityReferenceMap N M z‖=1 :=
  (retainedPrior_absolutelyContinuous N M e delta).ae_le (referenceMap_norm_ae hN M)

private theorem mass_smul_cond {V : Type*} [MeasurableSpace V]
    (nu : Measure V) [IsFiniteMeasure nu] (S : Set V) (hS : nu S≠0) :
    nu S • ProbabilityTheory.cond nu S=nu.restrict S := by
  unfold ProbabilityTheory.cond
  rw [smul_smul,ENNReal.mul_inv_cancel hS (measure_ne_top nu S),one_smul]

theorem restricted_reference_eq_mass_smul {N M : ℕ} (hN : 0<N) (hM : 0<M)
    {e delta : ℝ} (he : 0<e) (hdelta : 0<delta) :
    (referenceLaw N M).restrict (retainedRegion N M e delta)=
      ((radiusLaw N) (radiusBox N e)*(stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)) •
        retainedPrior N M e delta := by
  have hR : (radiusLaw N) (radiusBox N e) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (radiusBoxMass_pos hN he)).1.ne'
  have hA : (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (annulusMass_pos hM hdelta)).1.ne'
  rw [referenceLaw,retainedRegion,← Measure.prod_restrict,Measure.restrict_univ,← Measure.prod_restrict,
    ← mass_smul_cond (radiusLaw N) (radiusBox N e) hR,
    ← mass_smul_cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta) hA]
  simp only [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  simp only [retainedPrior,mul_comm]

theorem integral_restricted_reference {N M : ℕ} (hN : 0<N) (hM : 0<M)
    {e delta : ℝ} (he : 0<e) (hdelta : 0<delta)
    (f : Model.Vector N×(ℝ×Model.Vector M)→ℝ) :
    (∫z in retainedRegion N M e delta,f z∂referenceLaw N M)=
      (radiusBoxMass N e*annulusMass M delta)*(∫z,f z∂retainedPrior N M e delta) := by
  rw [restricted_reference_eq_mass_smul hN hM he hdelta,integral_smul_measure,
    ENNReal.toReal_mul,smul_eq_mul]
  rfl

end
end TensorPCA.NonRSLowerProofs.FiniteCavityRetainedPrior
