-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.SpherePolarProofs
public import TensorPCA.GaussianMaximumComparisonProofs
public import TensorPCA.Geometry

/-! The finite cavity reference product law in the unit-sphere normalization. The bulk
radius is the norm of a canonical Gaussian, independent of the bulk sphere direction
and fresh cavity Gaussian.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceLaw
open MeasureTheory ProbabilityTheory Set
open GaussianCompactFeatureComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def radiusLaw (N : ℕ) : Measure ℝ := (stdGaussian (Model.Vector N)).map (fun g => ‖g‖)

instance radiusLaw_probability (N : ℕ) : IsProbabilityMeasure (radiusLaw N) := by
  unfold radiusLaw
  infer_instance

def referenceLaw (N M : ℕ) : Measure (Model.Vector N×(ℝ×Model.Vector M)) :=
  (Model.spherePrior N).prod ((radiusLaw N).prod (stdGaussian (Model.Vector M)))

instance referenceLaw_probability (N M : ℕ) : IsProbabilityMeasure (referenceLaw N M) := by
  unfold referenceLaw
  infer_instance

private def gaussianAppend (N M : ℕ) : Model.Vector N×Model.Vector M→L[ℝ] Model.Vector (N+M) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (Fin.addCases p.1 p.2)
      map_add' := by
        intro p q
        ext i
        exact Fin.addCases (fun _ => by simp) (fun _ => by simp) i
      map_smul' := by
        intro a p
        ext i
        exact Fin.addCases (fun _ => by simp [PiLp.smul_apply]) (fun _ => by simp [PiLp.smul_apply]) i }

private theorem gaussianAppend_gaussian_map (N M : ℕ) :
    ((stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector M))).map (gaussianAppend N M)=
      stdGaussian (Model.Vector (N+M)) := by
  let e : Model.Vector (N+M)≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N⊕Fin M) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm
  let S := (sumSplit (ι := Fin N) (κ := Fin M)).comp e.toContinuousLinearEquiv.toContinuousLinearMap
  have hsplit : (stdGaussian (Model.Vector (N+M))).map S=
      (stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector M)) := by
    change (stdGaussian (Model.Vector (N+M))).map ((sumSplit (ι := Fin N) (κ := Fin M)) ∘ e)=_
    rw [← Measure.map_map (sumSplit (ι := Fin N) (κ := Fin M)).continuous.measurable e.continuous.measurable,
      stdGaussian_map]
    simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using
      (sumSplit_gaussian_map (ι := Fin N) (κ := Fin M))
  have hid : (gaussianAppend N M) ∘ S=id := by
    funext g
    ext i
    exact Fin.addCases (fun _ => by simp [gaussianAppend,S,e,sumSplit])
      (fun _ => by simp [gaussianAppend,S,e,sumSplit]) i
  rw [← hsplit,Measure.map_map (gaussianAppend N M).continuous.measurable S.continuous.measurable,
    hid,Measure.map_id]

/-- Literal unit-sphere normalization of append(r*x,eta). At zero the same
total origin convention as Model.normalize is retained. -/
def cavityReferenceMap (N M : ℕ) (z : Model.Vector N×(ℝ×Model.Vector M)) : Model.Vector (N+M) :=
  Model.normalize (WithLp.toLp 2 (Fin.addCases (z.2.1 • z.1) z.2.2))

theorem cavityReferenceMap_eq (N M : ℕ) (z : Model.Vector N×(ℝ×Model.Vector M)) :
    cavityReferenceMap N M z=Model.normalize
      (WithLp.toLp 2 (Fin.addCases (z.2.1 • z.1) z.2.2)) := rfl

theorem cavityReferenceMap_measurable (N M : ℕ) : Measurable (cavityReferenceMap N M) := by
  exact (Model.measurable_normalize (N+M)).comp
    ((gaussianAppend N M).continuous.measurable.comp
      ((measurable_fst.comp measurable_snd).smul measurable_fst |>.prodMk (measurable_snd.comp measurable_snd)))

/-- Reconstruction with the original radius/cavity product law.
-/
theorem cavityReferenceMap_measurePreserving {N : ℕ} (hN : 0<N) (M : ℕ) :
    MeasurePreserving (cavityReferenceMap N M) (referenceLaw N M) (Model.spherePrior (N+M)) := by
  have hAssoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (Model.spherePrior N) (radiusLaw N) (stdGaussian (Model.Vector M)))
  have hRecon := (SpherePolarProofs.spherePrior_gaussian_radial_reconstruction hN).prod
    (MeasurePreserving.id (stdGaussian (Model.Vector M)))
  have hPair : MeasurePreserving
      (fun z : Model.Vector N×(ℝ×Model.Vector M) => (z.2.1 • z.1,z.2.2))
      (referenceLaw N M) ((stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector M))) :=
    hRecon.comp hAssoc
  have hAppend : MeasurePreserving (gaussianAppend N M)
      ((stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector M)))
      (stdGaussian (Model.Vector (N+M))) :=
    ⟨(gaussianAppend N M).continuous.measurable,gaussianAppend_gaussian_map N M⟩
  have hNorm : MeasurePreserving (Model.normalize (N := N+M))
      (stdGaussian (Model.Vector (N+M))) (Model.spherePrior (N+M)) :=
    ⟨Model.measurable_normalize (N+M),rfl⟩
  exact hNorm.comp (hAppend.comp hPair)

theorem actual_cavity_reference_product {N : ℕ} (hN : 0<N) (M : ℕ) :
    (referenceLaw N M).map (cavityReferenceMap N M)=Model.spherePrior (N+M) :=
  (cavityReferenceMap_measurePreserving hN M).map_eq

theorem radiusLaw_pos_ae {N : ℕ} (hN : 0<N) : ∀ᵐ r ∂radiusLaw N,0<r := by
  apply (ae_map_iff measurable_norm.aemeasurable measurableSet_Ioi).2
  exact (Geometry.gaussian_ne_zero_ae hN).mono (fun g hg => norm_pos_iff.mpr hg)

theorem referenceMap_norm_ae {N : ℕ} (hN : 0<N) (M : ℕ) :
    ∀ᵐ z ∂referenceLaw N M,‖cavityReferenceMap N M z‖=1 := by
  apply (ae_map_iff (cavityReferenceMap_measurable N M).aemeasurable
    ((measurableSet_singleton (1 : ℝ)).preimage measurable_norm)).1
  rw [actual_cavity_reference_product hN M]
  exact Geometry.spherePrior_norm_ae (by omega : 0<N+M)


end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceLaw
