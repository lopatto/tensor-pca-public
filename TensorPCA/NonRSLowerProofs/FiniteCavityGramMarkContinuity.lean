-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramRealizationContinuity
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility

/-! Fixed-mark product moduli for the canonical numerator and theta-compensator Gaussian
fields. Entrywise Gram tolerances are chosen before the two matrices. Transport of
vector laws in arbitrary ambient dimension is treated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityGramMarkContinuity
open MeasureTheory ProbabilityTheory Set Filter
open FiniteUnitGramRealization FiniteUnitGramRealizationContinuity
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility
open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
noncomputable section

theorem blockField_joint_continuous (N M k : ℕ) (mu beta : ℝ) :
    Continuous (fun p : Model.Vector N×CavityDisorder N M k ↦ blockField k mu beta p.2 p.1) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum Finset.univ
  intro I _
  exact ((PiLp.continuous_apply 2 _ I).comp ((zFeature_continuous N k mu beta).comp continuous_fst)).mul
    ((PiLp.continuous_apply 2 _ (i,I)).comp continuous_snd)

theorem limitingCompensatorField_joint_continuous (N M k : ℕ) (mu beta : ℝ) :
    Continuous (fun p : Model.Vector N×GroundState.Disorder N k ↦ inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) p.1) p.2) := by
  have hFeature : Continuous (fun x : Model.Vector N ↦
      limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) := by
    change Continuous (fun x : Model.Vector N ↦ Real.sqrt ((M : ℝ)/(N : ℝ)) •
      NonRSUpperProofs.FiniteTensorMixtureMaximum.feature (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j*((((j : ℕ)+1)-1 : ℕ) : ℝ)) x)
    exact (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous (N := N)
      (fun j : Fin k ↦ (j : ℕ)+1)
      (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j*((((j : ℕ)+1)-1 : ℕ) : ℝ))).const_smul
        (Real.sqrt ((M : ℝ)/(N : ℝ)))
  exact (hFeature.comp continuous_fst).inner continuous_snd

private theorem entry_modulus (r : ℕ) (f : Matrix (Fin (r+1)) (Fin (r+1)) ℝ → ℝ)
    (hF : UniformContinuousOn f (unitGramSet (r+1))) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ A∈unitGramSet (r+1),∀ B∈unitGramSet (r+1),
      (∀ i j,|A i j-B i j|≤delta)→|f A-f B|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := Metric.uniformContinuousOn_iff.mp hF eps heps
  refine ⟨delta/2,half_pos hDelta,?_⟩
  intro A hA B hB hEntries
  have hNorm : ‖A-B‖≤delta/2 := (Matrix.norm_le_iff (half_pos hDelta).le).mpr
    (fun i j ↦ by simpa only [Real.norm_eq_abs,Matrix.sub_apply] using hEntries i j)
  have hDist : dist A B<delta := by
    rw [dist_eq_norm]
    exact hNorm.trans_lt (half_lt_self hDelta)
  simpa only [Real.dist_eq] using hMain A hA B hB hDist

theorem numerator_mark_product_uniformContinuousOn (r M k : ℕ) (mu beta : ℝ)
    (mark : Model.Vector M → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) :
    UniformContinuousOn (fun A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ ↦
      ∫ g : CavityDisorder (r+1) M k,∏ i : Fin (r+1),mark (blockField k mu beta g (realization A i))
        ∂stdGaussian (CavityDisorder (r+1) M k)) (unitGramSet (r+1)) :=
  bounded_mark_product_uniformContinuousOn r (stdGaussian (CavityDisorder (r+1) M k))
    (fun x g ↦ blockField k mu beta g x) (blockField_joint_continuous (r+1) M k mu beta) mark hMark hBound

theorem compensator_mark_product_uniformContinuousOn (r M k : ℕ) (mu beta : ℝ)
    (mark : ℝ → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) :
    UniformContinuousOn (fun A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ ↦
      ∫ g : GroundState.Disorder (r+1) k,∏ i : Fin (r+1),mark (inner ℝ
        (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
          (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (realization A i)) g)
        ∂stdGaussian (GroundState.Disorder (r+1) k)) (unitGramSet (r+1)) :=
  bounded_mark_product_uniformContinuousOn r (stdGaussian (GroundState.Disorder (r+1) k))
    (fun x g ↦ inner ℝ (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
      (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) g)
    (limitingCompensatorField_joint_continuous (r+1) M k mu beta) mark hMark hBound

theorem exists_numerator_mark_product_entry_modulus (r M k : ℕ) (mu beta : ℝ)
    (mark : Model.Vector M → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1)
    {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ A∈unitGramSet (r+1),∀ B∈unitGramSet (r+1),
      (∀ i j,|A i j-B i j|≤delta)→
        |(∫ g : CavityDisorder (r+1) M k,∏ i : Fin (r+1),mark (blockField k mu beta g (realization A i))
          ∂stdGaussian (CavityDisorder (r+1) M k))-
         (∫ g : CavityDisorder (r+1) M k,∏ i : Fin (r+1),mark (blockField k mu beta g (realization B i))
          ∂stdGaussian (CavityDisorder (r+1) M k))|<eps :=
  entry_modulus r _ (numerator_mark_product_uniformContinuousOn r M k mu beta mark hMark hBound) heps

theorem exists_compensator_mark_product_entry_modulus (r M k : ℕ) (mu beta : ℝ)
    (mark : ℝ → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1)
    {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ A∈unitGramSet (r+1),∀ B∈unitGramSet (r+1),
      (∀ i j,|A i j-B i j|≤delta)→
        |(∫ g : GroundState.Disorder (r+1) k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (realization A i)) g)
          ∂stdGaussian (GroundState.Disorder (r+1) k))-
         (∫ g : GroundState.Disorder (r+1) k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (realization B i)) g)
          ∂stdGaussian (GroundState.Disorder (r+1) k))|<eps :=
  entry_modulus r _ (compensator_mark_product_uniformContinuousOn r M k mu beta mark hMark hBound) heps

end
end TensorPCA.NonRSLowerProofs.FiniteCavityGramMarkContinuity
