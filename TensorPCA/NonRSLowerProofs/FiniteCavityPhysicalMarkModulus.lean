-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityGramMarkContinuity
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianArrayLaw
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramMap

/-! Equality of Gaussian array laws transports fixed bounded marks to the canonical Gram
realization. The compact modulus is uniform in physical ambient dimension, and all
replicas retain their single shared draw.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPhysicalMarkModulus
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteUnitGramRealization FiniteUnitGramMap FiniteCavityGramMarkContinuity
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility FiniteCavityGaussianArrayLaw
open scoped BigOperators RealInnerProductSpace
noncomputable section

theorem numerator_product_eq_canonical {N M r : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (s : Fin (r+1) → UnitSpin N)
    (mark : Model.Vector M → ℝ) (hMark : Continuous mark) :
    (∫ g : CavityDisorder N M k,∏ i : Fin (r+1),mark (blockField k mu beta g (s i).val)
      ∂stdGaussian (CavityDisorder N M k))=
    ∫ g : CavityDisorder (r+1) M k,∏ i : Fin (r+1),mark
      (blockField k mu beta g (realization (sampleGram s) i)) ∂stdGaussian (CavityDisorder (r+1) M k) := by
  have hA := sampleGram_mem_unitGramSet s
  have hGram (i j : Fin (r+1)) : inner ℝ (s i).val (s j).val=
      inner ℝ (realization (sampleGram s) i) (realization (sampleGram s) j) :=
    (realization_inner (sampleGram s) hA.1 i j).symm
  have hLaw := blockField_array_law_eq_of_gram (M := M) k hmu beta (fun i ↦ (s i).val)
    (realization (sampleGram s)) hGram
  have hTest : Measurable (fun f : Fin (r+1) → Model.Vector M ↦ ∏ i,mark (f i)) :=
    (continuous_finsetProd Finset.univ (fun i _ ↦ hMark.comp (continuous_apply i))).measurable
  have H := congrArg (fun rho ↦ ∫ f : Fin (r+1) → Model.Vector M,∏ i,mark (f i) ∂rho) hLaw
  rw [integral_map (blockField_array_continuous k mu beta (fun i ↦ (s i).val)).measurable.aemeasurable hTest.aestronglyMeasurable,
    integral_map (blockField_array_continuous k mu beta (realization (sampleGram s))).measurable.aemeasurable hTest.aestronglyMeasurable] at H
  exact H

theorem compensator_product_eq_canonical {N r : ℕ} (hN : 0<N) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (s : Fin (r+1) → UnitSpin N)
    (mark : ℝ → ℝ) (hMark : Continuous mark) :
    (∫ g : GroundState.Disorder N k,∏ i : Fin (r+1),mark (inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (s i).val) g)
      ∂stdGaussian (GroundState.Disorder N k))=
    ∫ g : GroundState.Disorder (r+1) k,∏ i : Fin (r+1),mark (inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (realization (sampleGram s) i)) g)
      ∂stdGaussian (GroundState.Disorder (r+1) k) := by
  have hA := sampleGram_mem_unitGramSet s
  have hGram (i j : Fin (r+1)) : inner ℝ (s i).val (s j).val=
      inner ℝ (realization (sampleGram s) i) (realization (sampleGram s) j) :=
    (realization_inner (sampleGram s) hA.1 i j).symm
  have hLaw := compensator_array_law_eq_of_gram hN (Nat.succ_pos r) M k hmu beta
    (fun i ↦ (s i).val) (realization (sampleGram s)) hGram
  have hTest : Measurable (fun f : Fin (r+1) → ℝ ↦ ∏ i,mark (f i)) :=
    (continuous_finsetProd Finset.univ (fun i _ ↦ hMark.comp (continuous_apply i))).measurable
  have hLeft : Measurable (fun g : GroundState.Disorder N k ↦ fun i : Fin (r+1) ↦ inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (s i).val) g) := by fun_prop
  have hRight : Measurable (fun g : GroundState.Disorder (r+1) k ↦ fun i : Fin (r+1) ↦ inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (realization (sampleGram s) i)) g) := by fun_prop
  have H := congrArg (fun rho ↦ ∫ f : Fin (r+1) → ℝ,∏ i,mark (f i) ∂rho) hLaw
  rw [integral_map hLeft.aemeasurable hTest.aestronglyMeasurable,
    integral_map hRight.aemeasurable hTest.aestronglyMeasurable] at H
  exact H

theorem exists_uniform_physical_numerator_modulus (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : Model.Vector M → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {N N' : ℕ} (s : Fin (r+1) → UnitSpin N) (t : Fin (r+1) → UnitSpin N'),
      (∀ i j,|inner ℝ (s i).val (s j).val-inner ℝ (t i).val (t j).val|≤delta)→
        |(∫ g : CavityDisorder N M k,∏ i : Fin (r+1),mark (blockField k mu beta g (s i).val)
          ∂stdGaussian (CavityDisorder N M k))-
         (∫ g : CavityDisorder N' M k,∏ i : Fin (r+1),mark (blockField k mu beta g (t i).val)
          ∂stdGaussian (CavityDisorder N' M k))|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_numerator_mark_product_entry_modulus r M k mu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro N N' s t hGram
  rw [numerator_product_eq_canonical k hmu beta s mark hMark,numerator_product_eq_canonical k hmu beta t mark hMark]
  exact hMain (sampleGram s) (sampleGram_mem_unitGramSet s) (sampleGram t) (sampleGram_mem_unitGramSet t) hGram

theorem exists_uniform_physical_compensator_modulus (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : ℝ → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {N N' : ℕ},0<N → 0<N' →
      ∀ (s : Fin (r+1) → UnitSpin N) (t : Fin (r+1) → UnitSpin N'),
      (∀ i j,|inner ℝ (s i).val (s j).val-inner ℝ (t i).val (t j).val|≤delta)→
        |(∫ g : GroundState.Disorder N k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (s i).val) g)
          ∂stdGaussian (GroundState.Disorder N k))-
         (∫ g : GroundState.Disorder N' k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (t i).val) g)
          ∂stdGaussian (GroundState.Disorder N' k))|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_compensator_mark_product_entry_modulus r M k mu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro N N' hN hN' s t hGram
  rw [compensator_product_eq_canonical hN M k hmu beta s mark hMark,
    compensator_product_eq_canonical hN' M k hmu beta t mark hMark]
  exact hMain (sampleGram s) (sampleGram_mem_unitGramSet s) (sampleGram t) (sampleGram_mem_unitGramSet t) hGram

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPhysicalMarkModulus
