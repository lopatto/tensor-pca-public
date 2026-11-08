-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramRealization
public import TensorPCA.NonRSUpperProofs.SphericalSelectedPerturbationKernel
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed

/-! The continuous finite Gram map on intrinsic unit-spin arrays.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteUnitGramMap
open Matrix Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteUnitGramRealization
open scoped RealInnerProductSpace BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ambientGram_posSemidef {N K : ℕ} (s : Fin K → EuclideanSpace ℝ (Fin N)) :
    Matrix.PosSemidef (fun i j ↦ inner ℝ (s i) (s j)) := by
  let R : Matrix (Fin K) (Fin N) ℝ := fun i j ↦ s i j
  have hGram : (fun i j ↦ inner ℝ (s i) (s j) : Matrix (Fin K) (Fin K) ℝ)=R*Rᴴ := by
    ext i j
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Matrix.mul_apply,Matrix.conjTranspose,Matrix.map_apply,Matrix.transpose_apply,star_trivial,R]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hGram]
  exact Matrix.posSemidef_self_mul_conjTranspose R

def sampleGram {N K : ℕ} (s : Fin K → UnitSpin N) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j ↦ inner ℝ (s i).val (s j).val

theorem sampleGram_mem_unitGramSet {N K : ℕ} (s : Fin K → UnitSpin N) :
    sampleGram s∈unitGramSet K := by
  refine ⟨ambientGram_posSemidef (fun i ↦ (s i).val),?_⟩
  intro i
  change inner ℝ (s i).val (s i).val=1
  rw [real_inner_self_eq_norm_sq,(s i).property,one_pow]

theorem sampleGram_continuous (N K : ℕ) :
    Continuous (sampleGram (N := N) (K := K)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_subtype_val.comp (continuous_apply i)).inner
    (continuous_subtype_val.comp (continuous_apply j))

theorem sampleGram_measurable (N K : ℕ) :
    Measurable (sampleGram (N := N) (K := K)) := (sampleGram_continuous N K).measurable

theorem entry_abs_sub_le_norm {K : ℕ} (A B : Matrix (Fin K) (Fin K) ℝ) (i j : Fin K) :
    |A i j-B i j|≤‖A-B‖ := by
  simpa only [Real.norm_eq_abs,Matrix.sub_apply] using
    (Matrix.norm_entry_le_entrywise_sup_norm (A-B) (i := i) (j := j))

end
end TensorPCA.NonRSLowerProofs.FiniteUnitGramMap
