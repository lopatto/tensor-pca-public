-- SPDX-License-Identifier: Apache-2.0
/- Exact independent Gaussian block law adapted from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean (upstream
   openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All matrix laws
   are literal symmetrized standard Gaussian pushforwards. The actual GOE
   definition remains SphericalGaussianJet.goeLaw. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianUpperSplit
public import TensorPCA.RetainedCountProofs.GaussianMatrixBorder
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
instance symmetrized_probability {ι : Type*} [Fintype ι] (s : ℝ) :
    IsProbabilityMeasure ((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)) :=
  (Measure.isProbabilityMeasure_map_iff
    (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
def matrixTail {n : ℕ} (A : GaussianMatrix (Fin (n + 1))) : GaussianMatrix (Fin n) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A i.succ j.succ))

def goeBlocks {n : ℕ} (A : GaussianMatrix (Fin (n + 1))) :
    ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) :=
  (A 0 0, (fun i => A 0 i.succ, matrixTail A))

lemma matrixTail_measurable (n : ℕ) : Measurable (matrixTail (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  fun_prop [matrixTail]

lemma goeBlocks_measurable (n : ℕ) : Measurable (goeBlocks (n := n)) := by
  exact (by fun_prop : Measurable fun A : GaussianMatrix (Fin (n+1)) => A 0 0).prodMk
    ((Measurable.of_eval (fun _ => by fun_prop)).prodMk (matrixTail_measurable n))

lemma borderMatrix_blocks {n : ℕ} (A : GaussianMatrix (Fin (n + 1)))
    (hA : ∀ i j, A i j = A j i) :
    borderMatrix (goeBlocks A).1 (WithLp.toLp 2 (goeBlocks A).2.1) (goeBlocks A).2.2 = A := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · rfl
  · exact hA _ _
  · rfl

lemma symmetrized_blocks_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (goeBlocks (n := n)) (((stdGaussian (GaussianMatrix (Fin (n + 1)))).map (symmetrizeGaussianMatrix s)))
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (((stdGaussian (GaussianMatrix (Fin n))).map (symmetrizeGaussianMatrix s))))) := by
  let μ := Measure.pi (goeUpperMarginal (m := n+1) s)
  have hw : MeasurePreserving (upperWrite (m := n))
      (Measure.pi (goeUpperMarginal s)) (((stdGaussian (GaussianMatrix (Fin n))).map (symmetrizeGaussianMatrix s))) :=
    ⟨upperWrite_measurable, (symmetrized_eq_upper_product (m := n) s).symm⟩
  have hr : MeasurePreserving (upperRead (m := n+1)) (((stdGaussian (GaussianMatrix (Fin (n+1)))).map (symmetrizeGaussianMatrix s))) μ :=
    ⟨upperRead_measurable, symmetrized_upper_law (m := n+1) s⟩
  have hp := (MeasurePreserving.id (gaussianReal 0 (4 * s^2).toNNReal)).prod
    ((MeasurePreserving.id (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal)).prod hw)
  have h := hp.comp ((splitUpper_preserving n s).comp hr)
  refine ⟨goeBlocks_measurable n, ?_⟩
  rw [← h.map_eq]
  apply Measure.map_congr
  filter_upwards [symmetrized_symmetric_ae (m := n+1) s] with A hA
  dsimp only [Function.comp_apply, Prod.map_apply, id_eq, splitUpper, upperRead, goeBlocks]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change matrixTail A = upperWrite (upperRead (matrixTail A))
  exact (upperWrite_upperRead _ (fun i j => hA i.succ j.succ)).symm

lemma aligned_symmetrizedBlock_preserving (n : ℕ) (s : ℝ)
    (e : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun p : (Fin n → ℝ) × GaussianMatrix (Fin n) =>
      (p.1, conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 p.1)) p.2))
      ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod (((stdGaussian (GaussianMatrix (Fin n))).map (symmetrizeGaussianMatrix s))))
      ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod (((stdGaussian (GaussianMatrix (Fin n))).map (symmetrizeGaussianMatrix s)))) := by
  have hm : Measurable (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n) =>
      alignIsometry e (WithLp.toLp 2 p.1) p.2) := by
    simp_rw [alignIsometry_apply]
    fun_prop
  exact random_symmetrized_conjugation_preserving
    (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal) s
    (fun v : Fin n → ℝ => alignIsometry e (WithLp.toLp 2 v)) hm

lemma exposed_column_tail_law (n : ℕ) (s : ℝ) (e : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun A : GaussianMatrix (Fin (n+1)) =>
      (A 0 0, (fun i => A 0 i.succ,
        conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 (fun i => A 0 i.succ)))
          (matrixTail A))))
      (((stdGaussian (GaussianMatrix (Fin (n+1)))).map (symmetrizeGaussianMatrix s)))
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (((stdGaussian (GaussianMatrix (Fin n))).map (symmetrizeGaussianMatrix s))))) :=
  ((MeasurePreserving.id _).prod (aligned_symmetrizedBlock_preserving n s e)).comp (symmetrized_blocks_preserving n s)


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
