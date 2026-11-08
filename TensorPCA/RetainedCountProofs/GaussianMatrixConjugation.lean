-- SPDX-License-Identifier: Apache-2.0
/- Attributed exact Householder/conjugation source proof from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean (upstream
   openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Existing shared
   Gaussian matrices/transposition/symmetrization are reused. Laws below are
   literal pushforwards of standard Gaussian; the sole actual GOE definition
   remains SphericalGaussianJet.goeLaw. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixLaw
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def alignIsometry (e v : E) : E ≃ₗᵢ[ℝ] E :=
  Submodule.reflection (ℝ ∙ (v - ‖v‖ • e))ᗮ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma alignIsometry_apply (e v x : E) :
    alignIsometry e v x = x -
      (2 * (inner ℝ (v - ‖v‖ • e) x / ‖v - ‖v‖ • e‖ ^ 2)) • (v - ‖v‖ • e) := by
  rw [alignIsometry, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [two_mul, add_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma alignIsometry_align (e v : E) (he : ‖e‖ = 1) :
    alignIsometry e v v = ‖v‖ • e := by
  apply Submodule.reflection_sub
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), he, mul_one]

lemma alignIsometry_measurable (e : E) :
    Measurable (fun p : E × E => alignIsometry e p.1 p.2) := by
  simp_rw [alignIsometry_apply]
  fun_prop

lemma random_isometry_gaussian_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (U : Ω → E ≃ₗᵢ[ℝ] E)
    (hU : Measurable (fun p : Ω × E => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × E => (p.1, U p.1 p.2))
      (μ.prod (stdGaussian E)) (μ.prod (stdGaussian E)) := by
  exact (MeasurePreserving.id μ).skew_product (g := fun ω x => U ω x)
    (μc := stdGaussian E) (μd := stdGaussian E) hU
    (Filter.Eventually.of_forall (fun ω => stdGaussian_map (U ω)))

lemma exposed_gaussian_alignment (e : E) :
    MeasurePreserving (fun p : E × E => (p.1, alignIsometry e p.1 p.2))
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
  random_isometry_gaussian_preserving _ _ (alignIsometry_measurable e)


end

variable {ι : Type*} [Fintype ι]

def rowIsometry (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => U)

@[simp] lemma rowIsometry_apply (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i : ι) : rowIsometry U A i = U (A i) := rfl

def conjugateGaussianMatrix (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι :=
  (rowIsometry U).trans (transposeGaussianMatrix.trans
    ((rowIsometry U).trans transposeGaussianMatrix))

lemma conjugateGaussianMatrix_preserves (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U) =
      stdGaussian (GaussianMatrix ι) :=
  stdGaussian_map _

lemma euclidean_isometry_apply_eq_sum
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) (i : ι) :
    U v i = ∑ j, v j * U (EuclideanSpace.basisFun ι ℝ j) i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v, map_sum]
  simp

lemma conjugateGaussianMatrix_apply
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i j : ι) :
    conjugateGaussianMatrix U A i j =
      ∑ k, ∑ l, U (EuclideanSpace.basisFun ι ℝ k) i * A k l *
        U (EuclideanSpace.basisFun ι ℝ l) j := by
  simp only [conjugateGaussianMatrix, LinearIsometryEquiv.trans_apply,
    transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma conjugateGaussianMatrix_transpose
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (transposeGaussianMatrix A) =
      transposeGaussianMatrix (conjugateGaussianMatrix U A) := by
  ext i j
  simp only [conjugateGaussianMatrix_apply, transposeGaussianMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma conjugate_symmetrize (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (symmetrizeGaussianMatrix s A) =
      symmetrizeGaussianMatrix s (conjugateGaussianMatrix U A) := by
  simp only [symmetrizeGaussianMatrix, map_smul, map_add,
    conjugateGaussianMatrix_transpose]

lemma symmetrized_conjugate (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s))).map (conjugateGaussianMatrix U) = ((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)) := by
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, conjugate_symmetrize]
  calc
    _ = ((stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U)).map
        (symmetrizeGaussianMatrix s) :=
      (Measure.map_map (symmetrizeGaussianMatrix_continuous s).measurable
        (conjugateGaussianMatrix U).continuous.measurable).symm
    _ = _ := by rw [conjugateGaussianMatrix_preserves]

lemma conjugateGaussianMatrix_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    Measurable (fun p : Ω × GaussianMatrix ι => conjugateGaussianMatrix (U p.1) p.2) := by
  have hc (k i : ι) : Measurable (fun ω => U ω (EuclideanSpace.basisFun ι ℝ k) i) :=
    (by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).comp
      (hU.comp (measurable_id.prodMk measurable_const))
  change Measurable (fun p : Ω × GaussianMatrix ι => WithLp.toLp 2
    (fun i => WithLp.toLp 2 (fun j => conjugateGaussianMatrix (U p.1) p.2 i j)))
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  simp only [conjugateGaussianMatrix_apply]
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  exact ((hc k i).comp measurable_fst |>.mul
    ((by fun_prop : Measurable (fun A : GaussianMatrix ι => A k l)).comp measurable_snd)).mul
      ((hc l j).comp measurable_fst)

lemma random_symmetrized_conjugation_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (s : ℝ)
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × GaussianMatrix ι =>
      (p.1, conjugateGaussianMatrix (U p.1) p.2))
      (μ.prod (((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)))) (μ.prod (((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)))) := by
  let : IsProbabilityMeasure (((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s))) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  exact (MeasurePreserving.id μ).skew_product
    (g := fun ω A => conjugateGaussianMatrix (U ω) A)
    (conjugateGaussianMatrix_measurable U hU)
    (Filter.Eventually.of_forall (fun ω => symmetrized_conjugate s (U ω)))


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
