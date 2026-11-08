-- SPDX-License-Identifier: Apache-2.0
/- Attributed generic finite count-window source port from
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/SphericalCountRectangles.lean. Exact ordinary mean
   measurability and actual Euclidean rectangle integration proofs retained.
   The exact score-pair equivalence is reused from SphericalScoreCoordinates;
   mixed/pure count-intensity specializations are not needed here. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GOEPhysicalPotential
public import TensorPCA.RetainedCountProofs.SphericalScoreCoordinates
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function GOEPhysicalPotential GOERawMoments
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma physicalMean_measurable (n N : ℕ) (b : ℝ) : Measurable (physicalMean n N b) := by
  have h : Continuous (fun p : ℝ × Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      matrixAbsoluteDet n p.1 p.2) :=
    ((continuous_fst.smul continuous_const).sub continuous_snd).matrix_det.abs
  exact h.measurable.stronglyMeasurable.integral_prod_right'.measurable

def rectangularScoreWindow (I U : Set ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {b | b 0 ∈ I ∧ b 1 ∈ U}

lemma rectangularScoreWindow_measurable (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    MeasurableSet (rectangularScoreWindow I U) :=
  (hI.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable).inter
    (hU.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable)

lemma lintegral_rectangularScoreWindow (I U : Set ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b in rectangularScoreWindow I U, f b) =
      ∫⁻ h in I, ∫⁻ k in U, f (WithLp.toLp 2 ![h,k]) := by
  rw [← scorePairEquiv_measurePreserving.setLIntegral_comp_preimage_emb
    scorePairEquiv.measurableEmbedding f]
  have he : scorePairEquiv ⁻¹' rectangularScoreWindow I U = I ×ˢ U := by
    ext p
    rfl
  rw [he]
  exact setLIntegral_prod _ (hf.comp scorePairEquiv.measurable).aemeasurable


end
end TensorPCA.RetainedCountProofs.SphericalMarkedWindows
