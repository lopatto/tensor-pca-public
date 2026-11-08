-- SPDX-License-Identifier: Apache-2.0
/- Narrow static score-coordinate source port:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalCountRectangles.lean
Only the literal score-pair measurable equivalence, evaluation and volume
transport are retained; determinant intensity/asymptotic imports are omitted.
Bodies unchanged except namespace wrappers. See repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SphericalScoreDensity
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalMarkedWindows
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
def scorePairEquiv : (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma scorePairEquiv_apply (h k : ℝ) : scorePairEquiv (h,k) = WithLp.toLp 2 ![h,k] := rfl

lemma scorePairEquiv_measurePreserving : MeasurePreserving scorePairEquiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm


end
end TensorPCA.RetainedCountProofs.SphericalMarkedWindows
