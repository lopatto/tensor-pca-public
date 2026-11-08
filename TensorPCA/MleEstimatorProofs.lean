-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.MleSelectorProofs
public import TensorPCA.TensorLiftProofs
public import Mathlib.Probability.Distributions.Bernoulli

/-! Borel likelihood maximizers, with independent fair sign randomization for
even degree, in the manuscript's ordered tensor experiment. -/

@[expose] public section
namespace TensorPCA.MleEstimatorProofs
open Set Filter MeasureTheory ProbabilityTheory MleSelectorProofs TensorLiftProofs
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def vectorSelector (N k : ℕ) (hN : 0 < N) (w : Model.Tensor N (k+1)) : Model.Vector N :=
  finiteLift k (canonicalTensor N (k+1) hN w)

theorem vectorSelector_measurable (N k : ℕ) (hN : 0 < N) :
    Measurable (vectorSelector N k hN) :=
  (finiteLift_measurable N k).comp (canonicalTensor_measurable N (k+1) hN)

theorem vectorSelector_spec (N k : ℕ) (hN : 0 < N) (w : Model.Tensor N (k+1)) :
    vectorSelector N k hN w ∈ Model.unitSphere N ∧
      Model.feature (k+1) (vectorSelector N k hN w) = canonicalTensor N (k+1) hN w := by
  obtain ⟨x, hx, hT⟩ := canonicalTensor_mem N (k+1) hN w
  simpa only [vectorSelector, ← hT] using finiteLift_feature_spec k hx

theorem vectorSelector_ae_maximizes (N k : ℕ) (hN : 0 < N) (lam : ℝ) :
    ∀ᵐ w ∂Model.observationLaw N (k+1) lam, ∀ x ∈ Model.unitSphere N,
      Model.score w x ≤ Model.score w (vectorSelector N k hN w) := by
  filter_upwards [canonicalTensor_ae_maximizes N (k+1) hN lam] with w hw
  intro x hx
  simpa only [Model.score, (vectorSelector_spec N k hN w).2] using hw x hx

def halfParameter : unitInterval := ⟨1/2, by constructor <;> norm_num⟩

def fairSeed : Measure Bool := bernoulliMeasure true false halfParameter

instance fairSeed_probability : IsProbabilityMeasure fairSeed := by
  unfold fairSeed
  infer_instance

def fairEstimator (N k : ℕ) (hN : 0 < N) : Model.Estimator N (k+1) Bool := by
  classical
  exact fun w a ↦ if Even (k+1) then
    (if a then vectorSelector N k hN w else -vectorSelector N k hN w)
    else vectorSelector N k hN w

theorem fairEstimator_isUnit (N k : ℕ) (hN : 0 < N) :
    Model.IsUnitEstimator (fairEstimator N k hN) := by
  classical
  constructor
  · apply measurable_from_prod_countable_left
    intro a
    by_cases heven : Even (k+1)
    · cases a
      · convert (vectorSelector_measurable N k hN).neg using 1
        funext w
        simp [Function.uncurry, fairEstimator, heven]
      · simpa only [Function.uncurry, fairEstimator, ite_eq_left heven, ite_true] using
          vectorSelector_measurable N k hN
    · simpa only [Function.uncurry, fairEstimator, ite_eq_right heven] using
        vectorSelector_measurable N k hN
  · intro w a
    have hnorm : ‖vectorSelector N k hN w‖ = 1 := (vectorSelector_spec N k hN w).1
    by_cases heven : Even (k+1) <;> cases a <;> simp [fairEstimator, heven, hnorm]

theorem fairEstimator_feature (N k : ℕ) (hN : 0 < N) (w : Model.Tensor N (k+1)) (a : Bool) :
    Model.feature (k+1) (fairEstimator N k hN w a) =
      Model.feature (k+1) (vectorSelector N k hN w) := by
  classical
  apply (GaussianMaximumProofs.feature_eq_iff_unit (Nat.succ_ne_zero k)
    ((fairEstimator_isUnit N k hN).2 w a) (vectorSelector_spec N k hN w).1).mpr
  by_cases heven : Even (k+1) <;> cases a <;> simp [fairEstimator, heven]

theorem fairEstimator_isMLE (N k : ℕ) (hN : 0 < N) (lam : ℝ) :
    Model.IsMLE N (k+1) lam (fairEstimator N k hN) fairSeed := by
  refine ⟨fairEstimator_isUnit N k hN, ?_⟩
  have hmax := vectorSelector_ae_maximizes N k hN lam
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmax] with z hz
  intro x hx
  simpa only [Model.score, fairEstimator_feature N k hN z.1 z.2] using hz x hx

theorem halfParameter_symm : unitInterval.symm halfParameter = halfParameter := by
  apply Subtype.ext
  norm_num [halfParameter, unitInterval.coe_symm_eq]

theorem bernoulli_half_comm {X : Type*} [MeasurableSpace X] (x y : X) :
    bernoulliMeasure x y halfParameter = bernoulliMeasure y x halfParameter := by
  simp only [bernoulliMeasure_def, halfParameter_symm]
  exact add_comm _ _

theorem fairEstimator_symmetric (N k : ℕ) (hN : 0 < N) (heven : Even (k+1)) :
    Model.HasSymmetricOutputLaw (fairEstimator N k hN) fairSeed := by
  classical
  intro w
  rw [fairSeed, map_bernoulliMeasure, map_bernoulliMeasure]
  simp only [fairEstimator, ite_eq_left heven, ite_true, Bool.false_eq_true,
    ite_eq_right (by decide : ¬False), neg_neg]
  exact bernoulli_half_comm _ _

/-- A single Borel estimator is valid at every fixed strength; its independent
Bool seed gives the paper's fair law in even degree. -/
theorem exists_borel_mle (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    ∃ est : Model.Estimator N k Bool,
      (∀ lam : ℝ, Model.IsMLE N k lam est fairSeed) ∧
      (Even k → Model.HasSymmetricOutputLaw est fairSeed) := by
  cases k with
  | zero => exact False.elim (Nat.not_lt_zero 0 hk)
  | succ k => exact ⟨fairEstimator N k hN, fairEstimator_isMLE N k hN,
      fairEstimator_symmetric N k hN⟩

end
end TensorPCA.MleEstimatorProofs
