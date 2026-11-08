-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- The CDF monotonicity/right-continuity construction is a narrow adaptation of
-- the Apache-2.0 recoveryCDF block from
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SourceLiteratureGroundStateFinal.lean
-- Its terminal value is the actual truncated profile rate, without a thermal
-- normalization or a probability assumption.
module
public import TensorPCA.JTProfileRepresentationProofs
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Finite curvature measures on compact initial subintervals. The atom
at zero records the initial negative slope of the admissible profile. -/
@[expose] public section
namespace TensorPCA.JTCurvatureMeasureProofs
open Set Filter MeasureTheory JTProfileRepresentationProofs
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def curvatureCDF (p : ℝ → ℝ) (r t : ℝ) : ℝ :=
  if t < 0 then 0 else profileRate p (min t r)

theorem curvatureCDF_monotone {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) : Monotone (curvatureCDF p r) := by
  intro s t hst
  by_cases hs : s < 0
  · by_cases ht : t < 0
    · simp only [curvatureCDF,ite_eq_left hs,ite_eq_left ht,le_refl]
    · simp only [curvatureCDF,ite_eq_left hs,ite_eq_right ht]
      exact profileRate_nonneg hp ((min_le_right t r).trans_lt hr.2)
  · have ht : ¬t < 0 := not_lt.mpr ((le_of_not_gt hs).trans hst)
    simp only [curvatureCDF,ite_eq_right hs,ite_eq_right ht]
    exact profileRate_monotone hp ((min_le_right s r).trans_lt hr.2)
      ((min_le_right t r).trans_lt hr.2) (min_le_min hst le_rfl)

theorem curvatureCDF_rightContinuous {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (s : ℝ) :
    ContinuousWithinAt (curvatureCDF p r) (Ici s) s := by
  by_cases hs : s < 0
  · apply continuousWithinAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℝ))
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hs)] with t ht
      simp only [curvatureCDF,ite_eq_left (show t < 0 from ht)]
    · simp only [curvatureCDF,ite_eq_left hs]
  · by_cases hsr : s < r
    · apply (profileRate_rightContinuous hp (hsr.trans hr.2)).congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds hsr)] with t hst htr
        simp only [curvatureCDF,ite_eq_right (not_lt.mpr ((le_of_not_gt hs).trans hst)),
          min_eq_left htr.le]
      · simp only [curvatureCDF,ite_eq_right hs,min_eq_left hsr.le]
    · apply continuousWithinAt_const.congr_of_eventuallyEq
        (f := fun _ => profileRate p r)
      · filter_upwards [self_mem_nhdsWithin] with t hst
        have hrt : r ≤ t := (le_of_not_gt hsr).trans hst
        simp only [curvatureCDF,ite_eq_right (not_lt.mpr (hr.1.trans hrt)),min_eq_right hrt]
      · simp only [curvatureCDF,ite_eq_right hs,min_eq_right (le_of_not_gt hsr)]

def curvatureStieltjes {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) : StieltjesFunction ℝ where
  toFun := curvatureCDF p r
  mono' := curvatureCDF_monotone hp hr
  right_continuous' := curvatureCDF_rightContinuous hp hr

theorem curvatureStieltjes_atBot {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    Tendsto (curvatureStieltjes hp hr) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  simp only [curvatureStieltjes,curvatureCDF,ite_eq_left ht]

theorem curvatureStieltjes_atTop {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    Tendsto (curvatureStieltjes hp hr) atTop (𝓝 (profileRate p r)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop r] with t ht
  simp only [curvatureStieltjes,curvatureCDF,ite_eq_right (not_lt.mpr (hr.1.trans ht)),
    min_eq_right ht]

def curvatureMeasure {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) : Measure ℝ := (curvatureStieltjes hp hr).measure

instance curvatureMeasure_finite {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) : IsFiniteMeasure (curvatureMeasure hp hr) :=
  (curvatureStieltjes hp hr).isFiniteMeasure
    (curvatureStieltjes_atBot hp hr) (curvatureStieltjes_atTop hp hr)

theorem curvatureMeasure_Iic {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) r) :
    curvatureMeasure hp hr (Iic t) = ENNReal.ofReal (profileRate p t) := by
  rw [curvatureMeasure,(curvatureStieltjes hp hr).measure_Iic (curvatureStieltjes_atBot hp hr)]
  simp only [curvatureStieltjes,curvatureCDF,ite_eq_right (not_lt.mpr ht.1),min_eq_left ht.2,sub_zero]

theorem curvatureMeasure_univ {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    curvatureMeasure hp hr univ = ENNReal.ofReal (profileRate p r) := by
  rw [curvatureMeasure,(curvatureStieltjes hp hr).measure_univ
    (curvatureStieltjes_atBot hp hr) (curvatureStieltjes_atTop hp hr),sub_zero]

theorem curvatureStieltjes_leftLim_zero {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    Function.leftLim (curvatureStieltjes hp hr) 0 = 0 := by
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [curvatureStieltjes,curvatureCDF,ite_eq_left (show t < 0 from ht)]

theorem curvatureMeasure_singleton_zero {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    curvatureMeasure hp hr {0} = ENNReal.ofReal (profileRate p 0) := by
  rw [curvatureMeasure,(curvatureStieltjes hp hr).measure_singleton,
    curvatureStieltjes_leftLim_zero hp hr]
  simp only [curvatureStieltjes,curvatureCDF,ite_eq_right (show ¬(0 : ℝ) < 0 from lt_irrefl _),
    min_eq_left hr.1,sub_zero]

theorem curvatureMeasure_ae_mem {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ t ∂curvatureMeasure hp hr, t ∈ Icc (0 : ℝ) r := by
  have hneg : curvatureMeasure hp hr (Iio (0 : ℝ)) = 0 := by
    rw [curvatureMeasure,(curvatureStieltjes hp hr).measure_Iio
      (curvatureStieltjes_atBot hp hr),curvatureStieltjes_leftLim_zero hp hr]
    simp only [sub_self,ENNReal.ofReal_zero]
  have hpos : curvatureMeasure hp hr (Ioi r) = 0 := by
    rw [curvatureMeasure,(curvatureStieltjes hp hr).measure_Ioi
      (curvatureStieltjes_atTop hp hr)]
    simp only [curvatureStieltjes,curvatureCDF,ite_eq_right (not_lt.mpr hr.1),
      min_self,sub_self,ENNReal.ofReal_zero]
  rw [ae_iff]
  have he : {t : ℝ | ¬t ∈ Icc (0 : ℝ) r} = Iio 0 ∪ Ioi r := by
    ext t
    simp only [mem_ofPred_eq,mem_Icc,not_and_or,not_le,mem_union,mem_Iio,mem_Ioi]
  rw [he]
  exact measure_union_null hneg hpos


end
end TensorPCA.JTCurvatureMeasureProofs
