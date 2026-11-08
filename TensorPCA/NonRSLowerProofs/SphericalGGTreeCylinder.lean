-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionOverlap
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMoment
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Threshold cylinders of the finite Tree, with cuts distinct from analytic covariance
nodes. The discount height is the lower-tail probability Iio cuts under the
amplitude's pair law, complementary to Ici cuts; threshold atoms remain on the upper
side.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeCylinder
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedPartitionOverlap SphericalGGJetFamily
open scoped BigOperators
noncomputable section

def treeCylinder {N depth n : ℕ} (cuts : Fin depth → ℝ) (t : NestedPartition depth n)
    (old : Fin n → UnitSpin N) : Prop :=
  ∀ l : Fin depth,∀ i j : Fin n,(l.val<coalescence t i j ↔ cuts l≤unitOverlap (old i) (old j))

def ballSize {depth n : ℕ} (t : NestedPartition depth n) (l : Fin depth) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j ↦ l.val<coalescence t i j)).card

def lowerHeight {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (cut : ℝ) (x : Fin K → ℝ) : ℝ :=
  pairMean nu v ((Iio cut).indicator (fun _ ↦ (1 : ℝ))) x

theorem treeCylinder_measurable {N depth n : ℕ} (cuts : Fin depth → ℝ) (t : NestedPartition depth n) :
    MeasurableSet {old : Fin n → UnitSpin N | treeCylinder cuts t old} := by
  have hR (i j : Fin n) : Measurable (fun old : Fin n → UnitSpin N ↦ unitOverlap (old i) (old j)) := by
    have hPair : Measurable (fun old : Fin n → UnitSpin N ↦ (old i,old j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    simpa only [Function.comp_def] using (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair
  have hAtom (l : Fin depth) (i j : Fin n) :
      MeasurableSet {old : Fin n → UnitSpin N | l.val<coalescence t i j ↔ cuts l≤unitOverlap (old i) (old j)} := by
    by_cases h : l.val<coalescence t i j
    · simpa only [h,true_iff] using measurableSet_le measurable_const (hR i j)
    · simpa only [h,false_iff,not_le] using measurableSet_lt (hR i j) measurable_const
  simp only [treeCylinder,Set.setOf_forall]
  exact MeasurableSet.iInter (fun l ↦ MeasurableSet.iInter (fun i ↦ MeasurableSet.iInter (fun j ↦ hAtom l i j)))

theorem treeCylinder_row_sum {N depth n : ℕ} (cuts : Fin depth → ℝ) (t : NestedPartition depth n)
    (old : Fin n → UnitSpin N) (h : treeCylinder cuts t old) (l : Fin depth) (i : Fin n) :
    (∑ j,(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) (unitOverlap (old i) (old j)))=(ballSize t l i : ℝ) := by
  have hEach (j : Fin n) : (Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) (unitOverlap (old i) (old j))=
      if l.val<coalescence t i j then (1 : ℝ) else 0 := by
    by_cases hc : l.val<coalescence t i j
    · rw [if_pos hc,Set.indicator_of_mem (show unitOverlap (old i) (old j)∈Ici (cuts l) from (h l i j).mp hc)]
    · rw [if_neg hc,Set.indicator_of_notMem (show unitOverlap (old i) (old j)∉Ici (cuts l) from fun hr ↦ hc ((h l i j).mpr hr))]
  simp_rw [hEach]
  exact Finset.sum_boole _ _

theorem treeCylinder_self_indicator {N depth n : ℕ} (cuts : Fin depth → ℝ) (t : NestedPartition depth n)
    (old : Fin n → UnitSpin N) (h : treeCylinder cuts t old) (l : Fin depth) (i : Fin n) :
    (Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) (unitOverlap (old i) (old i))=1 := by
  have hSelf : l.val<coalescence t i i := by simpa only [coalescence_self] using l.isLt
  exact Set.indicator_of_mem ((h l i i).mp hSelf) _

theorem treeCylinder_offdiag_row_sum {N depth n : ℕ} (cuts : Fin depth → ℝ)
    (t : NestedPartition depth (n+1)) (old : Fin (n+1) → UnitSpin N) (h : treeCylinder cuts t old)
    (l : Fin depth) (i : Fin (n+1)) :
    (∑ j : Fin n,(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ))
      (unitOverlap (old i) (old (i.succAbove j))))=(ballSize t l i : ℝ)-1 := by
  have H := treeCylinder_row_sum cuts t old h l i
  rw [Fin.sum_univ_succAbove _ i,treeCylinder_self_indicator cuts t old h l i] at H
  linarith only [H]

theorem lowerHeight_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cut : ℝ) : Measurable (lowerHeight (K := K) nu v cut) := by
  exact pairMean_measurable nu hv (measurable_const.indicator measurableSet_Iio) (B := 1)
    (fun r ↦ by by_cases h : r∈Iio cut <;> simp [h])

theorem lowerHeight_mem_Icc {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cut : ℝ) (x : Fin K → ℝ) : lowerHeight nu v cut x∈Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun r ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _),?_⟩
  exact (le_abs_self _).trans (pairMean_abs_le nu hv
    (fun r ↦ by by_cases h : r∈Iio cut <;> simp [h]) x)

theorem lowerHeight_add_upper {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cut : ℝ) (x : Fin K → ℝ) :
    lowerHeight nu v cut x+pairMean nu v ((Ici cut).indicator (fun _ ↦ (1 : ℝ))) x=1 := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let rho := (((((parameterizedGibbsKernel nu v).sectR x) ×ₖ
    ((parameterizedGibbsKernel nu v).sectR x)) ∘ₘ
      SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)).map
        (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2))
  have hLower : Integrable ((Iio cut).indicator (fun _ ↦ (1 : ℝ))) rho := (integrable_const _).indicator measurableSet_Iio
  have hUpper : Integrable ((Ici cut).indicator (fun _ ↦ (1 : ℝ))) rho := (integrable_const _).indicator measurableSet_Ici
  have hPoint (r : ℝ) : (Iio cut).indicator (fun _ ↦ (1 : ℝ)) r+(Ici cut).indicator (fun _ ↦ (1 : ℝ)) r=1 := by
    by_cases h : r∈Iio cut
    · simp only [Set.indicator_of_mem h,Set.indicator_of_notMem (show r∉Ici cut from not_le.mpr h),add_zero]
    · simp only [Set.indicator_of_notMem h,Set.indicator_of_mem (show r∈Ici cut from le_of_not_gt h),zero_add]
  change (∫ r,(Iio cut).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)+
    (∫ r,(Ici cut).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)=1
  rw [← integral_add hLower hUpper]
  simp only [hPoint,integral_const,probReal_univ,smul_eq_mul,mul_one]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeCylinder
