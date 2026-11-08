-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedPowerSeries

/-! Logarithmic-root reconstruction, distinct from the parent power at p=0, which is
constant one. Child expansions follow from the finite-depth parent theorem.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedRootSeries
open MeasureTheory ProbabilityTheory Filter Set
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms
open FiniteNestedGaussianMarkedSeriesCoefficients FiniteNestedGaussianMarkedIntegralStep
open FiniteNestedGaussianMarkedPowerSeries FiniteDiscountedTransformDerivativeBinding
open FiniteDiscountedPartitionProofs FiniteDiscountedPartitionCoefficients BoundedMarkedTaylorContinuation
open scoped NNReal ENNReal ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def rootCoefficient (depth n : ℕ) (x : Fin (depth+1)→ℝ)
    (T : Fin (depth+1)→E→L[ℝ]E) (Z : E→ℝ) (z : E) : ℝ :=
  if n=0 then 0 else (-normalizer 0 n/(n.factorial : ℝ))*weightedMoment (depth+1) n x 0 T Z z

private theorem tail_strict {depth : ℕ} (x : Fin (depth+1)→ℝ) (hxm : StrictMono x) :
    (∀j : Fin depth,x 0<x j.succ) ∧ StrictMono (fun j : Fin depth => x j.succ) := by
  refine ⟨fun j => hxm ?_,?_⟩
  · change (0 : ℕ)<(j : ℕ)+1
    omega
  · intro i j hij
    exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)

theorem root_jet (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (z : E) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun t => rootLog depth x T Z t z) 0=
      -normalizer 0 n*weightedMoment (depth+1) n x 0 T Z z := by
  have HT := tail_strict x hxm
  have hchild (y : E) := parent_series depth (fun j => x j.succ) (x 0) (hx 0).le (hx1 0)
    HT.1 HT.2 (fun j => hx1 j.succ) (fun j => T j.succ) hZ ha hb R hR hAR y
  have HS := integral_child_series depth (fun j => x j.succ) (x 0) (hx 0).le (hx1 0)
    HT.1 HT.2 (fun j => hx1 j.succ) (fun j => T j.succ) hZ ha hb R hR hAR hchild (T 0) z
  have HJ (j : ℕ) := integral_child_jet depth (fun j => x j.succ) (x 0) (hx 0).le (hx1 0)
    HT.1 HT.2 (fun j => hx1 j.succ) (fun j => T j.succ) hZ ha hb R hR hAR hchild (T 0) z j
  have hf0 : (∫g : E,parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z 0 (z+T 0 g) ∂stdGaussian E)=1 := by
    simp only [parentPower_zero,integral_const,probReal_univ,one_smul]
  have H := log_comp_derivative_eq_partition_moment (ne_of_gt (hx 0)) hn HS.analyticAt.contDiffAt hf0
    (fun j => ∫g : E,weightedMoment depth j (fun j => x j.succ) (x 0) (fun j => T j.succ) Z (z+T 0 g) ∂stdGaussian E)
    (fun j _ _ => HJ j)
  rw [weightedMoment_succ depth n x 0 T hZ ha hb z]
  exact H

theorem root_taylor_coefficient (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (z : E) (n : ℕ) :
    iteratedDeriv n (fun t => rootLog depth x T Z t z) 0/(n.factorial : ℝ)=rootCoefficient depth n x T Z z := by
  cases n with
  | zero => simp [rootLog_zero,rootCoefficient]
  | succ n =>
    rw [root_jet depth x hx hxm hx1 T hZ ha hb R hR hAR z (Nat.succ_pos n),rootCoefficient,if_neg (Nat.succ_ne_zero n)]
    ring

theorem rootCoefficient_succ_abs_le (depth n : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    |rootCoefficient depth (n+1) x T Z z|≤(1/((n+1 : ℕ) : ℝ))*a^(n+1) := by
  have HM := weightedMoment_mem (depth+1) (n+1) x 0 le_rfl hx hxm hx1 T hZ ha hb z
  have HC : (-normalizer 0 (n+1))/((n+1).factorial : ℝ)= -(1/((n+1 : ℕ) : ℝ)) := by
    rw [normalizer_zero_eq_factorial,Nat.factorial_succ,Nat.cast_mul]
    field_simp
  rw [rootCoefficient,if_neg (Nat.succ_ne_zero n),HC,abs_mul,abs_neg,
    abs_of_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)),abs_of_nonneg HM.1]
  exact mul_le_mul_of_nonneg_left HM.2 (div_nonneg zero_le_one (Nat.cast_nonneg _))

theorem root_series (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (z : E) : HasFPowerSeriesOnBall (fun t => rootLog depth x T Z t z)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => rootCoefficient depth n x T Z z)) 0 R := by
  have HT := tail_strict x hxm
  have hchild (y : E) := parent_series depth (fun j => x j.succ) (x 0) (hx 0).le (hx1 0)
    HT.1 HT.2 (fun j => hx1 j.succ) (fun j => T j.succ) hZ ha hb R hR hAR y
  have HS := integral_child_series depth (fun j => x j.succ) (x 0) (hx 0).le (hx1 0)
    HT.1 HT.2 (fun j => hx1 j.succ) (fun j => T j.succ) hZ ha hb R hR hAR hchild (T 0) z
  have HA : AnalyticOnNhd ℝ (fun t => rootLog depth x T Z t z) (Metric.eball 0 R) := by
    intro t ht
    have htR : |t|<(R : ℝ) := by
      rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq,sub_zero] at ht
      exact ht
    have hta : |t| *a<1 := (mul_le_mul_of_nonneg_right htR.le ha).trans_lt (by simpa only [mul_comm] using hAR)
    exact ((HS.analyticAt_of_mem ht).log (integral_child_pos depth (fun j => x j.succ) (x 0)
      (fun j => T j.succ) hZ ha hb (hx 0).le (fun j => hx j.succ) hta (T 0) z)).div_const
  have HC := root_taylor_coefficient depth x hx hxm hx1 T hZ ha hb R hR hAR z
  have HB (n : ℕ) : |rootCoefficient depth n x T Z z|≤a^n := by
    cases n with
    | zero => simp only [rootCoefficient,if_pos rfl,abs_zero,pow_zero]; norm_num
    | succ n =>
      have H := rootCoefficient_succ_abs_le depth n x hx hxm hx1 T hZ ha hb z
      have HD : 1/((n+1 : ℕ) : ℝ)≤1 := div_le_self zero_le_one (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      exact H.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right HD (pow_nonneg ha (n+1)))
  have H := hasFPowerSeriesOnBall_of_coefficient_bound ha R hR hAR.le HA (fun n => by rw [HC n]; exact HB n)
  have HE : (fun n => iteratedDeriv n (fun t => rootLog depth x T Z t z) 0/(n.factorial : ℝ))=
      (fun n => rootCoefficient depth n x T Z z) := funext HC
  rw [HE] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedRootSeries
