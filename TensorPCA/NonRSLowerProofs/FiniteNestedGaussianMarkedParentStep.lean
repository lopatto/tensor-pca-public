-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedIntegralStep
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedTransformDerivativeBinding

/-! Depth induction from the child series to the parent series. The proof uses finite-
PMF Faa coefficients and analyticity throughout the specified ball; smooth
derivatives alone do not suffice.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedParentStep
open MeasureTheory ProbabilityTheory Filter Set
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms
open FiniteNestedGaussianMarkedSeriesCoefficients FiniteNestedGaussianMarkedIntegralStep
open FiniteDiscountedTransformDerivativeBinding FiniteDiscountedPartitionProofs
open FiniteDiscountedPartitionCoefficients BoundedMarkedTaylorContinuation
open scoped NNReal ENNReal ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem tail_domain {depth : ℕ} (x : Fin (depth+1)→ℝ) {p : ℝ}
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1) :
    0<x 0 ∧ (∀j : Fin depth,x 0<x j.succ) ∧ StrictMono (fun j : Fin depth => x j.succ) ∧
      (∀j : Fin depth,x j.succ≤1) := by
  refine ⟨hp.trans_lt (hpx 0),fun j => hxm ?_,?_,fun j => hx1 j.succ⟩
  · change (0 : ℕ)<(j : ℕ)+1
    omega
  · intro i j hij
    exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)

theorem parent_jet_step (depth : ℕ) (x : Fin (depth+1)→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hchild : ∀z : E,HasFPowerSeriesOnBall
      (fun t => parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t z)
      (powerSeries depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z z) 0 R)
    (z : E) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun t => parentPower (depth+1) x p T Z t z) 0=
      (-p*normalizer p n)*weightedMoment (depth+1) n x p T Z z := by
  have HD := tail_domain x hp hpx hxm hx1
  have HS := integral_child_series depth (fun j => x j.succ) (x 0) HD.1.le (hx1 0)
    HD.2.1 HD.2.2.1 HD.2.2.2 (fun j => T j.succ) hZ ha hb R hR hAR hchild (T 0) z
  have HJ (j : ℕ) := integral_child_jet depth (fun j => x j.succ) (x 0) HD.1.le (hx1 0)
    HD.2.1 HD.2.2.1 HD.2.2.2 (fun j => T j.succ) hZ ha hb R hR hAR hchild (T 0) z j
  have hf0 : (∫g : E,parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z 0 (z+T 0 g) ∂stdGaussian E)=1 := by
    simp only [parentPower_zero,integral_const,probReal_univ,one_smul]
  have H := power_comp_derivative_eq_partition_moment (ne_of_gt HD.1) ((hpx 0).trans_le (hx1 0)) hn
    HS.analyticAt.contDiffAt hf0
    (fun j => ∫g : E,weightedMoment depth j (fun j => x j.succ) (x 0) (fun j => T j.succ) Z (z+T 0 g) ∂stdGaussian E)
    (fun j _ _ => HJ j)
  rw [weightedMoment_succ depth n x p T hZ ha hb z]
  exact H

theorem parent_taylor_coefficient_step (depth : ℕ) (x : Fin (depth+1)→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hchild : ∀z : E,HasFPowerSeriesOnBall
      (fun t => parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t z)
      (powerSeries depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z z) 0 R)
    (z : E) (n : ℕ) :
    iteratedDeriv n (fun t => parentPower (depth+1) x p T Z t z) 0/(n.factorial : ℝ)=
      powerCoefficient (depth+1) n x p T Z z := by
  cases n with
  | zero =>
    rw [powerCoefficient_zero (depth+1) x p hp hpx hxm hx1 T Z z]
    simp only [iteratedDeriv_zero,parentPower_zero,Nat.factorial_zero,Nat.cast_one,div_one]
  | succ n =>
    rw [parent_jet_step depth x p hp hpx hxm hx1 T hZ ha hb R hR hAR hchild z (Nat.succ_pos n),powerCoefficient]
    have HE : (-1 : ℝ)^(n+1)*(descPochhammer ℝ (n+1)).eval p= -p*normalizer p (n+1) := by
      simpa only [blockFactor,normalizer] using signed_desc_eq_blockFactor p n
    rw [HE]
    ring

theorem parent_analytic_step (depth : ℕ) (x : Fin (depth+1)→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hchild : ∀z : E,HasFPowerSeriesOnBall
      (fun t => parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t z)
      (powerSeries depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z z) 0 R)
    (z : E) : AnalyticOnNhd ℝ (fun t => parentPower (depth+1) x p T Z t z) (Metric.eball 0 R) := by
  have HD := tail_domain x hp hpx hxm hx1
  have HS := integral_child_series depth (fun j => x j.succ) (x 0) HD.1.le (hx1 0)
    HD.2.1 HD.2.2.1 HD.2.2.2 (fun j => T j.succ) hZ ha hb R hR hAR hchild (T 0) z
  intro t ht
  have HA := HS.analyticAt_of_mem ht
  have htR : |t|<(R : ℝ) := by
    rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq,sub_zero] at ht
    exact ht
  have hta : |t| *a<1 := (mul_le_mul_of_nonneg_right htR.le ha).trans_lt (by simpa only [mul_comm] using hAR)
  have hpos := integral_child_pos depth (fun j => x j.succ) (x 0) (fun j => T j.succ) hZ ha hb HD.1.le
    (fun j => HD.1.trans (HD.2.1 j)) hta (T 0) z
  have HL := ((HA.log hpos).mul (analyticAt_const (v := p/x 0))).rexp'
  apply HL.congr
  filter_upwards [HA.continuousAt.eventually (lt_mem_nhds hpos)] with s hs
  exact (Real.rpow_def_of_pos hs (p/x 0)).symm

theorem parent_series_step (depth : ℕ) (x : Fin (depth+1)→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hchild : ∀z : E,HasFPowerSeriesOnBall
      (fun t => parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t z)
      (powerSeries depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z z) 0 R)
    (z : E) : HasFPowerSeriesOnBall (fun t => parentPower (depth+1) x p T Z t z)
      (powerSeries (depth+1) x p T Z z) 0 R := by
  have HC := parent_taylor_coefficient_step depth x p hp hpx hxm hx1 T hZ ha hb R hR hAR hchild z
  have HS := hasFPowerSeriesOnBall_of_coefficient_bound ha R hR hAR.le
    (parent_analytic_step depth x p hp hpx hxm hx1 T hZ ha hb R hR hAR hchild z)
    (fun n => by rw [HC n]; exact powerCoefficient_abs_le (depth+1) n x p hp ((hpx 0).le.trans (hx1 0)) hpx hxm hx1 T hZ ha hb z)
  have HE : (fun n => iteratedDeriv n (fun t => parentPower (depth+1) x p T Z t z) 0/(n.factorial : ℝ))=
      (fun n => powerCoefficient (depth+1) n x p T Z z) := funext HC
  rw [HE] at HS
  exact HS

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedParentStep
