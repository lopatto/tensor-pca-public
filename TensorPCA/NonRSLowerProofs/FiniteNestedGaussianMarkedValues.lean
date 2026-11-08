-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedRootSeries

/-! Nested Gaussian values at t=1 and uniform finite-moment tails. The root value is
reconstructed from unconditional nested-PMF moments, without conditioning an
approximate moment identity on a rare parent event.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedValues
open MeasureTheory ProbabilityTheory Set
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms
open FiniteNestedGaussianMarkedPowerSeries FiniteNestedGaussianMarkedRootSeries
open FiniteNestedGaussianMarkedSeriesCoefficients FiniteDiscountedPartitionProofs
open FiniteDiscountedPartitionCoefficients
open scoped BigOperators NNReal ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem exists_radius {a : ℝ} (ha : 0≤a) (ha1 : a<1) :
    ∃R : ℝ≥0,1<(R : ℝ) ∧ a*(R : ℝ)<1 := by
  have hd : 0<a+1 := by linarith
  refine ⟨⟨2/(a+1),(div_pos (by norm_num) hd).le⟩,?_,?_⟩
  · exact (lt_div_iff₀ hd).mpr (by linarith)
  · change a*(2/(a+1))<1
    rw [← mul_div_assoc,div_lt_iff₀ hd]
    linarith

theorem parent_positive_order_hasSum (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    HasSum (fun n : ℕ => powerCoefficient depth (n+1) x p T Z z) (parentPower depth x p T Z 1 z-1) := by
  obtain ⟨R,hR1,hAR⟩ := exists_radius ha ha1
  have hR : 0<R := by exact_mod_cast (zero_lt_one.trans hR1)
  have HS := parent_series depth x p hp hp1 hpx hxm hx1 T hZ ha hb R hR hAR z
  have h1 : (1 : ℝ)∈Metric.eball 0 (R : ℝ≥0∞) := by
    rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq]
    simpa using hR1
  have H := HS.hasSum h1
  simp only [powerSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,one_pow,mul_one,zero_add] at H
  have HH := (hasSum_nat_add_iff' 1).mpr H
  simpa only [Finset.sum_range_one,powerCoefficient_zero depth x p hp hpx hxm hx1 T Z z] using HH

theorem parent_polynomial_error_le (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) (n : ℕ) :
    |1+(∑j∈Finset.range n,powerCoefficient depth (j+1) x p T Z z)-parentPower depth x p T Z 1 z|≤
      p*(a^(n+1)/(1-a)) := by
  have HB (j : ℕ) : ‖powerCoefficient depth (j+1) x p T Z z‖≤(p*a)*a^j := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (p/((j+1 : ℕ) : ℝ))*a^(j+1) := powerCoefficient_succ_abs_le depth j x p hp hp1 hpx hxm hx1 T hZ ha hb z
      _ ≤ p*a^(j+1) := mul_le_mul_of_nonneg_right
        (div_le_self hp (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))) (pow_nonneg ha _)
      _ = _ := by rw [pow_succ]; ring
  have H := norm_sub_le_of_geometric_bound_of_hasSum ha1 HB
    (parent_positive_order_hasSum depth x p hp hp1 hpx hxm hx1 T hZ ha ha1 hb z) n
  rw [Real.norm_eq_abs] at H
  convert H using 1
  · congr 1
    ring
  · rw [pow_succ]
    ring

theorem rootCoefficient_succ_eq (depth n : ℕ) (x : Fin (depth+1)→ℝ)
    (T : Fin (depth+1)→E→L[ℝ]E) (Z : E→ℝ) (z : E) :
    rootCoefficient depth (n+1) x T Z z= -(1/((n+1 : ℕ) : ℝ))*weightedMoment (depth+1) (n+1) x 0 T Z z := by
  have HC : (-normalizer 0 (n+1))/((n+1).factorial : ℝ)= -(1/((n+1 : ℕ) : ℝ)) := by
    rw [normalizer_zero_eq_factorial,Nat.factorial_succ,Nat.cast_mul]
    field_simp
  rw [rootCoefficient,if_neg (Nat.succ_ne_zero n),HC]

theorem root_moment_hasSum (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    HasSum (fun n : ℕ => (1/((n+1 : ℕ) : ℝ))*weightedMoment (depth+1) (n+1) x 0 T Z z)
      (-rootLog depth x T Z 1 z) := by
  obtain ⟨R,hR1,hAR⟩ := exists_radius ha ha1
  have hR : 0<R := by exact_mod_cast (zero_lt_one.trans hR1)
  have HS := root_series depth x hx hxm hx1 T hZ ha hb R hR hAR z
  have h1 : (1 : ℝ)∈Metric.eball 0 (R : ℝ≥0∞) := by
    rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq]
    simpa using hR1
  have H := HS.hasSum h1
  simp only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,one_pow,mul_one,zero_add] at H
  have HH := ((hasSum_nat_add_iff' 1).mpr H).neg
  have H0 : rootCoefficient depth 0 x T Z z=0 := by simp [rootCoefficient]
  simpa only [Finset.sum_range_one,H0,sub_zero,rootCoefficient_succ_eq,
    neg_mul,neg_neg] using HH

theorem root_polynomial_error_le (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) (n : ℕ) :
    |(∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) x 0 T Z z)-
      (-rootLog depth x T Z 1 z)|≤a^(n+1)/(1-a) := by
  have HB (j : ℕ) : ‖(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) x 0 T Z z‖≤a*a^j := by
    have HM := weightedMoment_mem (depth+1) (j+1) x 0 le_rfl hx hxm hx1 T hZ ha hb z
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)),abs_of_nonneg HM.1]
    calc
      _ ≤ 1*a^(j+1) := mul_le_mul (div_le_self zero_le_one (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))) HM.2 HM.1 zero_le_one
      _ = _ := by rw [one_mul,pow_succ]; ring
  have H := norm_sub_le_of_geometric_bound_of_hasSum ha1 HB
    (root_moment_hasSum depth x hx hxm hx1 T hZ ha ha1 hb z) n
  simpa only [Real.norm_eq_abs,pow_succ,mul_comm] using H

theorem rootLog_measurable (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) (t : ℝ) :
    Measurable (fun z : E => rootLog depth x T Z t z) := by
  have hm : Measurable (fun zg : E×E =>
      parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t (zg.1+T 0 zg.2)) :=
    (parentPower_measurable depth (fun j => x j.succ) (x 0) (fun j => T j.succ) hZ).comp
      (measurable_const.prodMk (measurable_fst.add ((T 0).continuous.measurable.comp measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.log.div_const (x 0)

theorem rootLog_integrable (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a) (eta : Measure E) [IsProbabilityMeasure eta] :
    Integrable (fun z : E => rootLog depth x T Z 1 z) eta := by
  apply Integrable.of_bound (rootLog_measurable depth x T hZ 1).aestronglyMeasurable (a/(1-a))
  exact ae_of_all _ (fun z => by
    have H := root_polynomial_error_le depth x hx hxm hx1 T hZ ha ha1 hb z 0
    simpa only [Finset.sum_range_zero,zero_sub,abs_neg,neg_neg,Nat.zero_add,pow_one,Real.norm_eq_abs] using H)

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedValues
