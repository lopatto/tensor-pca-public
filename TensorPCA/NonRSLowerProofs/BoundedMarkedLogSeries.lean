-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedIIDMarkedMoments

/-! Uniform logarithmic polynomial tails for bounded nonnegative marks. The finite
moment comparison below leaves only finitely many moment discrepancies, with all
logarithmic integrability proved.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedLogSeries
open MeasureTheory ProbabilityTheory
open FiniteDiscountedIIDMarkedMoments
open scoped BigOperators Topology
noncomputable section
variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]

theorem log_polynomial_error_le {a z : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hz0 : 0≤z) (hza : z≤a) (n : ℕ) :
    |(∑i∈Finset.range n,z^(i+1)/((i+1 : ℕ) : ℝ))+Real.log (1-z)|≤a^(n+1)/(1-a) := by
  have hz1 : |z|<1 := by rw [abs_of_nonneg hz0]; exact hza.trans_lt ha1
  have H := Real.abs_log_sub_add_sum_range_le hz1 n
  rw [abs_of_nonneg hz0] at H
  have HB : z^(n+1)/(1-z)≤a^(n+1)/(1-a) := div_le_div₀ (pow_nonneg ha0 _)
    (pow_le_pow_left₀ hz0 hza _) (sub_pos.mpr ha1) (by linarith only [hza])
  simpa only [Nat.cast_add,Nat.cast_one] using H.trans HB

theorem bounded_mark_log_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) :
    Integrable (fun v => Real.log (1-Z v)) nu := by
  have hm : Measurable (fun v => Real.log (1-Z v)) := (measurable_const.sub hZ).log
  apply Integrable.of_bound hm.aestronglyMeasurable (a/(1-a))
  filter_upwards [hb] with v hv
  simpa only [Finset.range_zero,Finset.sum_empty,zero_add,pow_one,Real.norm_eq_abs] using
    log_polynomial_error_le ha0 ha1 hv.1 hv.2 0

theorem expected_log_polynomial_error_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (n : ℕ) :
    |(∑i∈Finset.range n,(∫v,(Z v)^(i+1) ∂nu)/((i+1 : ℕ) : ℝ))+
      (∫v,Real.log (1-Z v) ∂nu)|≤a^(n+1)/(1-a) := by
  have hi (i : ℕ) : Integrable (fun v => (Z v)^(i+1)/((i+1 : ℕ) : ℝ)) nu :=
    (bounded_mark_power_integrable nu hZ ha0 hb (i+1)).div_const _
  have hp : Integrable (fun v => ∑i∈Finset.range n,(Z v)^(i+1)/((i+1 : ℕ) : ℝ)) nu :=
    integrable_finset_sum _ (fun i _ => hi i)
  have HL := bounded_mark_log_integrable nu hZ ha0 ha1 hb
  have H := norm_integral_le_of_norm_le_const (μ := nu)
    (f := fun v => (∑i∈Finset.range n,(Z v)^(i+1)/((i+1 : ℕ) : ℝ))+Real.log (1-Z v))
    (hb.mono (fun v hv => by
      rw [Real.norm_eq_abs]
      exact log_polynomial_error_le ha0 ha1 hv.1 hv.2 n))
  rw [integral_add hp HL,integral_finset_sum _ (fun i _ => hi i)] at H
  simpa only [integral_div,Real.norm_eq_abs,probReal_univ,mul_one] using H

theorem expected_log_sub_le_finite_moments
    (nu : Measure V) [IsProbabilityMeasure nu] (mu : Measure W) [IsProbabilityMeasure mu]
    {Z : V→ℝ} {Y : W→ℝ} (hZ : Measurable Z) (hY : Measurable Y)
    {a : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hbZ : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (hbY : ∀ᵐw∂mu,0≤Y w ∧ Y w≤a) (n : ℕ) :
    |(∫v,Real.log (1-Z v) ∂nu)-(∫w,Real.log (1-Y w) ∂mu)|≤
      2*(a^(n+1)/(1-a))+
        ∑i∈Finset.range n,|(∫v,(Z v)^(i+1) ∂nu)-(∫w,(Y w)^(i+1) ∂mu)|/((i+1 : ℕ) : ℝ) := by
  let P := ∑i∈Finset.range n,(∫v,(Z v)^(i+1) ∂nu)/((i+1 : ℕ) : ℝ)
  let Q := ∑i∈Finset.range n,(∫w,(Y w)^(i+1) ∂mu)/((i+1 : ℕ) : ℝ)
  have hP := expected_log_polynomial_error_le nu hZ ha0 ha1 hbZ n
  have hQ := expected_log_polynomial_error_le mu hY ha0 ha1 hbY n
  have hPQ : |P-Q|≤∑i∈Finset.range n,
      |(∫v,(Z v)^(i+1) ∂nu)-(∫w,(Y w)^(i+1) ∂mu)|/((i+1 : ℕ) : ℝ) := by
    unfold P Q
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑i∈Finset.range n,|(∫v,(Z v)^(i+1) ∂nu)/((i+1 : ℕ) : ℝ)-
        (∫w,(Y w)^(i+1) ∂mu)/((i+1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← sub_div,abs_div]
        congr 1
        exact abs_of_pos (Nat.cast_pos.mpr (Nat.succ_pos i))
  have hP' := abs_le.mp hP
  have hQ' := abs_le.mp hQ
  have hPQ' := abs_le.mp hPQ
  change |(∫v,Real.log (1-Z v) ∂nu)-(∫w,Real.log (1-Y w) ∂mu)|≤_
  apply abs_le.mpr
  constructor <;> dsimp only [P,Q] at hPQ' <;> linarith only [hP'.1,hP'.2,hQ'.1,hQ'.2,hPQ'.1,hPQ'.2]

theorem expected_log_sub_le_of_moment_le
    (nu : Measure V) [IsProbabilityMeasure nu] (mu : Measure W) [IsProbabilityMeasure mu]
    {Z : V→ℝ} {Y : W→ℝ} (hZ : Measurable Z) (hY : Measurable Y)
    {a : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hbZ : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (hbY : ∀ᵐw∂mu,0≤Y w ∧ Y w≤a)
    (n : ℕ) {delta : ℝ}
    (hmoment : ∀i<n,|(∫v,(Z v)^(i+1) ∂nu)-(∫w,(Y w)^(i+1) ∂mu)|≤delta) :
    |(∫v,Real.log (1-Z v) ∂nu)-(∫w,Real.log (1-Y w) ∂mu)|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  have HS : (∑i∈Finset.range n,
      |(∫v,(Z v)^(i+1) ∂nu)-(∫w,(Y w)^(i+1) ∂mu)|/((i+1 : ℕ) : ℝ))≤(n : ℝ)*delta := by
    calc
      _ ≤ ∑_i∈Finset.range n,delta := by
        apply Finset.sum_le_sum
        intro i hi
        exact (div_le_self (abs_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i))).trans
          (hmoment i (Finset.mem_range.mp hi))
      _ = _ := by simp
  exact (expected_log_sub_le_finite_moments nu mu hZ hY ha0 ha1 hbZ hbY n).trans
    (add_le_add le_rfl HS)

theorem log_tail_tendsto_zero {a : ℝ} (ha0 : 0≤a) (ha1 : a<1) :
    Filter.Tendsto (fun n : ℕ => a^(n+1)/(1-a)) Filter.atTop (𝓝 0) := by
  have H := ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const a).div_const (1-a)
  simpa only [pow_succ,zero_mul,zero_div] using H

theorem exists_log_approximation_parameters {a eta : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (heta : 0<eta) :
    ∃n : ℕ,∃delta : ℝ,0<delta ∧ 2*(a^(n+1)/(1-a))+(n : ℝ)*delta≤eta := by
  have H := (log_tail_tendsto_zero ha0 ha1).eventually (gt_mem_nhds (by linarith : (0 : ℝ)<eta/4))
  obtain ⟨n,hn⟩ := Filter.eventually_atTop.mp H
  let delta := eta/(2*((n : ℝ)+1))
  have hd : 0<delta := div_pos heta (by positivity)
  have hdEq : 2*((n : ℝ)+1)*delta=eta := by dsimp only [delta]; field_simp
  refine ⟨n,delta,hd,?_⟩
  have HT := hn n le_rfl
  nlinarith only [HT,hd.le,hdEq]

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedLogSeries
