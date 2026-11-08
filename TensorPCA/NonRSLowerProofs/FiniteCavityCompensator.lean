-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.VariationalProofs

/-! Exact finite-degree covariance compensation for a bulk/cavity split.
This is finite polynomial algebra, including the degree-one block. It does
not assert an ASS inequality or a thermodynamic representation. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensator
open Finset
open scoped BigOperators
noncomputable section

def bulkRatio (N M : ℕ) : ℝ := (N : ℝ)/((N : ℝ)+M)

def degreeCompensator (N M p : ℕ) : ℝ :=
  (N : ℝ)/(M : ℝ)*(1-bulkRatio N M^(p-1))

theorem bulkRatio_nonneg (N M : ℕ) : 0≤bulkRatio N M := by
  unfold bulkRatio
  positivity

theorem bulkRatio_le_one (N M : ℕ) : bulkRatio N M≤1 := by
  unfold bulkRatio
  exact div_le_one_of_le₀ (le_add_of_nonneg_right (Nat.cast_nonneg M)) (by positivity)

theorem bulkRatio_lt_one (N : ℕ) {M : ℕ} (hM : 0<M) : bulkRatio N M<1 := by
  unfold bulkRatio
  exact (div_lt_one (by positivity)).2 (by exact_mod_cast Nat.lt_add_of_pos_right hM)

theorem one_sub_bulkRatio (N : ℕ) {M : ℕ} (hM : 0<M) :
    1-bulkRatio N M=(M : ℝ)/((N : ℝ)+M) := by
  unfold bulkRatio
  have h : (N : ℝ)+(M : ℝ)≠0 := by positivity
  field_simp
  ring

private theorem weighted_one_sub_ratio (N : ℕ) {M : ℕ} (hM : 0<M) :
    (N : ℝ)/(M : ℝ)*(1-bulkRatio N M)=bulkRatio N M := by
  rw [one_sub_bulkRatio N hM]
  unfold bulkRatio
  have h : (M : ℝ)≠0 := by positivity
  field_simp

private theorem geometric_compensation {r A : ℝ} (h : A*(1-r)=r) (n : ℕ) :
    A*(1-r^n)=∑ j∈range n,r^(j+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    calc
      A*(1-r^(n+1))=A*(1-r^n)+r^n*(A*(1-r)) := by rw [pow_succ]; ring
      _ = _ := by rw [ih,h,pow_succ]

theorem degreeCompensator_eq_sum (N p : ℕ) {M : ℕ} (hM : 0<M) :
    degreeCompensator N M p=∑ j∈range (p-1),bulkRatio N M^(j+1) :=
  geometric_compensation (weighted_one_sub_ratio N hM) (p-1)

@[simp] theorem degreeCompensator_one (N M : ℕ) : degreeCompensator N M 1=0 := by
  simp [degreeCompensator]

theorem degreeCompensator_nonneg (N p : ℕ) {M : ℕ} (hM : 0<M) :
    0≤degreeCompensator N M p := by
  rw [degreeCompensator_eq_sum N p hM]
  exact sum_nonneg (fun _ _ => pow_nonneg (bulkRatio_nonneg N M) _)

private theorem one_sub_pow_le (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) (n : ℕ) :
    1-r^n≤(n : ℝ)*(1-r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : r^n≤1 := pow_le_one₀ hr0 hr1
    have hmul := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hr1)
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith

private theorem geometric_compensation_error (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) (n : ℕ) :
    0≤(n : ℝ)-(∑ j∈range n,r^(j+1)) ∧
    (n : ℝ)-(∑ j∈range n,r^(j+1))≤(1-r)*(n : ℝ)*((n : ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : r^(n+1)≤1 := pow_le_one₀ hr0 hr1
    have he := one_sub_pow_le r hr0 hr1 (n+1)
    rw [sum_range_succ,Nat.cast_add,Nat.cast_one]
    rw [Nat.cast_add,Nat.cast_one] at he
    constructor <;> nlinarith

theorem degreeCompensator_error (N p : ℕ) {M : ℕ} (hM : 0<M) (hp : 1≤p) :
    0≤((p-1 : ℕ) : ℝ)-degreeCompensator N M p ∧
    ((p-1 : ℕ) : ℝ)-degreeCompensator N M p≤
      (M : ℝ)/((N : ℝ)+M)*(p : ℝ)*((p-1 : ℕ) : ℝ)/2 := by
  rw [degreeCompensator_eq_sum N p hM]
  have H := geometric_compensation_error (bulkRatio N M)
    (bulkRatio_nonneg N M) (bulkRatio_le_one N M) (p-1)
  rw [one_sub_bulkRatio N hM] at H
  have he : ((p-1 : ℕ) : ℝ)+1=(p : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hp
  simpa only [he,mul_comm ((p-1 : ℕ) : ℝ) (p : ℝ),mul_assoc] using H

theorem exact_bulk_compensation (N p : ℕ) {M : ℕ} (hM : 0<M) (hN : 0<N) :
    bulkRatio N M^(p-1)+(M : ℝ)/(N : ℝ)*degreeCompensator N M p=1 := by
  unfold degreeCompensator
  have hn : (N : ℝ)≠0 := by positivity
  have hm : (M : ℝ)≠0 := by positivity
  field_simp
  ring


end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensator
