-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Exact physical leading-rate transfer adapted from immutable
 pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
 GOEPhysicalPrefactors.lean (finite scale lower bound),
 GOEPhysicalWholeLinePotential.lean and GOEPhysicalLeadingUpper.lean.
 Only the genuine standard ordinary-mean input is parameterized. Actual law
 scaling and all-real semicircle dimension bounds are proved imports.
 No eigenvalue or physical maximum conclusion is assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GOEPhysicalMeanScalingProofs
public import TensorPCA.RetainedCountProofs.SemicircleDimensionScaling
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEPhysicalFirstMeanUpperProofs
noncomputable section
open Set Filter
open scoped Topology
open GOEScaling GOEPhysicalPotential GOEPhysicalMeanScalingProofs SemicirclePotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma scaleFactor_lower (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    Real.sqrt (b/(j+1 : ℝ)) ≤ scaleFactor n (n+1+j) b := by
  apply Real.sqrt_le_sqrt
  have hj : (0 : ℝ) < j+1 := by positivity
  have hN : (0 : ℝ) < (n+1+j : ℕ) := by positivity
  apply (div_le_div_iff₀ hj hN).mpr
  have hn : (0 : ℝ) ≤ n := by positivity
  have hjn : (0 : ℝ) ≤ j := by positivity
  simp only [Nat.cast_add,Nat.cast_one]
  nlinarith [mul_nonneg hn hjn]

lemma scaled_shift_mem (n j : ℕ) {b Z k : ℝ} (hb : 0 < b) (hZ : 0 ≤ Z) (hk : |k| ≤ Z) :
    k/scaleFactor n (n+1+j) b ∈
      Icc (-Z/Real.sqrt (b/(j+1 : ℝ))) (Z/Real.sqrt (b/(j+1 : ℝ))) := by
  have ha := scaleFactor_pos n (by omega : 0 < n+1+j) hb
  have hl : 0 < Real.sqrt (b/(j+1 : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hbound : |k/scaleFactor n (n+1+j) b| ≤ Z/Real.sqrt (b/(j+1 : ℝ)) := by
    rw [abs_div,abs_of_pos ha]
    exact (div_le_div_of_nonneg_right hk ha.le).trans
      (div_le_div_of_nonneg_left hZ hl (scaleFactor_lower n j hb.le))
  change -Z/Real.sqrt (b/(j+1 : ℝ)) ≤ k/scaleFactor n (n+1+j) b ∧
    k/scaleFactor n (n+1+j) b ≤ Z/Real.sqrt (b/(j+1 : ℝ))
  simpa only [neg_div] using abs_le.mp hbound

/-- All-real finite-dimensional rate comparison with its exact codimension
correction. No matrix asymptotic is needed for this deterministic inequality. -/
lemma scaled_rate_le (n j : ℕ) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    (n+1 : ℝ)*(Real.log (scaleFactor n (n+1+j) b)+
      potential (k/scaleFactor n (n+1+j) b)) ≤
      (n+1+j : ℕ)*(Real.log b/2+potential (k/Real.sqrt b))+
        (j : ℝ)*(1+|Real.log b|)/2 := by
  let N : ℕ := n+1+j
  let τ : ℝ := (n+1 : ℝ)/(N : ℝ)
  have hN : 0 < (N : ℝ) := by dsimp only [N]; positivity
  have hτ : 0 < τ := div_pos (by positivity) hN
  have hτ1 : τ ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    dsimp only [N]
    norm_cast
    omega
  have ht := physical_rate_dimension_scaling_le hb hτ hτ1 k
  have ha : scaleFactor n N b = Real.sqrt (b*τ) := by
    unfold scaleFactor
    dsimp only [τ]
    congr 1
    ring
  have hp : 0 < b*τ := mul_pos hb hτ
  have hrate : (n+1 : ℝ)*(Real.log (scaleFactor n N b)+potential (k/scaleFactor n N b)) =
      (n+1 : ℝ)*(Real.log (b*τ)/2+potential (k/Real.sqrt (b*τ))) := by
    rw [ha,Real.log_sqrt hp.le]
  rw [hrate]
  have hh := mul_le_mul_of_nonneg_left ht hN.le
  have hleft : (N : ℝ)*τ = (n+1 : ℝ) := by dsimp only [τ]; field_simp
  have hright : (N : ℝ)*(1-τ) = j := by
    dsimp only [τ,N]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  rw [← mul_assoc,hleft] at hh
  have he : (N : ℝ)*((1-τ)*(1+|Real.log b|)/2) = (j : ℝ)*(1+|Real.log b|)/2 := by
    rw [mul_div_assoc,← mul_assoc,hright]
    ring
  conv_rhs at hh => rw [mul_add]
  rw [he] at hh
  exact hh

/-- A genuine standard-law ordinary-mean estimate transfers to every physical
variance and fixed codimension, uniformly over bounded real shifts. -/
theorem physical_mean_leading_upper_uniform_of_standard
    (hstd : ∀ {S : Set ℝ}, IsCompact S → ∀ {eps : ℝ}, 0 < eps →
      ∀ᶠ n : ℕ in atTop, ∀ k ∈ S,
        physicalMean n (n+1) 1 k ≤ Real.exp (((n+1 : ℕ) : ℝ)*(potential k+eps)))
    (j : ℕ) {b Z eps : ℝ} (hb : 0 < b) (hZ : 0 ≤ Z) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, |k| ≤ Z →
      physicalMean n (n+1+j) b k ≤ Real.exp
        ((n+1+j : ℕ)*(Real.log b/2+potential (k/Real.sqrt b)+eps)+
          (j : ℝ)*(1+|Real.log b|)/2) := by
  have hbound := hstd
    (S := Icc (-Z/Real.sqrt (b/(j+1 : ℝ))) (Z/Real.sqrt (b/(j+1 : ℝ))))
    isCompact_Icc heps
  filter_upwards [hbound] with n hn
  intro k hk
  let a := scaleFactor n (n+1+j) b
  have ha : 0 < a := scaleFactor_pos n (by omega) hb
  have hstandard := hn (k/a) (scaled_shift_mem n j hb hZ hk)
  rw [physicalMean_scale n (by omega) hb]
  have H := mul_le_mul_of_nonneg_left hstandard (pow_pos ha (n+1)).le
  have hex : a^(n+1) = Real.exp ((n+1 : ℝ)*Real.log a) := by
    rw [← show ((n+1 : ℕ) : ℝ) = (n+1 : ℝ) by simp,Real.exp_nat_mul,Real.exp_log ha]
  change a^(n+1)*physicalMean n (n+1) 1 (k/a) ≤ _
  apply H.trans
  rw [hex,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hrate := scaled_rate_le n j hb k
  have hm : (n+1 : ℝ) ≤ (n+1+j : ℕ) := by norm_cast; omega
  have he := mul_le_mul_of_nonneg_right hm heps.le
  dsimp only [a]
  simp only [Nat.cast_add,Nat.cast_one] at hrate he ⊢
  nlinarith

end
end TensorPCA.RetainedCountProofs.GOEPhysicalFirstMeanUpperProofs
