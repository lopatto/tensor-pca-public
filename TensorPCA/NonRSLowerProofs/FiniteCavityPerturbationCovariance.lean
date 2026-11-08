-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.SphericalPositivePerturbation
public import TensorPCA.Model
public import Mathlib.Algebra.Order.Ring.Abs

/-! The same finite-cutoff perturbation kernel at two amplitudes and two
signed overlaps. The amplitude cube and cutoff are unchanged across N. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationCovariance
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def amplitudeKernel {K : ℕ} (x : Fin K→ℝ) (r : ℝ) : ℝ :=
  ∑p : Fin K,(coefficients 1 x p)^2*r^(p.val+1)

theorem amplitudeKernel_abs_le {K : ℕ} (x : Fin K→ℝ) (hx : ∀p,|x p|≤2)
    {r : ℝ} (hr : |r|≤1) : |amplitudeKernel x r|≤4 := by
  have hSum := coefficients_budget (1 : ℝ) x hx
  calc
    _ ≤ ∑p : Fin K,|(coefficients 1 x p)^2*r^(p.val+1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑p : Fin K,(coefficients 1 x p)^2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (abs_nonneg r) hr)
    _ ≤ 4 := by norm_num at hSum ⊢; exact hSum

private theorem signed_power_lipschitz (n : ℕ) {r s : ℝ} (hr : |r|≤1) (hs : |s|≤1) :
    |r^n-s^n|≤(n : ℝ)*|r-s| := by
  have hmax0 : 0≤max |r| |s| := (abs_nonneg r).trans (le_max_left _ _)
  have hmax1 : max |r| |s|≤1 := max_le hr hs
  have hp := pow_le_one₀ (n := n-1) hmax0 hmax1
  have H := (abs_pow_sub_pow_le r s n).trans
    (mul_le_of_le_one_right (mul_nonneg (abs_nonneg (r-s)) (Nat.cast_nonneg n)) hp)
  simpa only [mul_comm |r-s| (n : ℝ)] using H

theorem amplitudeKernel_lipschitz {K : ℕ} (x : Fin K→ℝ) (hx : ∀p,|x p|≤2)
    {r s : ℝ} (hr : |r|≤1) (hs : |s|≤1) :
    |amplitudeKernel x r-amplitudeKernel x s|≤4*(K : ℝ)*|r-s| := by
  have hSum := coefficients_budget (1 : ℝ) x hx
  have hterms (p : Fin K) :
      |(coefficients 1 x p)^2*(r^(p.val+1)-s^(p.val+1))|≤
        (coefficients 1 x p)^2*((K : ℝ)*|r-s|) := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (signed_power_lipschitz (p.val+1) hr hs).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show p.val+1≤K by omega)) (abs_nonneg _))
  have hid : amplitudeKernel x r-amplitudeKernel x s=
      ∑p : Fin K,(coefficients 1 x p)^2*(r^(p.val+1)-s^(p.val+1)) := by
    unfold amplitudeKernel
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hid]
  calc
    _ ≤ ∑p : Fin K,|(coefficients 1 x p)^2*(r^(p.val+1)-s^(p.val+1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑p : Fin K,(coefficients 1 x p)^2*((K : ℝ)*|r-s|) := Finset.sum_le_sum (fun p _ => hterms p)
    _ = (∑p : Fin K,(coefficients 1 x p)^2)*((K : ℝ)*|r-s|) := (Finset.sum_mul ..).symm
    _ ≤ 4*((K : ℝ)*|r-s|) :=
      mul_le_mul_of_nonneg_right (by norm_num at hSum ⊢; exact hSum) (by positivity)
    _ = _ := by ring

theorem feature_inner_eq_amplitudeKernel {N K : ℕ} (v : ℝ) (x : Fin K→ℝ)
    (z y : Model.Vector N) :
    inner ℝ (feature (coefficients v x) z) (feature (coefficients v x) y)=
      v^2*amplitudeKernel x (inner ℝ z y) := by
  rw [feature_inner,amplitudeKernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold coefficients
  ring

theorem amplitude_covariance_error {K : ℕ} (x : Fin K→ℝ) (hx : ∀p,|x p|≤2)
    (v w : ℝ) {r s : ℝ} (hr : |r|≤1) (hs : |s|≤1) :
    |v^2*amplitudeKernel x r-w^2*amplitudeKernel x s|≤
      4*|v^2-w^2|+4*(K : ℝ)*v^2*|r-s| := by
  have hid : v^2*amplitudeKernel x r-w^2*amplitudeKernel x s=
      v^2*(amplitudeKernel x r-amplitudeKernel x s)+(v^2-w^2)*amplitudeKernel x s := by ring
  rw [hid]
  calc
    _ ≤ |v^2*(amplitudeKernel x r-amplitudeKernel x s)|+|(v^2-w^2)*amplitudeKernel x s| := abs_add_le _ _
    _ = v^2*|amplitudeKernel x r-amplitudeKernel x s|+|v^2-w^2| *|amplitudeKernel x s| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg v)]
    _ ≤ v^2*(4*(K : ℝ)*|r-s|)+|v^2-w^2| *4 :=
      add_le_add (mul_le_mul_of_nonneg_left (amplitudeKernel_lipschitz x hx hr hs) (sq_nonneg v))
        (mul_le_mul_of_nonneg_left (amplitudeKernel_abs_le x hx hs) (abs_nonneg _))
    _ = _ := by ring

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationCovariance
