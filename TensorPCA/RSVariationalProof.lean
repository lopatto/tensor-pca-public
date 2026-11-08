-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GroundState
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-! Direct analytic certificate for the variational replica-symmetric criterion.
This module proves a statement about the profile infimum; it does not
assume or establish a physical spin-glass ground-state limit. -/
@[expose] public section
namespace TensorPCA.RSVariationalProof
open MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

/-- Ordinary finite nonnegative covariance polynomial, with degree-one terms. -/
def covariance {P : ℕ} (c : Fin P → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * t ^ (i.val+1)

def covarianceD {P : ℕ} (c : Fin P → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * (i.val+1 : ℕ) * t ^ i.val

def covarianceDD {P : ℕ} (c : Fin P → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * (i.val+1 : ℕ) * (i.val : ℕ) * t ^ (i.val-1)

theorem covariance_hasDerivAt {P : ℕ} (c : Fin P → ℝ) (t : ℝ) :
    HasDerivAt (covariance c) (covarianceD c t) t := by
  unfold covariance covarianceD
  simpa only [Nat.add_sub_cancel, mul_assoc] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ (hasDerivAt_pow (i.val+1) t).const_mul (c i))

theorem covarianceD_hasDerivAt {P : ℕ} (c : Fin P → ℝ) (t : ℝ) :
    HasDerivAt (covarianceD c) (covarianceDD c t) t := by
  unfold covarianceD covarianceDD
  simpa only [mul_assoc] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ (hasDerivAt_pow i.val t).const_mul (c i * (i.val+1 : ℕ)))

theorem deriv_covariance {P : ℕ} (c : Fin P → ℝ) :
    deriv (covariance c) = covarianceD c :=
  funext (fun t ↦ (covariance_hasDerivAt c t).deriv)

theorem deriv_deriv_covariance {P : ℕ} (c : Fin P → ℝ) :
    deriv (deriv (covariance c)) = covarianceDD c := by
  rw [deriv_covariance]
  exact funext (fun t ↦ (covarianceD_hasDerivAt c t).deriv)

theorem covarianceD_nonnegative {P : ℕ} (c : Fin P → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ covarianceD c t := by
  unfold covarianceD
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg
    (mul_nonneg (hc i) (Nat.cast_nonneg _)) (pow_nonneg ht _))

theorem covarianceDD_nonnegative {P : ℕ} (c : Fin P → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ covarianceDD c t := by
  unfold covarianceDD
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg
    (mul_nonneg (mul_nonneg (hc i) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (pow_nonneg ht _))

theorem covarianceDD_le_at_one {P : ℕ} (c : Fin P → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : covarianceDD c t ≤ covarianceDD c 1 := by
  unfold covarianceDD
  apply Finset.sum_le_sum
  intro i _
  have hcoef : 0 ≤ c i * (i.val+1 : ℕ) * (i.val : ℕ) :=
    mul_nonneg (mul_nonneg (hc i) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  simpa only [one_pow, mul_one] using
    mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2 (n := i.val-1)) hcoef

theorem integral_covarianceDD {P : ℕ} (c : Fin P → ℝ) :
    (∫ t in (0 : ℝ)..1, covarianceDD c t) = covarianceD c 1 - covarianceD c 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ covarianceD_hasDerivAt c t)
  have hcont : Continuous (covarianceDD c) := by unfold covarianceDD; fun_prop
  exact hcont.intervalIntegrable _ _

/-- The support-line inequality for the reciprocal at the constant RS profile. -/
theorem reciprocal_support {A p : ℝ} (hA : 0 ≤ A) (hp : 0 < p) :
    2 * Real.sqrt A - A*p ≤ 1/p := by
  apply (le_div_iff₀ hp).mpr
  have hs : 0 ≤ A*p^2 - 2*Real.sqrt A*p + 1 := by
    calc
      0 ≤ (Real.sqrt A*p-1)^2 := sq_nonneg _
      _ = A*p^2 - 2*Real.sqrt A*p + 1 := by
        rw [sub_sq, mul_pow, Real.sq_sqrt hA]
        ring
  nlinarith

/-- The certificate only needs profile positivity/continuity/antitonicity;
its concavity is retained in the actual admissible profile class. -/
theorem profile_lower_bound {w : ℝ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hwle : ∀ t ∈ Icc (0 : ℝ) 1, w t ≤ A)
    (hmass : (∫ t in (0 : ℝ)..1, w t) = A-B)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    2 * Real.sqrt A ≤
      (∫ t in (0 : ℝ)..1, w t*p t + 1/p t) + B*p 0 := by
  rcases hp with ⟨hcont, hanti, _, hpos⟩
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      2*Real.sqrt A + (w t-A)*p 0 ≤ w t*p t + 1/p t := by
    intro t ht
    have hanti' := hanti (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ht ht.1
    have hmul := mul_le_mul_of_nonpos_left hanti' (sub_nonpos.mpr (hwle t ht))
    have hinv := reciprocal_support hA (hpos t ht)
    nlinarith
  have hleft : ContinuousOn (fun t ↦ 2*Real.sqrt A + (w t-A)*p 0)
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.add ((hw.sub continuousOn_const).mul continuousOn_const)
  have hinv : ContinuousOn (fun t ↦ 1/p t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hcont (fun t ht ↦ (hpos t ht).ne')
  have hright : ContinuousOn (fun t ↦ w t*p t + 1/p t) (Icc (0 : ℝ) 1) :=
    (hw.mul hcont).add hinv
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hleft.intervalIntegrable_of_Icc zero_le_one)
    (hright.intervalIntegrable_of_Icc zero_le_one) hpoint
  have hlin : (∫ t in (0 : ℝ)..1, 2*Real.sqrt A + (w t-A)*p 0) =
      2*Real.sqrt A - B*p 0 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ ↦ 2*Real.sqrt A)
      (g := fun t : ℝ ↦ (w t-A)*p 0) intervalIntegrable_const
      (((hw.sub continuousOn_const).mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one)]
    rw [intervalIntegral.integral_mul_const (p 0) (fun t ↦ w t-A)]
    rw [intervalIntegral.integral_sub (f := w) (g := fun _ ↦ A)
        (hw.intervalIntegrable_of_Icc zero_le_one) intervalIntegrable_const, hmass]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    ring
  rw [hlin] at h
  linarith

/-- Direct evaluation of every constant profile, including the linear boundary. -/
theorem functional_const {P : ℕ} (c : Fin P → ℝ) (h d : ℝ) :
    Scalar.parisiFunctional (covariance c) h (fun _ ↦ d) =
      (covarianceD c 1+h^2)*d + 1/d := by
  unfold Scalar.parisiFunctional
  rw [deriv_deriv_covariance, deriv_covariance]
  have hc : Continuous (covarianceDD c) := by unfold covarianceDD; fun_prop
  rw [intervalIntegral.integral_add
    (f := fun t ↦ covarianceDD c t*d) (g := fun _ ↦ 1/d)
    ((hc.mul continuous_const).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_mul_const d (covarianceDD c), integral_covarianceDD]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  ring

/-- The RS criterion gives a sharp lower certificate for every actual profile. -/
theorem functional_lower {P : ℕ} (c : Fin P → ℝ) (hc : ∀ i, 0 ≤ c i) (h : ℝ)
    (hRS : covarianceDD c 1 ≤ covarianceD c 1+h^2)
    {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    2*Real.sqrt (covarianceD c 1+h^2) ≤ Scalar.parisiFunctional (covariance c) h p := by
  have hA : 0 ≤ covarianceD c 1+h^2 :=
    add_nonneg (covarianceD_nonnegative c hc zero_le_one) (sq_nonneg h)
  have hw : ContinuousOn (covarianceDD c) (Icc (0 : ℝ) 1) := by
    have : Continuous (covarianceDD c) := by unfold covarianceDD; fun_prop
    exact this.continuousOn
  have hm : (∫ t in (0 : ℝ)..1, covarianceDD c t) =
      (covarianceD c 1+h^2)-(h^2+covarianceD c 0) := by
    rw [integral_covarianceDD]
    ring
  have H := profile_lower_bound hA hw
    (fun t ht ↦ (covarianceDD_le_at_one c hc ht).trans hRS) hm hp
  unfold Scalar.parisiFunctional
  rw [deriv_deriv_covariance, deriv_covariance]
  exact H

/-- The complete finite-polynomial variational RS identity. Its degenerate
zero-covariance/zero-field case uses an unattained infimum, not a minimizer. -/
theorem covariance_variationalValue {P : ℕ} (c : Fin P → ℝ)
    (hc : ∀ i, 0 ≤ c i) (h : ℝ)
    (hRS : covarianceDD c 1 ≤ covarianceD c 1+h^2) :
    Scalar.variationalValue (covariance c) h = Real.sqrt (covarianceD c 1+h^2) := by
  let A : ℝ := covarianceD c 1+h^2
  let S : Set ℝ := {v | ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧
    v = Scalar.parisiFunctional (covariance c) h p}
  have hA : 0 ≤ A :=
    add_nonneg (covarianceD_nonnegative c hc zero_le_one) (sq_nonneg h)
  have hlower : ∀ v ∈ S, 2*Real.sqrt A ≤ v := by
    rintro v ⟨p, hp, rfl⟩
    exact functional_lower c hc h hRS hp
  by_cases hzero : A = 0
  · have hSne : S.Nonempty := ⟨Scalar.parisiFunctional (covariance c) h (fun _ ↦ 1),
      fun _ ↦ 1, Scalar.admissibleProfile_const zero_lt_one, rfl⟩
    have hnonneg : ∀ v ∈ S, 0 ≤ v := by simpa only [hzero, Real.sqrt_zero, mul_zero] using hlower
    have hbb : BddBelow S := ⟨0, hnonneg⟩
    have hInfNonneg : 0 ≤ sInf S := le_csInf hSne hnonneg
    have hInfLe : sInf S ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro eps heps
      have hmem : Scalar.parisiFunctional (covariance c) h (fun _ ↦ 1/eps) ∈ S :=
        ⟨fun _ ↦ 1/eps, Scalar.admissibleProfile_const (one_div_pos.mpr heps), rfl⟩
      calc
        sInf S ≤ Scalar.parisiFunctional (covariance c) h (fun _ ↦ 1/eps) := csInf_le hbb hmem
        _ = 0+eps := by
          rw [functional_const]
          change A*(1/eps)+1/(1/eps) = 0+eps
          simp only [hzero, zero_mul, zero_add, one_div_one_div]
    have hInf : sInf S = 0 := le_antisymm hInfLe hInfNonneg
    change (1/2 : ℝ)*sInf S = Real.sqrt A
    rw [hInf, hzero, Real.sqrt_zero, mul_zero]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
    have hr : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
    have hvalue : Scalar.parisiFunctional (covariance c) h (fun _ ↦ 1/Real.sqrt A) =
        2*Real.sqrt A := by
      rw [functional_const]
      change A*(1/Real.sqrt A)+1/(1/Real.sqrt A) = 2*Real.sqrt A
      field_simp [hr.ne']
      nlinarith [Real.sq_sqrt hA]
    have hleast : IsLeast S (2*Real.sqrt A) :=
      ⟨⟨fun _ ↦ 1/Real.sqrt A, Scalar.admissibleProfile_const (one_div_pos.mpr hr),
        hvalue.symm⟩, hlower⟩
    change (1/2 : ℝ)*sInf S = Real.sqrt A
    rw [hleast.csInf_eq]
    ring

/-- Unconditional proof of the reviewed variational RS obligation. No physical
Parisi formula or ground-state limit is assumed. -/
theorem generalRSVariationalLaw : GroundState.GeneralRSVariationalLaw := by
  intro xi h hcov _ hRS
  obtain ⟨P, c, hc, hxi⟩ := hcov
  have heq : xi = covariance c := funext hxi
  subst xi
  rw [deriv_deriv_covariance, deriv_covariance] at hRS
  simpa only [deriv_covariance] using covariance_variationalValue c hc h hRS

end
end TensorPCA.RSVariationalProof
