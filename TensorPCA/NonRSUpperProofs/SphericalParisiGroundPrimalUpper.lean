-- SPDX-License-Identifier: Apache-2.0
/- Positive-degree specialization of the genuine mean-upper proof from
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalParisiGroundPrimalUpper.lean
The actual positive-degree dual endpoint is used directly; unrelated degree-zero
restriction and probability-tail consumers are omitted. The added structural
hypothesis 1 <= d i is discharged by the slice degrees p+1, never exported as a
new manuscript assumption. The analytic certificates and proof strategy are retained. -/
module
public import TensorPCA.NonRSUpperProofs.SphericalParisiSphereNetGround
public import TensorPCA.NonRSUpperProofs.SphericalParisiGlobalPrimalDual
public import TensorPCA.NonRSUpperProofs.SphericalParisiPositivePolynomialCalculus
@[expose] public section
open TensorPCA.RetainedCountProofs
namespace TensorPCA.NonRSUpperProofs.SphericalParisiGroundPrimalUpper
noncomputable section
open MeasureTheory Set Filter
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiGroundRSUpper
open SphericalParisiPositivePolynomialCalculus
open SphericalParisiSphereNet SphericalParisiGlobalPrimalDual LatitudeGroundTrial
open scoped Topology BigOperators
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ] in
theorem xi2_nonnegative (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ xi2 d c t := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (mul_nonneg (hc i) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (pow_nonneg ht _)

omit [DecidableEq σ] in
theorem literal_functional_nonnegative (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) {L α s : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) :
    0 ≤ functional (xi1 d c) (xi2 d c) L α s := by
  have hL : 0 < L := by linarith [mul_nonneg hα (sub_nonneg.mpr hs.2)]
  have hprofile : ∀ t ∈ Icc (0 : ℝ) 1,0 < profile L α s t :=
    fun t ht => hb.trans_le (profile_lower hα hs ht)
  have henergy : 0 ≤ ∫ t in (0 : ℝ)..1,xi2 d c t*profile L α s t :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => mul_nonneg (xi2_nonnegative d c hc ht.1) (hprofile t ht).le)
  have hinverse : 0 ≤ ∫ t in (0 : ℝ)..1,(profile L α s t)⁻¹ :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => inv_nonneg.mpr (hprofile t ht).le)
  unfold functional
  exact div_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (xi1_zero_nonnegative d c hc) hL.le) henergy) hinverse) (by norm_num)

omit [DecidableEq σ] in
theorem functional_zero_alpha_eq (d : σ → ℕ) (c : σ → ℝ) (L s : ℝ) :
    functional (xi1 d c) (xi2 d c) L 0 s=(L*xi1 d c 1+1/L)/2 := by
  have he := energy_integral (xi d c) (xi1 d c) (xi2 d c)
    (xi_hasDerivAt d c) (xi1_hasDerivAt d c) (xi2_continuous d c)
    (s := 0) (by constructor <;> norm_num) L 0
  simp only [profile,zero_mul,sub_zero,add_zero] at he
  unfold functional
  simp only [profile,zero_mul,sub_zero]
  rw [he]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  ring

/-- The Gaussian spherical maximum is asymptotically bounded
by every literal source one-step positive-profile trial. All positive covariance
degrees, including linear and odd degrees, are finite ordered-tensor blocks. No HS or pressure formula is assumed. -/
theorem eventual_actual_ground_functional_upper
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s ∈ Icc (0 : ℝ) 1)
    (hb : 0 < L-α*(1-s)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        functional (xi1 d c) (xi2 d c) L α s+ε := by
  by_cases hαpos : 0 < α
  · by_cases h1 : 0 < xi1 d c 1
    · obtain ⟨q,hq,κ,_hκ,hmargin,hBelow⟩ := exists_dual_below_all_primal d c hαpos
        (xi_hasDerivAt d c) (xi_monotoneOn_unitInterval d c hc) h1 (xi1_zero_nonnegative d c hc)
      have hF := functional_eq_primal (xi d c) (xi1 d c) (xi2 d c)
        (xi_hasDerivAt d c) (xi1_hasDerivAt d c) (xi2_continuous d c) hαpos hs hb
      have hBelowF := hBelow s hs L hb
      rw [← hF] at hBelowF
      exact (eventual_actual_ground_oneStepDual_upper d c hc hd hαpos hq.1 hq.2 hmargin hε).mono
        (fun _ hN => by linarith [hBelowF])
    · have hz : xi1 d c 1=0 := le_antisymm (not_lt.mp h1)
        (xi1_nonnegative d c hc (by norm_num))
      have hF := literal_functional_nonnegative d c hc hα hs hb
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      have HRS := actual_expected_maximum_le hN d c hc hd
      have hweighted : (∑ i,(d i : ℝ)*c i)=xi1 d c 1 := by
        simp only [xi1,one_pow,mul_one]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hweighted,hz,Real.sqrt_zero,mul_zero] at HRS
      exact (div_nonpos_of_nonpos_of_nonneg HRS hNr.le).trans (by linarith)
  · have hzα : α=0 := le_antisymm (not_lt.mp hαpos) hα
    subst α
    rw [functional_zero_alpha_eq]
    have hL : 0 < L := by simpa only [zero_mul,sub_zero] using hb
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have H := SphericalParisiGroundRSUpper.actual_constant_profile_ground_upper hN d c hc hd hL
    have hweighted : (∑ i,(d i : ℝ)*c i)=xi1 d c 1 := by
      simp only [xi1,one_pow,mul_one]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hweighted] at H
    have HD := div_le_div_of_nonneg_right H hNr.le
    have he : ((N : ℝ)*(L*xi1 d c 1+1/L)/2)/(N : ℝ)=(L*xi1 d c 1+1/L)/2 := by field_simp
    rw [he] at HD
    exact HD.trans (by linarith)


end
end TensorPCA.NonRSUpperProofs.SphericalParisiGroundPrimalUpper

