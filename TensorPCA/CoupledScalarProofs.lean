-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.Coupled
public import TensorPCA.ScalarPhiProofs

/-! Exact scalar trial calculus used by the coupled free-energy trial bounds. -/
@[expose] public section
namespace TensorPCA.CoupledScalarProofs
open Set Filter ScalarStaticRatioProofs ScalarPhiProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem trial_zeroLambda (k : ℕ) (lam m u : ℝ) :
    Coupled.trial k lam m 0 u = lam^2+(1-m)*Coupled.theta k lam u+
      (1/m)*Real.log ((1+Coupled.xiPrime k lam u)/(1+(1-m)*Coupled.xiPrime k lam u))-
        Real.log (1+Coupled.xiPrime k lam u) := by
  unfold Coupled.trial
  simp only [zero_mul, sub_zero, add_zero]
  ring

theorem trial_one_zeroLambda (k : ℕ) (lam u : ℝ) : Coupled.trial k lam 1 0 u = lam^2 := by
  rw [trial_zeroLambda]
  simp

/-- Exact m derivative driving the positive-strength improving trial. -/
theorem hasDerivAt_trial_m (k : ℕ) (lam u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (fun m : ℝ => Coupled.trial k lam m 0 u) (Scalar.phi k lam u) 1 := by
  let a := Coupled.xiPrime k lam u
  let theta := Coupled.theta k lam u
  have ha : 0 ≤ a := by unfold a Coupled.xiPrime; positivity
  have ha1 : 1+a ≠ 0 := ne_of_gt (by linarith)
  have hD := (hasDerivAt_const (1 : ℝ) (1 : ℝ)).add
    (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 1)).mul_const a)
  have hratio := (hasDerivAt_const (1 : ℝ) (1+a)).div hD (by norm_num)
  have hlog := hratio.log (by simpa using ha1)
  have hinv := (hasDerivAt_id (1 : ℝ)).inv (by norm_num)
  have htheta := ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 1)).mul_const theta
  convert (((hasDerivAt_const (1 : ℝ) (lam^2)).add htheta).add (hinv.mul hlog)).sub_const
    (Real.log (1+a)) using 1
  · funext m
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, id_eq]
    simpa only [a, theta, one_div] using trial_zeroLambda k lam m u
  · dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, id_eq]
    simp only [sub_self, zero_mul, add_zero, one_mul, mul_one, zero_add,
      inv_one, zero_sub, div_one, neg_mul, one_pow]
    have hphi : Scalar.phi k lam u = -theta+a-Real.log (1+a) := by
      unfold Scalar.phi a theta Coupled.xiPrime Coupled.theta
      rw [mul_comm (k : ℝ) (lam^2)]
      ring
    rw [hphi]
    field_simp [ha1]
    ring

/-- The zero-strength improving direction is Lambda rather than m. -/
theorem hasDerivAt_trial_zero_strength_Lambda (k : ℕ) (u : ℝ) :
    HasDerivAt (fun L : ℝ => Coupled.trial k 0 1 L u) (-u) 0 := by
  have hminus := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)
  have hplus := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id 0)
  have hratio := hminus.div hminus (by norm_num)
  have hlog := hratio.log (by norm_num)
  have hlogs := (hplus.log (by norm_num)).add (hminus.log (by norm_num))
  convert (((hasDerivAt_id (0 : ℝ)).mul_const (-u)).add hlog).sub
    (hlogs.const_mul (1/2 : ℝ)) using 1
  · funext L
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, id_eq]
    simp only [Coupled.trial, Coupled.xiPrime, Coupled.theta, zero_pow two_ne_zero,
      mul_zero, zero_mul, add_zero, sub_self, one_div, inv_one, one_mul]
    ring
  · norm_num

theorem exists_right_step_decrease {f : ℝ → ℝ} {x d eta : ℝ}
    (hf : HasDerivAt f d x) (hd : d < 0) (heta : 0 < eta) :
    ∃ h ∈ Ioo (0 : ℝ) eta, f (x+h) < f x := by
  have hs : ∀ᶠ h in 𝓝[>] (0 : ℝ), h⁻¹*(f (x+h)-f x) < 0 := by
    simpa only [smul_eq_mul] using hf.tendsto_slope_zero_right.eventually (Iio_mem_nhds hd)
  have hp : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have he' : ∀ᶠ h in 𝓝 (0 : ℝ), h < eta := Iio_mem_nhds heta
  have he : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < eta := he'.filter_mono nhdsWithin_le_nhds
  obtain ⟨h, hhpos, hhsmall, hhneg⟩ := (hp.and (he.and hs)).exists
  refine ⟨h, ⟨hhpos, hhsmall⟩, ?_⟩
  apply sub_neg.mp
  by_contra hn
  have hh := mul_nonneg (inv_nonneg.mpr hhpos.le) (le_of_not_gt hn)
  exact not_lt_of_ge hh hhneg

/-- Every subcritical macroscopic overlap has a genuinely improving admissible
trial. Strength zero uses the Lambda direction; positive strength uses m. -/
theorem exists_improving_trial (k : ℕ) (hk : 3 ≤ k) {lam u : ℝ}
    (hlam : 0 ≤ lam) (hsub : lam < Scalar.lambdaC k) (hu : u ∈ Ioc (0 : ℝ) 1) :
    ∃ m L : ℝ, m ∈ Icc (1 : ℝ) 2 ∧ L ∈ Icc (0 : ℝ) 1 ∧
      0 < 1+(1-m)*Coupled.xiPrime k lam u-L ∧ Coupled.trial k lam m L u < lam^2 := by
  by_cases hzero : lam = 0
  · subst lam
    obtain ⟨L, hL, hgap⟩ := exists_right_step_decrease
      (hasDerivAt_trial_zero_strength_Lambda k u) (by linarith [hu.1] : -u < 0) zero_lt_one
    refine ⟨1, L, ⟨le_rfl, by norm_num⟩, ⟨hL.1.le, hL.2.le⟩, ?_, ?_⟩
    · simp only [sub_self, zero_mul, add_zero]
      linarith [hL.2]
    · have hz : Coupled.trial k 0 1 0 u = 0 := by rw [trial_one_zeroLambda]; norm_num
      simpa only [zero_add, hz, zero_pow two_ne_zero] using hgap
  · have hlampos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hzero)
    let a := Coupled.xiPrime k lam u
    have ha : 0 ≤ a := by unfold a Coupled.xiPrime; have := hu.1.le; positivity
    have heta : 0 < min (1 : ℝ) (1/(1+a)) := lt_min zero_lt_one (one_div_pos.mpr (by linarith))
    obtain ⟨h, hh, hgap⟩ := exists_right_step_decrease (hasDerivAt_trial_m k lam u hu.1.le)
      (phi_neg_of_subcritical k hk hlampos hsub hu) heta
    have hh1 : h < 1 := hh.2.trans_le (min_le_left _ _)
    have hhA : h < 1/(1+a) := hh.2.trans_le (min_le_right _ _)
    have hprod := (lt_div_iff₀ (by linarith : 0 < 1+a)).mp hhA
    refine ⟨1+h, 0, ⟨by linarith [hh.1], by linarith⟩, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · change 0 < 1+(1-(1+h))*a-0
      nlinarith [hh.1]
    · rwa [trial_one_zeroLambda] at hgap

end
end TensorPCA.CoupledScalarProofs
