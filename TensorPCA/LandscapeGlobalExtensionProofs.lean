-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.EnergyBranchProofs

/-! Analytic extension of the critical low-overlap variational certificate.
The only open input in the final assembly is the explicit trial-profile bound;
the strength, sign and RS-region steps are proved here. -/
@[expose] public section
namespace TensorPCA.LandscapeGlobalExtensionProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs
  ScalarSelectionProofs ScalarBranchProofs ScalarValueProofs EnergyBranchProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem energy_mono_strength (k : ℕ) {lam mu m : ℝ}
    (hm : 0 ≤ m) (hle : lam ≤ mu) : Scalar.energy k lam m ≤ Scalar.energy k mu m := by
  unfold Scalar.energy
  exact add_le_add (mul_le_mul_of_nonneg_right hle (pow_nonneg hm _)) le_rfl

theorem energy_le_abs (k : ℕ) {lam m : ℝ} (hlam : 0 ≤ lam) :
    Scalar.energy k lam m ≤ Scalar.energy k lam |m| := by
  have hcov : Scalar.xiSlice k |m| = Scalar.xiSlice k m := by
    funext t
    simp only [Scalar.xiSlice, pow_mul, sq_abs]
  unfold Scalar.energy
  rw [hcov]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (by simpa only [abs_pow] using le_abs_self (m ^ k)) hlam) le_rfl

theorem sqrt_criticalOverlap_mem_rsDomain (k : ℕ) (hk : 3 ≤ k) :
    Real.sqrt (criticalOverlap k) ∈ Ioo (rsBoundary k) 1 := by
  simpa only [qS_at_critical k hk] using
    sqrt_qS_mem_rsDomain k hk (lambdaS_lt_lambdaC k hk)

theorem energy_eq_rsEnergy_closed (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {m : ℝ}
    (hm : m ∈ Icc (Real.sqrt (criticalOverlap k)) 1) :
    Scalar.energy k lam m = Scalar.rsEnergy k lam m := by
  have hm0 : 0 ≤ m := (Real.sqrt_nonneg _).trans hm.1
  have hb := (sqrt_criticalOverlap_mem_rsDomain k hk).1.le.trans hm.1
  have hrs := GroundState.rsSlice_of_general RSVariationalProof.generalRSVariationalLaw
    VariationalProofs.slicePolynomialFacts k hk m ⟨by linarith, hm.2⟩
      (by rw [← rsBoundary_eq k hk, abs_of_nonneg hm0]; exact hb)
  exact congrArg (fun v : ℝ => lam * m ^ k + v) hrs

theorem mleValue_ge_critical_tangent (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k ≤ lam) :
    Scalar.gs k + (lam - Scalar.lambdaC k) * (Real.sqrt (criticalOverlap k)) ^ k ≤
      Scalar.mleValue k lam := by
  by_cases heq : lam = Scalar.lambdaC k
  · subst lam
    simp [Scalar.mleValue]
  have hlt : Scalar.lambdaC k < lam := lt_of_le_of_ne hlam (Ne.symm heq)
  have hc : ContinuousOn (branchEnergy k) (Icc (Scalar.lambdaC k) lam) := by
    intro t ht
    exact (hasDerivAt_branchEnergy k hk
      ((lambdaS_lt_lambdaC k hk).trans_le ht.1)).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (branchEnergy k) (interior (Icc (Scalar.lambdaC k) lam)) := by
    intro t ht
    have ht' : Scalar.lambdaC k < t ∧ t < lam := by simpa only [interior_Icc, mem_Ioo] using ht
    exact (hasDerivAt_branchEnergy k hk
      ((lambdaS_lt_lambdaC k hk).trans ht'.1)).differentiableAt.differentiableWithinAt
  have hslope : ∀ t ∈ interior (Icc (Scalar.lambdaC k) lam),
      (Real.sqrt (criticalOverlap k)) ^ k ≤ deriv (branchEnergy k) t := by
    intro t ht
    have ht' : Scalar.lambdaC k < t ∧ t < lam := by simpa only [interior_Icc, mem_Ioo] using ht
    rw [(hasDerivAt_branchEnergy k hk ((lambdaS_lt_lambdaC k hk).trans ht'.1)).deriv]
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [← qS_at_critical k hk]
    exact (strictMonoOn_qS k hk).monotoneOn (lambdaS_lt_lambdaC k hk)
      ((lambdaS_lt_lambdaC k hk).trans ht'.1) ht'.1.le
  have h := (convex_Icc (Scalar.lambdaC k) lam).mul_sub_le_image_sub_of_le_deriv hc hd hslope
    (Scalar.lambdaC k) ⟨le_rfl, hlam⟩ lam ⟨hlam, le_rfl⟩ hlam
  rw [branchEnergy_critical k hk] at h
  rw [Scalar.mleValue, if_neg (not_le_of_gt hlt), supercriticalValue_eq_branchEnergy k hk hlt]
  nlinarith

theorem rsEnergy_deriv_sign (k : ℕ) (hk : 3 ≤ k) {lam m : ℝ}
    (hlam : 0 < lam) (hm : m ∈ Ioo (rsBoundary k) 1) :
    (1 < ((k : ℝ) * lam ^ 2) * beta k (m ^ 2) →
      0 < deriv (Scalar.rsEnergy k lam) m) ∧
    (((k : ℝ) * lam ^ 2) * beta k (m ^ 2) < 1 →
      deriv (Scalar.rsEnergy k lam) m < 0) := by
  have hderiv : deriv (Scalar.rsEnergy k lam) m = deriv (Scalar.energy k lam) m := by
    rw [(hasDerivAt_rsEnergy k hk lam hm).deriv, (hasDerivAt_energy k hk lam hm).deriv]
  rw [hderiv]
  exact energy_deriv_sign k hk hlam hm

theorem rsEnergy_monotone_left (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k ≤ lam) :
    MonotoneOn (Scalar.rsEnergy k lam)
      (Icc (Real.sqrt (criticalOverlap k)) (Real.sqrt (Scalar.qS k lam))) := by
  have hlamS := (lambdaS_lt_lambdaC k hk).trans_le hlam
  have hlam0 := (lambdaC_pos k hk).trans_le hlam
  have hroot := sqrt_qS_mem_rsDomain k hk hlamS
  have hcroot := sqrt_criticalOverlap_mem_rsDomain k hk
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans (qS_spec k hk hlamS).1.1.1
  have hqeq : ((k : ℝ) * lam ^ 2) * beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using (qS_spec k hk hlamS).1.2
  have hcoef : 0 < (k : ℝ) * lam ^ 2 := by positivity
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · unfold Scalar.rsEnergy
    fun_prop
  · intro x hx
    have hx' : Real.sqrt (criticalOverlap k) < x ∧ x < Real.sqrt (Scalar.qS k lam) := by
      simpa only [interior_Icc, mem_Ioo] using hx
    exact (hasDerivAt_rsEnergy k hk lam
      ⟨hcroot.1.trans hx'.1, hx'.2.trans hroot.2⟩).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : Real.sqrt (criticalOverlap k) < x ∧ x < Real.sqrt (Scalar.qS k lam) := by
      simpa only [interior_Icc, mem_Ioo] using hx
    have hdomain : x ∈ Ioo (rsBoundary k) 1 :=
      ⟨hcroot.1.trans hx'.1, hx'.2.trans hroot.2⟩
    have hx0 : 0 < x := (Real.sqrt_nonneg _).trans_lt hx'.1
    have hbx : turningPoint k < x ^ 2 := by
      have hbc := criticalOverlap_gt_turningPoint k hk
      nlinarith [Real.sq_sqrt (criticalOverlap_mem_Ioo k hk).1.le,
        Real.sqrt_nonneg (criticalOverlap k)]
    have hxq : x ^ 2 < Scalar.qS k lam := by
      nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg (Scalar.qS k lam)]
    have hb := (strictAntiOn_beta_right k hk)
      ⟨hbx.le, (hxq.trans (qS_spec k hk hlamS).1.1.2).le⟩
      ⟨(qS_spec k hk hlamS).1.1.1.le, (qS_spec k hk hlamS).1.1.2.le⟩ hxq
    apply ((rsEnergy_deriv_sign k hk hlam0 hdomain).1 ?_).le
    have h := mul_lt_mul_of_pos_left hb hcoef
    simpa only [hqeq] using h

theorem rsEnergy_antitone_right (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlamS : Scalar.lambdaS k < lam) :
    AntitoneOn (Scalar.rsEnergy k lam) (Icc (Real.sqrt (Scalar.qS k lam)) 1) := by
  have hlam0 := (lambdaS_pos k hk).trans hlamS
  have hroot := sqrt_qS_mem_rsDomain k hk hlamS
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans (qS_spec k hk hlamS).1.1.1
  have hqeq : ((k : ℝ) * lam ^ 2) * beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using (qS_spec k hk hlamS).1.2
  have hcoef : 0 < (k : ℝ) * lam ^ 2 := by positivity
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · unfold Scalar.rsEnergy
    fun_prop
  · intro x hx
    have hx' : Real.sqrt (Scalar.qS k lam) < x ∧ x < 1 := by
      simpa only [interior_Icc, mem_Ioo] using hx
    exact (hasDerivAt_rsEnergy k hk lam
      ⟨hroot.1.trans hx'.1, hx'.2⟩).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : Real.sqrt (Scalar.qS k lam) < x ∧ x < 1 := by
      simpa only [interior_Icc, mem_Ioo] using hx
    have hdomain : x ∈ Ioo (rsBoundary k) 1 := ⟨hroot.1.trans hx'.1, hx'.2⟩
    have hx0 : 0 < x := (Real.sqrt_nonneg _).trans_lt hx'.1
    have hqx : Scalar.qS k lam < x ^ 2 := by
      nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg (Scalar.qS k lam)]
    have hx1 : x ^ 2 < 1 := by nlinarith
    have hb := (strictAntiOn_beta_right k hk)
      ⟨(qS_spec k hk hlamS).1.1.1.le, (qS_spec k hk hlamS).1.1.2.le⟩
      ⟨((qS_spec k hk hlamS).1.1.1.trans hqx).le, hx1.le⟩ hqx
    apply ((rsEnergy_deriv_sign k hk hlam0 hdomain).2 ?_).le
    have h := mul_lt_mul_of_pos_left hb hcoef
    simpa only [hqeq] using h

theorem critical_energy_le_gs_above (k : ℕ) (hk : 3 ≤ k) {m : ℝ}
    (hm : m ∈ Icc (Real.sqrt (criticalOverlap k)) 1) :
    Scalar.energy k (Scalar.lambdaC k) m ≤ Scalar.gs k := by
  have hanti := rsEnergy_antitone_right k hk (lambdaS_lt_lambdaC k hk)
  rw [qS_at_critical k hk] at hanti
  have hC := sqrt_criticalOverlap_mem_rsDomain k hk
  have h := hanti ⟨le_rfl, hC.2.le⟩ hm hm.1
  rw [← energy_eq_rsEnergy_closed k hk _ hm] at h
  rw [← energy_eq_rsEnergy_closed k hk _ ⟨le_rfl, hC.2.le⟩] at h
  have heq := secondaryEnergy_critical k hk
  rw [qS_at_critical k hk] at heq
  exact h.trans_eq heq

theorem energy_le_mleValue_above (k : ℕ) (hk : 3 ≤ k) {lam m : ℝ}
    (hm : m ∈ Icc (Real.sqrt (criticalOverlap k)) 1) :
    Scalar.energy k lam m ≤ Scalar.mleValue k lam := by
  have hm0 : 0 ≤ m := (Real.sqrt_nonneg _).trans hm.1
  by_cases hbelow : lam ≤ Scalar.lambdaC k
  · rw [Scalar.mleValue, if_pos hbelow]
    exact (energy_mono_strength k hm0 hbelow).trans (critical_energy_le_gs_above k hk hm)
  have habove : Scalar.lambdaC k < lam := lt_of_not_ge hbelow
  have hlamS := (lambdaS_lt_lambdaC k hk).trans habove
  have hroot := sqrt_qS_mem_rsDomain k hk hlamS
  have hcroot := sqrt_criticalOverlap_mem_rsDomain k hk
  have hCq : Real.sqrt (criticalOverlap k) ≤ Real.sqrt (Scalar.qS k lam) := by
    apply Real.sqrt_le_sqrt
    rw [← qS_at_critical k hk]
    exact (strictMonoOn_qS k hk).monotoneOn (lambdaS_lt_lambdaC k hk) hlamS habove.le
  have hmax : Scalar.rsEnergy k lam m ≤ Scalar.rsEnergy k lam (Real.sqrt (Scalar.qS k lam)) := by
    by_cases hleft : m ≤ Real.sqrt (Scalar.qS k lam)
    · exact rsEnergy_monotone_left k hk habove.le ⟨hm.1, hleft⟩ ⟨hCq, le_rfl⟩ hleft
    · exact rsEnergy_antitone_right k hk hlamS ⟨le_rfl, hroot.2.le⟩
        ⟨(lt_of_not_ge hleft).le, hm.2⟩ (lt_of_not_ge hleft).le
  rw [← energy_eq_rsEnergy_closed k hk _ hm,
    ← energy_eq_rsEnergy_closed k hk _ ⟨hCq, hroot.2.le⟩,
    ← secondaryBranch_matches_mleValue k hk hlamS habove.le] at hmax
  exact hmax

/-- A critical low-overlap trial certificate propagates to every nonnegative
strength and every physical overlap. The premise is a separate variational
trial bound, not a physical ground-state limit or the global conclusion. -/
theorem global_energy_upper_of_critical_low (k : ℕ) (hk : 3 ≤ k)
    (hcritical : ∀ m : ℝ, 0 ≤ m → m ≤ Real.sqrt (criticalOverlap k) →
      Scalar.energy k (Scalar.lambdaC k) m ≤ Scalar.gs k)
    (lam : ℝ) (hlam : 0 ≤ lam) (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) :
    Scalar.energy k lam m ≤ Scalar.mleValue k lam := by
  suffices hnonneg : ∀ x ∈ Icc (0 : ℝ) 1,
      Scalar.energy k lam x ≤ Scalar.mleValue k lam by
    exact (energy_le_abs k hlam).trans (hnonneg |m|
      ⟨abs_nonneg _, abs_le.mpr ⟨hm.1, hm.2⟩⟩)
  intro x hx
  by_cases hsmall : x ≤ Real.sqrt (criticalOverlap k)
  · have hcrit := hcritical x hx.1 hsmall
    by_cases hbelow : lam ≤ Scalar.lambdaC k
    · rw [Scalar.mleValue, if_pos hbelow]
      exact (energy_mono_strength k hx.1 hbelow).trans hcrit
    have habove : Scalar.lambdaC k ≤ lam := (lt_of_not_ge hbelow).le
    have hpower : x ^ k ≤ (Real.sqrt (criticalOverlap k)) ^ k :=
      pow_le_pow_left₀ hx.1 hsmall k
    have hsignal := mul_le_mul_of_nonneg_left hpower (sub_nonneg.mpr habove)
    have htangent := mleValue_ge_critical_tangent k hk habove
    unfold Scalar.energy at hcrit ⊢
    nlinarith
  · exact energy_le_mleValue_above k hk ⟨(lt_of_not_ge hsmall).le, hx.2⟩


end
end TensorPCA.LandscapeGlobalExtensionProofs
