-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarPhiProofs
public import TensorPCA.ScalarBranchProofs
public import TensorPCA.Statistical
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Deterministic derivative of the reviewed Bayesian scalar variational limit. -/
@[expose] public section
namespace TensorPCA.ScalarBayesianProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs ScalarBranchProofs ScalarPhiProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def fBranch (k : ℕ) (lam : ℝ) : ℝ := Scalar.f k lam (Scalar.qS k lam)

theorem hasDerivAt_fBranch (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    HasDerivAt (fBranch k) (2*lam*(Scalar.qS k lam)^k) lam := by
  have hs := (qS_spec k hk hlam).1
  have hq := hasDerivAt_qS k hk hlam
  generalize hderiv : (2*Scalar.qS k lam*(1-Scalar.qS k lam) /
    (lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2)))) = d at hq
  have hp : (Scalar.qS k lam)^(k-1) = (Scalar.qS k lam)^(k-2)*Scalar.qS k lam := by
    rw [← pow_succ]
    congr 1
    omega
  have hcancel : lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1) -
      1/(1-Scalar.qS k lam)+1 = 0 := by
    field_simp [(sub_pos.mpr hs.1.2).ne']
    rw [hp]
    nlinarith [congrArg (fun x : ℝ => x*Scalar.qS k lam) hs.2]
  have hlog := ((hasDerivAt_const lam (1 : ℝ)).sub hq).log (sub_pos.mpr hs.1.2).ne'
  convert (((((hasDerivAt_id lam).pow 2).mul (hq.pow k)).add hlog).add hq) using 1
  · funext mu
    rfl
  · dsimp
    simp only [pow_one, mul_one, zero_sub]
    simp only [div_eq_mul_inv] at *
    nlinarith [congrArg (fun x : ℝ => x*d) hcancel]

theorem sSup_phi_eq_f_qStar (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam) :
    sSup (Scalar.phi k lam '' Icc (0 : ℝ) 1) = Scalar.f k lam (Scalar.qStar k lam) := by
  have hs := qStar_isScalarMaximizer k hk hlam.le
  have hg : IsGreatest (Scalar.f k lam '' Ico (0 : ℝ) 1)
      (Scalar.f k lam (Scalar.qStar k lam)) := by
    refine ⟨⟨_, hs.1, rfl⟩, ?_⟩
    rintro y ⟨q, hq, rfl⟩
    exact hs.2 q hq
  rw [← common_maximum_values k hk hlam]
  exact hg.isLUB.csSup_eq ⟨_, hg.1⟩

/-- The limiting scalar free energy vanishes on the complete subcritical range. -/
theorem bayesianLimit_eq_zero (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : Real.sqrt gamma < Scalar.lambdaC k) : Statistical.bayesianLimit k gamma = 0 := by
  unfold Statistical.bayesianLimit
  by_cases hz : Real.sqrt gamma = 0
  · have hphi : Scalar.phi k (Real.sqrt gamma) '' Icc (0 : ℝ) 1 = {0} := by
      rw [hz]
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        simp [Scalar.phi]
      · intro hy
        have heq : y = 0 := mem_singleton_iff.mp hy
        refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
        simp [Scalar.phi, heq]
    rw [hphi]
    simp
  · have hpos : 0 < Real.sqrt gamma := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    rw [sSup_phi_eq_f_qStar k hk hpos]
    simp [Scalar.qStar, hgamma.le, Scalar.f, show k ≠ 0 by omega]

theorem bayesianLimit_eq_fBranch (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : Scalar.lambdaC k < Real.sqrt gamma) : Statistical.bayesianLimit k gamma =
      (1/2 : ℝ)*fBranch k (Real.sqrt gamma) := by
  unfold Statistical.bayesianLimit
  rw [sSup_phi_eq_f_qStar k hk ((lambdaC_pos k hk).trans hgamma), qStar_eq_qS k hk hgamma]
  rfl

/-- Scalar derivative at squared signal strength. No asymptotic
free-energy or MMSE assertion is assumed in this deterministic calculation. -/
theorem hasDerivAt_bayesianLimit (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ Scalar.lambdaC k) :
    HasDerivAt (Statistical.bayesianLimit k) ((1/2 : ℝ)*(Scalar.qStar k lam)^k) (lam^2) := by
  have hsqrt : Real.sqrt (lam^2) = lam := Real.sqrt_sq hlam.le
  by_cases hle : lam ≤ Scalar.lambdaC k
  · have hlt : lam < Scalar.lambdaC k := lt_of_le_of_ne hle hne
    have hq : Scalar.qStar k lam = 0 := by simp [Scalar.qStar, hle]
    rw [hq, zero_pow (by omega : k ≠ 0), mul_zero]
    apply (hasDerivAt_const (lam^2) (0 : ℝ)).congr_of_eventuallyEq
    have hevent : ∀ᶠ gamma in 𝓝 (lam^2), Real.sqrt gamma < Scalar.lambdaC k :=
      Real.continuous_sqrt.continuousAt.eventually (Iio_mem_nhds (by simpa only [hsqrt] using hlt))
    filter_upwards [hevent] with gamma hgamma
    exact bayesianLimit_eq_zero k hk hgamma
  · have hgt := lt_of_not_ge hle
    rw [qStar_eq_qS k hk hgt]
    have hf := hasDerivAt_fBranch k hk ((lambdaS_lt_lambdaC k hk).trans hgt)
    have hroot := Real.hasDerivAt_sqrt (sq_pos_of_pos hlam).ne'
    have hf' : HasDerivAt (fBranch k) (2*lam*(Scalar.qS k lam)^k) (Real.sqrt (lam^2)) := by
      rw [hsqrt]
      exact hf
    have hcomp := (hf'.comp (lam^2) hroot).const_mul (1/2 : ℝ)
    have hd : HasDerivAt (fun gamma : ℝ => (1/2 : ℝ)*fBranch k (Real.sqrt gamma))
        ((1/2 : ℝ)*(Scalar.qS k lam)^k) (lam^2) := by
      convert hcomp using 1
      · funext gamma
        rfl
      · rw [hsqrt]
        field_simp [hlam.ne']
    apply hd.congr_of_eventuallyEq
    have hevent : ∀ᶠ gamma in 𝓝 (lam^2), Scalar.lambdaC k < Real.sqrt gamma :=
      Real.continuous_sqrt.continuousAt.eventually (Ioi_mem_nhds (by simpa only [hsqrt] using hgt))
    filter_upwards [hevent] with gamma hgamma
    exact bayesianLimit_eq_fBranch k hk hgamma

end
end TensorPCA.ScalarBayesianProofs
