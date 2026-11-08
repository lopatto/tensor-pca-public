-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianScalarProofs
public import TensorPCA.ScalarBayesianProofs

/-!
# Exact Gaussian-prior replica-symmetric scalar normalization

The external product-prior theorem maximizes over every q>=0. The Gaussian scalar integral reduces to half the scalar potential phi; its values beyond
one cannot increase the supremum. This is a deterministic normalization result,
not a proof of the nonlinear free-energy limit.
-/
@[expose] public section

namespace TensorPCA.GaussianRSNormalizationProofs

open MeasureTheory ProbabilityTheory Set ScalarStationaryProofs ScalarPhiProofs
open scoped RealInnerProductSpace Topology

noncomputable def gaussianRSPotential (k : ℕ) (gamma q : ℝ) : ℝ :=
  (∫ z, GaussianScalarProofs.scalarLogPartition ((k : ℝ) * gamma * q ^ (k-1)) z
    ∂(stdGaussian ℝ).prod (stdGaussian ℝ)) - ((k : ℝ)-1) * gamma / 2 * q ^ k

theorem gaussianRSPotential_eq_phi (k : ℕ) {gamma q : ℝ} (hgamma : 0 ≤ gamma) (hq : 0 ≤ q) :
    gaussianRSPotential k gamma q = (1 / 2 : ℝ) * Scalar.phi k (Real.sqrt gamma) q := by
  have ha : 0 ≤ (k : ℝ) * gamma * q ^ (k-1) := by positivity
  rw [gaussianRSPotential, GaussianScalarProofs.integral_scalarLogPartition ha]
  unfold Scalar.phi
  rw [Real.sq_sqrt hgamma]
  ring

theorem phi_antitoneOn_above_one (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    AntitoneOn (Scalar.phi k lam) (Ici (1 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (1 : ℝ))
  · intro q hq
    have hq1 : 1 ≤ q := hq
    exact (hasDerivAt_phi k hk lam (by linarith : 0 ≤ q)).continuousAt.continuousWithinAt
  · intro q hq
    have hq1 : 1 ≤ q := interior_subset hq
    exact (hasDerivAt_phi k hk lam (by linarith : 0 ≤ q)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq1 : 1 ≤ q := interior_subset hq
    have hq0 : 0 ≤ q := by linarith
    have hk1 : 0 ≤ (k : ℝ)-1 := by
      have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [(hasDerivAt_phi k hk lam hq0).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · apply mul_nonpos_of_nonneg_of_nonpos hq0
      have hb : beta k q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq0 _) (sub_nonpos.mpr hq1)
      have hc := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg lam)) hb
      linarith

theorem phi_le_qStar_global (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam)
    {q : ℝ} (hq : 0 ≤ q) :
    Scalar.phi k lam q ≤ Scalar.phi k lam (Scalar.qStar k lam) := by
  rw [phi_qStar_eq_f k hk hlam]
  by_cases hq1 : q ≤ 1
  · exact phi_le_qStar_f k hk hlam ⟨hq, hq1⟩
  · have hq1' : 1 ≤ q := (lt_of_not_ge hq1).le
    exact ((phi_antitoneOn_above_one k hk lam) (by norm_num) hq1' hq1').trans
      (phi_le_qStar_f k hk hlam (q := 1) (by constructor <;> norm_num))

/-- The full nonnegative-domain source supremum equals the reviewed compact
Bayesian scalar value, with the exact factor one-half. -/
theorem sSup_gaussianRSPotential_eq_bayesianLimit (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    sSup (gaussianRSPotential k gamma '' Ici (0 : ℝ)) = Statistical.bayesianLimit k gamma := by
  have hlam := Real.sqrt_pos.mpr hgamma
  have hq := (qStar_isScalarMaximizer k hk hlam.le).1
  have hg : IsGreatest (gaussianRSPotential k gamma '' Ici (0 : ℝ))
      (gaussianRSPotential k gamma (Scalar.qStar k (Real.sqrt gamma))) := by
    refine ⟨⟨_, hq.1, rfl⟩, ?_⟩
    rintro y ⟨q, hq0, rfl⟩
    rw [gaussianRSPotential_eq_phi k hgamma.le hq0,
      gaussianRSPotential_eq_phi k hgamma.le hq.1]
    exact mul_le_mul_of_nonneg_left (phi_le_qStar_global k hk hlam hq0) (by norm_num)
  rw [hg.isLUB.csSup_eq ⟨_, hg.1⟩, gaussianRSPotential_eq_phi k hgamma.le hq.1,
    Statistical.bayesianLimit, ScalarBayesianProofs.sSup_phi_eq_f_qStar k hk hlam,
    phi_qStar_eq_f k hk hlam]


end TensorPCA.GaussianRSNormalizationProofs
