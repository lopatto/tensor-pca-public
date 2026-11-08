-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.RetainedCountProofs.GOEClippedMeanProofs
public import TensorPCA.RetainedCountProofs.SemicircleClipping
public import TensorPCA.RetainedCountProofs.UniformLipschitzConvergence
/-! First-mean upper bounds reduced to expected spectral-test
convergence. The reduction's convergence parameter is not an unconditional
random-matrix theorem. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEFirstMeanUpperProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEClippedDeterminants GOEClippedMeanProofs SpectralTraceLipschitz
open GOEAsymptotics OAI.CriticalSK SemicirclePotential SemicircleClipping
open scoped Topology BigOperators NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalized expectation under the literal standard GOE matrix law. -/
def normalizedExpectedClippedTrace (n : ℕ) (k rho : ℝ) : ℝ :=
  (∫ W, matrixClippedTrace (n+1) k rho W
    ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)/((n+1 : ℕ) : ℝ)

lemma matrixClippedTrace_shift_dist (m : ℕ) {rho : ℝ} (hrho : 0 < rho) (k l : ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    |matrixClippedTrace m k rho W-matrixClippedTrace m l rho W| ≤
      (m : ℝ)*(1/rho)*|k-l| := by
  unfold matrixClippedTrace
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin m, (1/rho)*|k-l| := by
      apply Finset.sum_le_sum
      intro i _
      let a := matrixOrderedEigenvalues (matrixToGaussian W) i
      have h := (clippedLog_lipschitz a hrho).dist_le_mul k l
      change |clippedLog a rho k-clippedLog a rho l| ≤ (1/rho)*|k-l| at h
      simpa only [clippedLog, abs_sub_comm a k, abs_sub_comm a l] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma normalizedExpectedClippedTrace_lipschitz (n : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith ⟨1/rho, by positivity⟩ (fun k => normalizedExpectedClippedTrace n k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro k l
  change |normalizedExpectedClippedTrace n k rho-normalizedExpectedClippedTrace n l rho| ≤
    (1/rho)*|k-l|
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  unfold normalizedExpectedClippedTrace
  rw [← sub_div, abs_div, abs_of_pos hN,
    ← integral_sub (matrixClippedTrace_integrable n k hrho) (matrixClippedTrace_integrable n l hrho)]
  apply (div_le_iff₀ hN).mpr
  have h := norm_integral_le_of_norm_le_const
    (μ := SphericalGaussianJet.goeLaw (n+1) (n+1) 1)
    (f := fun W => matrixClippedTrace (n+1) k rho W-matrixClippedTrace (n+1) l rho W)
    (C := ((n+1 : ℕ) : ℝ)*(1/rho)*|k-l|) (ae_of_all _ fun W => by
      simpa only [Real.norm_eq_abs] using matrixClippedTrace_shift_dist (n+1) hrho k l W)
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at h
  convert h using 1; ring

lemma normalizedExpectedClippedTrace_uniform {rho : ℝ} (hrho : 0 < rho)
    (hlim : ∀ k : ℝ, Tendsto (fun n => normalizedExpectedClippedTrace n k rho) atTop
      (𝓝 (clippedPotential k rho))) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n k => normalizedExpectedClippedTrace n k rho)
      (fun k => clippedPotential k rho) atTop S := by
  apply UniformLipschitzConvergence.uniform_on_compact
    (L := ⟨1/rho, by positivity⟩) _ (fun n => normalizedExpectedClippedTrace_lipschitz n hrho)
    (clippedPotential_lipschitz hrho) hlim hS
  change (0 : ℝ) < 1/rho
  positivity

/-- Checked reduction to a genuine intermediate spectral-statistic limit.
No determinant-mean estimate or physical ground-state conclusion is a premise. -/
theorem standard_mean_upper_uniform_of_clippedTrace_tendsto
    (hlim : ∀ (k rho : ℝ), 0 < rho →
      Tendsto (fun n => normalizedExpectedClippedTrace n k rho) atTop (𝓝 (clippedPotential k rho)))
    {S : Set ℝ} (hS : IsCompact S) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ S,
      GOEPhysicalPotential.physicalMean n (n+1) 1 k ≤
        Real.exp (((n+1 : ℕ) : ℝ)*(potential k+eps)) := by
  have hclip := (clippedPotential_uniform_on_compact hS) _
    (show {(x,y) : ℝ×ℝ | dist x y < eps/3} ∈ uniformity ℝ from
      Metric.dist_mem_uniformity (by positivity))
  obtain ⟨j, hj⟩ := hclip.exists
  let rho := clippingRadius j
  have hrho : 0 < rho := clippingRadius_pos j
  have hmean := (normalizedExpectedClippedTrace_uniform hrho (fun k => hlim k rho hrho) hS) _
    (show {(x,y) : ℝ×ℝ | dist x y < eps/3} ∈ uniformity ℝ from
      Metric.dist_mem_uniformity (by positivity))
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hsmall := ((hn.atTop_mul_const (sq_pos_of_pos hrho)).const_div_atTop 1).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < eps/3))
  filter_upwards [hmean, hsmall] with n hmean hsmall
  intro k hk
  have h1 := hj k hk
  have h2 := hmean k hk
  change dist (potential k) (clippedPotential k rho) < eps/3 at h1
  change dist (clippedPotential k rho) (normalizedExpectedClippedTrace n k rho) < eps/3 at h2
  simp only [Real.dist_eq] at h1 h2
  have hs : 1/(rho^2*((n+1 : ℕ) : ℝ)) < eps/3 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm (rho^2)] using hsmall
  have hc : clippedPotential k rho < potential k+eps/3 := by
    linarith [(abs_lt.mp h1).1, (abs_lt.mp h1).2]
  have hm : normalizedExpectedClippedTrace n k rho < clippedPotential k rho+eps/3 := by
    linarith [(abs_lt.mp h2).1, (abs_lt.mp h2).2]
  apply (standard_mean_le_exp_clipped_mean n k hrho).trans
  apply Real.exp_le_exp.mpr
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have he : (∫ W, matrixClippedTrace (n+1) k rho W
      ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)+1/rho^2 =
      ((n+1 : ℕ) : ℝ)*(normalizedExpectedClippedTrace n k rho+1/(rho^2*((n+1 : ℕ) : ℝ))) := by
    unfold normalizedExpectedClippedTrace
    field_simp [hN.ne', hrho.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hN.le
  linarith

end
end TensorPCA.RetainedCountProofs.GOEFirstMeanUpperProofs
