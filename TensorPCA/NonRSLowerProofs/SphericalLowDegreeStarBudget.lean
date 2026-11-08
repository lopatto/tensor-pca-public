-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetLowDegreeBudget

/-! Star-test GG errors are bounded by the same deviation budgets, uniformly as the
total perturbation cutoff increases.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalLowDegreeStarBudget
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianGGEnsemble
open NonRSUpperProofs.GaussianPerturbationDeviation
open SphericalPolynomialFirstJetBudget SphericalFirstJetCubeBudget SphericalFirstJetLowDegreeBudget
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cubeMeanPowerDefect_le_boundedError_mean {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (p : Fin K) (eps : ℝ) (m : ℕ) :
    cubeMeanPowerDefect (K := K) nu v eps m (p.val+1)≤
      ∫ x, boundedDegreeError nu v x m p ∂positiveCubeLaw K := by
  apply integral_mono_ae (cubePowerDefect_integrable nu hv.le eps m (p.val+1))
    (boundedDegreeError_integrable nu hv.le m p)
  filter_upwards [positiveCubeLaw_support K,positiveCubeLaw_abs_le_two K] with x hx hx2
  have hxp : 0<x p := by linarith [(hx p).1]
  have H := cubePowerDefect_coordinate_le nu hv x hx2 p (x p) hxp eps m
  rw [Function.update_eq_self] at H
  have hraw : cubePowerDefect nu v eps m (p.val+1) x≤degreeError nu v x m p := H
  exact (le_min (cubePowerDefect_le_two nu hv.le eps m (p.val+1) x) hraw).trans (le_max_right _ _)

theorem exists_uniform_lowDegree_star_threshold (Q : ℕ) {delta : ℝ} (hdelta : 0<delta) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N K : ℕ}
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ), V≤v →
      ∀ (p : Fin K), p.val+1≤Q → ∀ (eps : ℝ) (m : ℕ),
        cubeMeanPowerDefect (K := K) nu v eps m (p.val+1)≤delta := by
  obtain ⟨V,hV1,hV⟩ := exists_uniform_lowDegreeError_threshold Q hdelta
  refine ⟨V,hV1,?_⟩
  intro N K nu _ v hvV p hp eps m
  have hv : 0<v := lt_of_lt_of_le zero_lt_one (hV1.trans hvV)
  exact (cubeMeanPowerDefect_le_boundedError_mean nu hv p eps m).trans (hV nu v hvV p hp m)

theorem cubeMeanPowerDefect_zero_degree {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (eps : ℝ) (m : ℕ) :
    cubeMeanPowerDefect (K := K) nu v eps m 0=0 := by
  letI := ambientParameterizedGibbsKernel_markov (K := K) nu hv
  unfold cubeMeanPowerDefect cubePowerDefect
  simp only [NonRSUpperProofs.GaussianGGEnsemble.powerDefect_zero,integral_zero]

end
end TensorPCA.NonRSLowerProofs.SphericalLowDegreeStarBudget
