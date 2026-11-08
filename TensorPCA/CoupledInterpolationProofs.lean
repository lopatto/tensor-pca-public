-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairRegularityProofs
public import TensorPCA.GaussianDensityProofs

/-! Finite two-replica auxiliary fields for the one-step interpolation.
The fresh independent weight-one level is annealed exactly. -/
@[expose] public section
namespace TensorPCA.CoupledInterpolationProofs
open Set MeasureTheory ProbabilityTheory PairRegularityProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two genuinely independent fresh vectors, one for each physical replica. -/
def freshAuxiliary {N : ℕ} (delta : ℝ) (xy gh : Model.Vector N × Model.Vector N) : ℝ :=
  Real.sqrt ((N : ℝ)*delta)*(inner ℝ xy.1 gh.1+inner ℝ xy.2 gh.2)

theorem freshAuxiliary_exp_integrable {N : ℕ} (delta : ℝ)
    (xy : Model.Vector N × Model.Vector N) :
    Integrable (fun gh ↦ Real.exp (freshAuxiliary delta xy gh))
      ((stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector N))) := by
  let s := Real.sqrt ((N : ℝ)*delta)
  have hi (x : Model.Vector N) : Integrable (fun g ↦ Real.exp (s*inner ℝ x g))
      (stdGaussian (Model.Vector N)) := by
    have H := GaussianDensityProofs.densityLaw_exp_integrable (s • x)
    rw [GaussianDensityProofs.densityLaw_eq_stdGaussian] at H
    simpa only [real_inner_smul_left] using H
  convert (hi xy.1).mul_prod (hi xy.2) using 1
  funext gh
  simp only [freshAuxiliary, s, mul_add, Real.exp_add]

theorem freshAuxiliary_exp_integral {N : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1) :
    (∫ gh, Real.exp (freshAuxiliary delta xy gh)
      ∂(stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector N))) =
        Real.exp ((N : ℝ)*delta) := by
  simp only [freshAuxiliary, mul_add, Real.exp_add]
  rw [integral_prod_mul (fun g : Model.Vector N ↦ Real.exp
      (Real.sqrt ((N : ℝ)*delta)*inner ℝ xy.1 g))
    (fun h : Model.Vector N ↦ Real.exp (Real.sqrt ((N : ℝ)*delta)*inner ℝ xy.2 h)),
    GaussianDensityProofs.integral_exp_inner_stdGaussian,
    GaussianDensityProofs.integral_exp_inner_stdGaussian, hx, hy, one_pow, mul_one,
    ← Real.exp_add]
  congr 1
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hdelta)]
  ring

theorem trial_auxiliary_variances (k : ℕ) (lam u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ Coupled.xiPrime k lam u ∧ Coupled.xiPrime k lam u ≤ Coupled.xiPrime k lam 1 := by
  have hp : u^(k-1) ≤ 1 := pow_le_one₀ hu.1 hu.2
  constructor
  · unfold Coupled.xiPrime
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg lam)) (pow_nonneg hu.1 _)
  · simpa only [Coupled.xiPrime, one_pow, mul_one] using
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg lam))

theorem anneal_trial_fresh_level {N : ℕ} (k : ℕ) (lam u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1) :
    (∫ gh, Real.exp (freshAuxiliary (Coupled.xiPrime k lam 1-Coupled.xiPrime k lam u) xy gh)
      ∂(stdGaussian (Model.Vector N)).prod (stdGaussian (Model.Vector N))) =
        Real.exp ((N : ℝ)*(Coupled.xiPrime k lam 1-Coupled.xiPrime k lam u)) :=
  freshAuxiliary_exp_integral _ (sub_nonneg.mpr (trial_auxiliary_variances k lam u hu).2) xy hx hy

end
end TensorPCA.CoupledInterpolationProofs
