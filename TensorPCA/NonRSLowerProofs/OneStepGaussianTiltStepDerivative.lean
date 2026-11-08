-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- Adapted dominated-differentiation argument from
-- pmaronow/arbitrary-rsb-palomar@5162e2d15b440ce46fd322f20eb429468d601948,
-- vendor/spin-glass-foundations/Targets/CascadeDerivPi.lean (Apache-2.0).
-- The measure is Mathlib stdGaussian on Model.Vector N; growth uses its norm.
module
public import TensorPCA.GaussianMomentProofs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Differentiation through a literal finite Gaussian expectation and a
positive or negative nonzero-mass log-Laplace step. Parameter-dependent
fields, including separately quenched and annealed blocks, stay inside A.
The local growth assumptions are analytic inputs to this integration lemma,
not additional hypotheses of a physical principal theorem. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltStepDerivative
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

private theorem integrable_exp_mul_norm (N : ℕ) (c : ℝ) :
    Integrable (fun y : Model.Vector N => Real.exp (c*‖y‖))
      (stdGaussian (Model.Vector N)) := by
  have H := SYK.integrable_exp_mul_norm (ι := Fin N) c
  simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using H

theorem integrable_of_linear_growth {N : ℕ} {A : Model.Vector N → ℝ} {C D : ℝ}
    (hA : Measurable A) (hb : ∀ y, |A y| ≤ C+D*‖y‖) :
    Integrable A (stdGaussian (Model.Vector N)) := by
  have hi := (integrable_const C).add
    ((IsGaussian.integrable_id (μ := stdGaussian (Model.Vector N))).norm.const_mul D)
  apply hi.mono' hA.aestronglyMeasurable
  filter_upwards [] with y
  change ‖A y‖ ≤ C+D*‖y‖
  simpa only [Real.norm_eq_abs] using hb y

theorem integrable_exp_of_linear_growth {N : ℕ} {A : Model.Vector N → ℝ} {C D : ℝ}
    (hA : Measurable A) (hb : ∀ y, |A y| ≤ C+D*‖y‖) (mass : ℝ) :
    Integrable (fun y => Real.exp (mass*A y)) (stdGaussian (Model.Vector N)) := by
  have hi := (integrable_exp_mul_norm N (|mass| * D)).const_mul (Real.exp (|mass| * C))
  apply hi.mono' (hA.const_mul mass).exp.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  change Real.exp (mass*A y) ≤ Real.exp (|mass| * C)*Real.exp (|mass| * D*‖y‖)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : mass*A y ≤ |mass| * |A y| := by rw [← abs_mul]; exact le_abs_self _
  have h2 := mul_le_mul_of_nonneg_left (hb y) (abs_nonneg mass)
  nlinarith

private theorem integrable_poly_mul_exp_norm {N : ℕ} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun y : Model.Vector N => (a+b*‖y‖)*Real.exp (c*‖y‖))
      (stdGaussian (Model.Vector N)) := by
  have hi := (integrable_exp_mul_norm N (c+1)).const_mul (a+b)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hExp : Real.exp (c*‖y‖) ≤ Real.exp ((c+1)*‖y‖) :=
    Real.exp_le_exp.mpr (by nlinarith [norm_nonneg y])
  have hNorm : ‖y‖ ≤ Real.exp ‖y‖ := by have H := Real.add_one_le_exp ‖y‖; linarith
  have hProd : ‖y‖*Real.exp (c*‖y‖) ≤ Real.exp ((c+1)*‖y‖) := by
    calc
      _ ≤ Real.exp ‖y‖*Real.exp (c*‖y‖) := mul_le_mul_of_nonneg_right hNorm (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hA := mul_le_mul_of_nonneg_left hExp ha
  have hB := mul_le_mul_of_nonneg_left hProd hb
  nlinarith

theorem hasDerivAt_gaussian_integral {N : ℕ} {A A' : ℝ → Model.Vector N → ℝ}
    {t0 C D C' D' : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t0)
    (hderiv : ∀ t ∈ s, ∀ y, HasDerivAt (fun t' => A t' y) (A' t y) t)
    (hmeas : ∀ t ∈ s, Measurable (A t)) (hmeas' : ∀ t ∈ s, Measurable (A' t))
    (hb : ∀ t ∈ s, ∀ y, |A t y| ≤ C+D*‖y‖)
    (hb' : ∀ t ∈ s, ∀ y, |A' t y| ≤ C'+D'*‖y‖) :
    HasDerivAt (fun t => ∫ y, A t y ∂stdGaussian (Model.Vector N))
      (∫ y, A' t0 y ∂stdGaussian (Model.Vector N)) t0 := by
  have ht0 : t0 ∈ s := mem_of_mem_nhds hs
  have hBound := (integrable_const C').add
    ((IsGaussian.integrable_id (μ := stdGaussian (Model.Vector N))).norm.const_mul D')
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := A') (bound := fun y => C'+D'*‖y‖) hs ?_
    (integrable_of_linear_growth (hmeas t0 ht0) (hb t0 ht0)) ?_ ?_ hBound ?_).2
  · filter_upwards [hs] with t ht
    exact (hmeas t ht).aestronglyMeasurable
  · exact (hmeas' t0 ht0).aestronglyMeasurable
  · filter_upwards [] with y t ht
    simpa only [Real.norm_eq_abs] using hb' t ht y
  · filter_upwards [] with y t ht
    exact hderiv t ht y

theorem hasDerivAt_gaussian_exp_integral {N : ℕ} {A A' : ℝ → Model.Vector N → ℝ}
    {t0 mass C D C' D' : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t0)
    (hD' : 0 ≤ D')
    (hderiv : ∀ t ∈ s, ∀ y, HasDerivAt (fun t' => A t' y) (A' t y) t)
    (hmeas : ∀ t ∈ s, Measurable (A t)) (hmeas' : ∀ t ∈ s, Measurable (A' t))
    (hb : ∀ t ∈ s, ∀ y, |A t y| ≤ C+D*‖y‖)
    (hb' : ∀ t ∈ s, ∀ y, |A' t y| ≤ C'+D'*‖y‖) :
    HasDerivAt (fun t => ∫ y, Real.exp (mass*A t y) ∂stdGaussian (Model.Vector N))
      (∫ y, mass*(A' t0 y*Real.exp (mass*A t0 y)) ∂stdGaussian (Model.Vector N)) t0 := by
  have ht0 : t0 ∈ s := mem_of_mem_nhds hs
  have hC' : 0 ≤ C' := by
    have H := hb' t0 ht0 0
    simp only [norm_zero,mul_zero,add_zero] at H
    exact (abs_nonneg _).trans H
  let K := Real.exp (|mass| * C)
  let a := |mass| * C'*K
  let b := |mass| * D'*K
  let c := |mass| * D
  have ha : 0 ≤ a := by dsimp [a,K]; positivity
  have hb0 : 0 ≤ b := by dsimp [b,K]; positivity
  have hBound : Integrable (fun y : Model.Vector N => (a+b*‖y‖)*Real.exp (c*‖y‖))
      (stdGaussian (Model.Vector N)) := integrable_poly_mul_exp_norm ha hb0
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => Real.exp (mass*A t y))
    (F' := fun t y => mass*(A' t y*Real.exp (mass*A t y)))
    (bound := fun y => (a+b*‖y‖)*Real.exp (c*‖y‖)) hs ?_
    (integrable_exp_of_linear_growth (hmeas t0 ht0) (hb t0 ht0) mass) ?_ ?_ hBound ?_).2
  · filter_upwards [hs] with t ht
    exact ((hmeas t ht).const_mul mass).exp.aestronglyMeasurable
  · exact (((hmeas' t0 ht0).mul ((hmeas t0 ht0).const_mul mass).exp).const_mul mass).aestronglyMeasurable
  · filter_upwards [] with y t ht
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hExp : Real.exp (mass*A t y) ≤ K*Real.exp (c*‖y‖) := by
      dsimp only [K,c]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have H1 : mass*A t y ≤ |mass| * |A t y| := by rw [← abs_mul]; exact le_abs_self _
      have H2 := mul_le_mul_of_nonneg_left (hb t ht y) (abs_nonneg mass)
      nlinarith
    have hA' : 0 ≤ C'+D'*‖y‖ := (abs_nonneg _).trans (hb' t ht y)
    calc
      _ ≤ |mass| * ((C'+D'*‖y‖)*(K*Real.exp (c*‖y‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hb' t ht y) hExp (Real.exp_pos _).le hA')
          (abs_nonneg mass)
      _ = _ := by dsimp only [a,b]; ring
  · filter_upwards [] with y t ht
    exact (((hderiv t ht y).const_mul mass).exp).congr_deriv (by ring)

theorem hasDerivAt_gaussian_log_step {N : ℕ} {A A' : ℝ → Model.Vector N → ℝ}
    {t0 mass C D C' D' : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t0)
    (hmass : mass ≠ 0) (hD' : 0 ≤ D')
    (hderiv : ∀ t ∈ s, ∀ y, HasDerivAt (fun t' => A t' y) (A' t y) t)
    (hmeas : ∀ t ∈ s, Measurable (A t)) (hmeas' : ∀ t ∈ s, Measurable (A' t))
    (hb : ∀ t ∈ s, ∀ y, |A t y| ≤ C+D*‖y‖)
    (hb' : ∀ t ∈ s, ∀ y, |A' t y| ≤ C'+D'*‖y‖) :
    HasDerivAt (fun t => Real.log (∫ y, Real.exp (mass*A t y)
      ∂stdGaussian (Model.Vector N))/mass)
      ((∫ y, A' t0 y*Real.exp (mass*A t0 y) ∂stdGaussian (Model.Vector N))/
        (∫ y, Real.exp (mass*A t0 y) ∂stdGaussian (Model.Vector N))) t0 := by
  have ht0 : t0 ∈ s := mem_of_mem_nhds hs
  have hZ : 0 < ∫ y, Real.exp (mass*A t0 y) ∂stdGaussian (Model.Vector N) :=
    integral_exp_pos (integrable_exp_of_linear_growth (hmeas t0 ht0) (hb t0 ht0) mass)
  have H := hasDerivAt_gaussian_exp_integral (mass := mass) hs hD' hderiv hmeas hmeas' hb hb'
  convert (H.log hZ.ne').div_const mass using 1
  rw [integral_const_mul]
  field_simp [hmass,hZ.ne']

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltStepDerivative
