-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesCoefficients
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesOnBallIntegral
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedTransforms

/-! The Gaussian child-integral step of the depth induction. A child power-series
expansion yields the inner derivatives and positivity for the conditional Gaussian
mean.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedIntegralStep
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms
open FiniteNestedGaussianMarkedSeriesCoefficients FiniteNestedGaussianMarkedSeriesIntegral
open FiniteNestedGaussianMarkedSeriesOnBallIntegral
open scoped NNReal ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integral_child_series (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hchild : ∀z : E,HasFPowerSeriesOnBall (fun t => parentPower depth x p T Z t z)
      (powerSeries depth x p T Z z) 0 R) (S : E→L[ℝ]E) (z : E) :
    HasFPowerSeriesOnBall (fun t => ∫g : E,parentPower depth x p T Z t (z+S g) ∂stdGaussian E)
      (integralSeries (stdGaussian E) (fun n g => powerCoefficient depth n x p T Z (z+S g))) 0 R := by
  apply integral_series_on_ball (stdGaussian E)
    (fun n => (powerCoefficient_measurable depth n x p T hZ).comp
      (measurable_const.add S.continuous.measurable)) ha
    (fun n g => powerCoefficient_abs_le depth n x p hp hp1 hpx hxm hx1 T hZ ha hb (z+S g)) R hR hAR
  intro g
  simpa only [powerSeries,Function.comp_apply,Pi.add_apply] using hchild (z+S g)

theorem integral_child_jet (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hchild : ∀z : E,HasFPowerSeriesOnBall (fun t => parentPower depth x p T Z t z)
      (powerSeries depth x p T Z z) 0 R) (S : E→L[ℝ]E) (z : E) (n : ℕ) :
    iteratedDeriv n (fun t => ∫g : E,parentPower depth x p T Z t (z+S g) ∂stdGaussian E) 0=
      ((-1 : ℝ)^n*(descPochhammer ℝ n).eval p)*
        (∫g : E,weightedMoment depth n x p T Z (z+S g) ∂stdGaussian E) := by
  have HS := integral_child_series depth x p hp hp1 hpx hxm hx1 T hZ ha hb R hR hAR hchild S z
  dsimp only [integralSeries] at HS
  have HC := iteratedDeriv_div_factorial_eq HS n
  change iteratedDeriv n (fun t => ∫g : E,parentPower depth x p T Z t (z+S g) ∂stdGaussian E) 0/(n.factorial : ℝ)=
    ∫g : E,powerCoefficient depth n x p T Z (z+S g) ∂stdGaussian E at HC
  simp only [powerCoefficient,integral_const_mul] at HC
  have hFact : (n.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [div_eq_iff hFact] at HC
  rw [HC]
  field_simp

theorem integral_child_pos (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (hp : 0≤p) (hx : ∀j,0<x j) {t : ℝ} (ht : |t| *a<1)
    (S : E→L[ℝ]E) (z : E) :
    0<∫g : E,parentPower depth x p T Z t (z+S g) ∂stdGaussian E := by
  have hi := parentPower_integrable_shift depth x p T hZ ha hb hp hx ht S z
  have H := integral_mono (integrable_const ((1-|t| *a)^p)) hi
    (fun g => (parentPower_bounds depth x p T hZ ha hb hp hx ht (z+S g)).1)
  simp only [integral_const,probReal_univ,one_smul] at H
  exact (Real.rpow_pos_of_pos (sub_pos.mpr ht) p).trans_le H

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedIntegralStep
