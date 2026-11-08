-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMoments
public import TensorPCA.NonRSLowerProofs.BoundedMarkedTaylorContinuation
public import TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialCoefficients

/-! Finite-PMF bounds for coefficients in the nested transform induction, and derivative
extraction from the convergent scalar series.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesCoefficients
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedMoments BoundedMarkedBinomialCoefficients
open scoped ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def powerCoefficient (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) : ℝ :=
  (((-1 : ℝ)^n*(descPochhammer ℝ n).eval p)/(n.factorial : ℝ))*weightedMoment depth n x p T Z z

def powerSeries (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => powerCoefficient depth n x p T Z z)

theorem powerCoefficient_measurable (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) :
    Measurable (fun z : E => powerCoefficient depth n x p T Z z) :=
  (weightedMoment_measurable depth n x p T hZ).const_mul _

theorem powerCoefficient_abs_le (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    |powerCoefficient depth n x p T Z z|≤a^n := by
  have HM := weightedMoment_mem depth n x p hp hpx hxm hx1 T hZ ha hb z
  rw [powerCoefficient,abs_mul,abs_of_nonneg HM.1]
  exact (mul_le_mul (signed_falling_coefficient_abs_le_one hp hp1 n) HM.2 HM.1 zero_le_one).trans_eq (one_mul _)

theorem powerCoefficient_succ_abs_le (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    |powerCoefficient depth (n+1) x p T Z z|≤(p/((n+1 : ℕ) : ℝ))*a^(n+1) := by
  have HM := weightedMoment_mem depth (n+1) x p hp hpx hxm hx1 T hZ ha hb z
  rw [powerCoefficient,abs_mul,abs_of_nonneg HM.1]
  exact mul_le_mul (signed_falling_coefficient_abs_le hp hp1 n) HM.2 HM.1
    (div_nonneg hp (Nat.cast_nonneg _))

theorem powerCoefficient_zero (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) : powerCoefficient depth 0 x p T Z z=1 := by
  rw [powerCoefficient,weightedMoment_zero depth x p hp hpx hxm hx1 T Z z]
  simp

theorem iteratedDeriv_div_factorial_eq {f : ℝ→ℝ} {c : ℕ→ℝ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℝ c) 0 R) (n : ℕ) :
    iteratedDeriv n f 0/(n.factorial : ℝ)=c n := by
  have H := hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hf.analyticAt.hasFPowerSeriesAt
  have HE := congrArg (fun P : FormalMultilinearSeries ℝ ℝ ℝ => P n (fun _ => 1)) H
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,one_pow,mul_one] using HE.symm

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesCoefficients
