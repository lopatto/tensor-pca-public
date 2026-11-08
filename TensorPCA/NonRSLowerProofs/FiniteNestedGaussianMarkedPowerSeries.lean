-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedParentStep

/-! Finite-depth reconstruction of the nested Gaussian parent power. The base case is
the binomial integral at a Dirac mark; the analytic induction step supplies the
child expansions.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedPowerSeries
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms
open FiniteNestedGaussianMarkedSeriesCoefficients FiniteNestedGaussianMarkedParentStep
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw
open BoundedMarkedPowerTransform BoundedMarkedIntegralAnalytic
open scoped NNReal ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem weightedMoment_depth_zero (n : ℕ) (x : Fin 0→ℝ) (p : ℝ)
    (T : Fin 0→E→L[ℝ]E) (Z : E→ℝ) (z : E) : weightedMoment 0 n x p T Z z=(Z z)^n := by
  simp [weightedMoment,NestedPartition,mass,treeMoment]

theorem parent_series (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (z : E) : HasFPowerSeriesOnBall (fun t => parentPower depth x p T Z t z)
      (powerSeries depth x p T Z z) 0 R := by
  induction depth generalizing p z with
  | zero =>
    have H := markTransform_hasFPowerSeriesOnBall (Measure.dirac z) hZ ha hp hp1
      (ae_of_all _ hb) R hR hAR
    have HE : markIntegralSeries (Measure.dirac z) Z p=powerSeries 0 x p T Z z := by
      unfold markIntegralSeries powerSeries
      congr 1
      funext n
      simp only [powerCoefficient,weightedMoment_depth_zero,integral_dirac]
    rw [HE] at H
    have HF : markTransform (Measure.dirac z) Z p=(fun t => (1-t*Z z)^p) := by
      funext t
      unfold markTransform
      rw [integral_dirac]
    rw [HF] at H
    exact H
  | succ depth ih =>
    have hA : 0<x 0 := hp.trans_lt (hpx 0)
    have hTail : ∀j : Fin depth,x 0<x j.succ := fun j => hxm (by change (0 : ℕ)<(j : ℕ)+1; omega)
    have hTailMono : StrictMono (fun j : Fin depth => x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)
    apply parent_series_step depth x p hp hpx hxm hx1 T hZ ha hb R hR hAR _ z
    intro y
    exact ih (fun j => x j.succ) (x 0) hA.le (hx1 0) hTail hTailMono
      (fun j => hx1 j.succ) (fun j => T j.succ) y

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedPowerSeries
