-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedValues
public import TensorPCA.NonRSLowerProofs.BoundedMarkedLogSeries

/-! Finite unconditional marked moments determine the averaged Gaussian root value up to
uniform tails. Moment errors are measured before child conditioning or division by
rare-event probabilities.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMomentConsumer
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms FiniteNestedGaussianMarkedValues
open BoundedMarkedLogSeries
open scoped BigOperators
noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V]

theorem weightedMoment_integrable (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (eta : Measure E) [IsProbabilityMeasure eta] :
    Integrable (fun z : E => weightedMoment depth n x p T Z z) eta := by
  apply Integrable.of_bound (weightedMoment_measurable depth n x p T hZ).aestronglyMeasurable (a^n)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_of_nonneg (weightedMoment_mem depth n x p hp hpx hxm hx1 T hZ ha hb z).1]
    exact (weightedMoment_mem depth n x p hp hpx hxm hx1 T hZ ha hb z).2)

theorem averaged_root_polynomial_error_le (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (eta : Measure E) [IsProbabilityMeasure eta] (n : ℕ) :
    |(∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*(∫z,weightedMoment (depth+1) (j+1) x 0 T Z z ∂eta))+
      (∫z,rootLog depth x T Z 1 z ∂eta)|≤a^(n+1)/(1-a) := by
  have hi (j : ℕ) := (weightedMoment_integrable (depth+1) (j+1) x 0 le_rfl hx hxm hx1 T hZ ha hb eta).const_mul
    (1/((j+1 : ℕ) : ℝ))
  have hp : Integrable (fun z : E => ∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) x 0 T Z z) eta :=
    integrable_finset_sum _ (fun j _ => hi j)
  have hl := rootLog_integrable depth x hx hxm hx1 T hZ ha ha1 hb eta
  have he : Integrable (fun z : E => (∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) x 0 T Z z)+
      rootLog depth x T Z 1 z) eta := hp.add hl
  have H := integral_mono_ae he.abs (integrable_const (a^(n+1)/(1-a))) (ae_of_all _ (fun z => by
    simpa only [sub_neg_eq_add] using root_polynomial_error_le depth x hx hxm hx1 T hZ ha ha1 hb z n))
  have HI := norm_integral_le_integral_norm
    (f := fun z : E => (∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) x 0 T Z z)+rootLog depth x T Z 1 z) (μ := eta)
  simp only [Real.norm_eq_abs] at HI
  have HA := HI.trans (by simpa only [integral_const,probReal_univ,one_smul] using H)
  rw [integral_add hp hl,integral_finset_sum _ (fun j _ => hi j)] at HA
  simpa only [integral_const_mul] using HA

theorem expected_log_close_of_nested_moments (depth : ℕ) (x : Fin (depth+1)→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (eta : Measure E) [IsProbabilityMeasure eta] (mu : Measure V) [IsProbabilityMeasure mu]
    {S : V→ℝ} (hS : Measurable S) (hbS : ∀ᵐv∂mu,0≤S v ∧ S v≤a) (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(S v)^(j+1) ∂mu)-
      (∫z,weightedMoment (depth+1) (j+1) x 0 T Z z ∂eta)|≤delta) :
    |(∫v,Real.log (1-S v) ∂mu)-(∫z,rootLog depth x T Z 1 z ∂eta)|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  let P := ∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*(∫v,(S v)^(j+1) ∂mu)
  let Q := ∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*(∫z,weightedMoment (depth+1) (j+1) x 0 T Z z ∂eta)
  have HP := expected_log_polynomial_error_le mu hS ha ha1 hbS n
  have HP' : |P+(∫v,Real.log (1-S v) ∂mu)|≤a^(n+1)/(1-a) := by
    simpa only [P,div_eq_mul_inv,one_div,mul_comm,mul_one] using HP
  have HQ := averaged_root_polynomial_error_le depth x hx hxm hx1 T hZ ha ha1 hb eta n
  change |Q+(∫z,rootLog depth x T Z 1 z ∂eta)|≤a^(n+1)/(1-a) at HQ
  have HD : |P-Q|≤(n : ℝ)*delta := by
    dsimp only [P,Q]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑j∈Finset.range n,|(1/((j+1 : ℕ) : ℝ))*(∫v,(S v)^(j+1) ∂mu)-
          (1/((j+1 : ℕ) : ℝ))*(∫z,weightedMoment (depth+1) (j+1) x 0 T Z z ∂eta)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_j∈Finset.range n,delta := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← mul_sub,abs_mul]
        have HC : |1/((j+1 : ℕ) : ℝ)|≤1 := by
          rw [abs_of_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))]
          exact div_le_self zero_le_one (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
        exact (mul_le_mul HC (hmoment j (Finset.mem_range.mp hj)) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp
  have hP := abs_le.mp HP'
  have hQ := abs_le.mp HQ
  have hD := abs_le.mp HD
  exact abs_le.mpr ⟨by linarith only [hP.1,hQ.2,hD.2],by linarith only [hP.2,hQ.1,hD.1]⟩

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMomentConsumer
