-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedMarkedMomentMeasurability
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMomentConsumer

/-! Hierarchy heights may vary with the amplitude/prior section. The common Gaussian
field is averaged outside the root logarithm. Measurability follows from the
convergent moment series, and averaging retains the varying height family.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedVariableHeights
open MeasureTheory ProbabilityTheory Filter
open FiniteNestedMarkedMomentMeasurability FiniteNestedGaussianMarkedMoments
open FiniteNestedGaussianMarkedTransforms FiniteNestedGaussianMarkedValues BoundedMarkedLogSeries
open scoped BigOperators Topology
noncomputable section
variable {E S V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [MeasurableSpace V]

theorem rootLog_params_measurable (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a) :
    Measurable (fun p : S×E => rootLog depth (x p.1) T Z 1 p.2) := by
  have hW (n : ℕ) := weightedMoment_params_joint_measurable (depth+1) n T hZ
    x (fun _ : S => (0 : ℝ)) hxs measurable_const
  have hP (n : ℕ) : Measurable (fun p : S×E =>
      -(∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2)) :=
    (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hW (j+1)))).neg
  apply measurable_of_tendsto_metrizable hP
  apply tendsto_pi_nhds.mpr
  intro p
  have H := (root_moment_hasSum depth (x p.1) (hx p.1) (hxm p.1) (hx1 p.1) T hZ ha ha1 hb p.2).tendsto_sum_nat.neg
  simpa only [neg_neg] using H

theorem rootLog_params_integrable (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (eta : Measure (S×E)) [IsProbabilityMeasure eta] :
    Integrable (fun p : S×E => rootLog depth (x p.1) T Z 1 p.2) eta := by
  apply Integrable.of_bound (rootLog_params_measurable depth x hxs hx hxm hx1 T hZ ha ha1 hb).aestronglyMeasurable (a/(1-a))
  exact ae_of_all _ (fun p => by
    have H := root_polynomial_error_le depth (x p.1) (hx p.1) (hxm p.1) (hx1 p.1) T hZ ha ha1 hb p.2 0
    simpa only [Finset.sum_range_zero,zero_sub,abs_neg,neg_neg,Nat.zero_add,pow_one,Real.norm_eq_abs] using H)

theorem averaged_root_polynomial_error_le (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (eta : Measure (S×E)) [IsProbabilityMeasure eta] (n : ℕ) :
    |(∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*(∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2 ∂eta))+
      (∫p,rootLog depth (x p.1) T Z 1 p.2 ∂eta)|≤a^(n+1)/(1-a) := by
  have hi (j : ℕ) := (weightedMoment_params_integrable (depth+1) (j+1) T hZ ha hb
    x (fun _ : S => (0 : ℝ)) hxs measurable_const (fun _ => le_rfl) hx hxm hx1 eta).const_mul (1/((j+1 : ℕ) : ℝ))
  have hp : Integrable (fun p : S×E => ∑j∈Finset.range n,
      (1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2) eta :=
    integrable_finset_sum _ (fun j _ => hi j)
  have hl := rootLog_params_integrable depth x hxs hx hxm hx1 T hZ ha ha1 hb eta
  have he : Integrable (fun p : S×E => (∑j∈Finset.range n,
      (1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2)+rootLog depth (x p.1) T Z 1 p.2) eta := hp.add hl
  have H := integral_mono_ae he.abs (integrable_const (a^(n+1)/(1-a))) (ae_of_all _ (fun p => by
    simpa only [sub_neg_eq_add] using
      root_polynomial_error_le depth (x p.1) (hx p.1) (hxm p.1) (hx1 p.1) T hZ ha ha1 hb p.2 n))
  have HI := norm_integral_le_integral_norm
    (f := fun p : S×E => (∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2)+
      rootLog depth (x p.1) T Z 1 p.2) (μ := eta)
  simp only [Real.norm_eq_abs] at HI
  have HA := HI.trans (by simpa only [integral_const,probReal_univ,one_smul] using H)
  rw [integral_add hp hl,integral_finset_sum _ (fun j _ => hi j)] at HA
  simpa only [integral_const_mul] using HA

theorem expected_log_close_of_nested_moments (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (eta : Measure (S×E)) [IsProbabilityMeasure eta] (mu : Measure V) [IsProbabilityMeasure mu]
    {A : V→ℝ} (hA : Measurable A) (hbA : ∀ᵐv∂mu,0≤A v ∧ A v≤a) (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(A v)^(j+1) ∂mu)-
      (∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2 ∂eta)|≤delta) :
    |(∫v,Real.log (1-A v) ∂mu)-(∫p,rootLog depth (x p.1) T Z 1 p.2 ∂eta)|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  let P := ∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*(∫v,(A v)^(j+1) ∂mu)
  let Q := ∑j∈Finset.range n,(1/((j+1 : ℕ) : ℝ))*(∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2 ∂eta)
  have HP := expected_log_polynomial_error_le mu hA ha ha1 hbA n
  have HP' : |P+(∫v,Real.log (1-A v) ∂mu)|≤a^(n+1)/(1-a) := by
    simpa only [P,div_eq_mul_inv,one_div,mul_comm,mul_one] using HP
  have HQ := averaged_root_polynomial_error_le depth x hxs hx hxm hx1 T hZ ha ha1 hb eta n
  change |Q+(∫p,rootLog depth (x p.1) T Z 1 p.2 ∂eta)|≤a^(n+1)/(1-a) at HQ
  have HD : |P-Q|≤(n : ℝ)*delta := by
    dsimp only [P,Q]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑j∈Finset.range n,|(1/((j+1 : ℕ) : ℝ))*(∫v,(A v)^(j+1) ∂mu)-
          (1/((j+1 : ℕ) : ℝ))*(∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2 ∂eta)| := Finset.abs_sum_le_sum_abs _ _
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
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedVariableHeights
