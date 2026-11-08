-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedAmplitudeIntegrability
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationPressureBudget

/-! Average the perturbation-compatible ASS inequality over one fixed amplitude cube at
every dimension. Its threshold precedes amplitude averaging; the amplitude choice is
uniform in dimension.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavitySameCubePressure
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCavityPerturbedAmplitudeIntegrability FiniteCavityPerturbedASSLower
open FiniteCavityPerturbationPressureBudget FiniteCavityASSLower FiniteCavityRetainedMass
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The raw perturbed pressure averaged over the same fixed positive amplitude cube. The
strength argument may later be N^gamma.
-/
def cubeAveragedPressure (N k K : ℕ) (mu beta v : ℝ) : ℝ :=
  ∫a,expectedLogPerturbedSlicePartition N k K mu beta v a∂positiveCubeLaw K

theorem perturbed_pressure_amplitude_measurable (N k K : ℕ) (mu beta v : ℝ) :
    Measurable (expectedLogPerturbedSlicePartition N k K mu beta v) :=
  slice_expected_logPartition_measurable N k K mu beta v

theorem perturbed_pressure_cube_integrable {N k K : ℕ} (hN : 0< N) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) :
    Integrable (expectedLogPerturbedSlicePartition N k K mu beta v) (positiveCubeLaw K) :=
  slice_expected_logPartition_cube_integrable hN hmu beta v

theorem perturbed_cavity_amplitude_measurable {N : ℕ} (hN : 0< N) (M k K : ℕ) (mu beta v : ℝ) :
    Measurable (perturbedCavityFunctional N M k K mu beta v) := by
  exact (numerator_population_amplitude_measurable hN M k K mu beta v).sub
    (theta_population_amplitude_measurable hN M k K mu beta v)

theorem perturbed_cavity_cube_integrable {N M k K : ℕ} (hN : 0< N) (hM : 0< M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) :
    Integrable (perturbedCavityFunctional N M k K mu beta v) (positiveCubeLaw K) := by
  exact (numerator_population_cube_integrable hN hM hmu beta v).sub
    (theta_population_cube_integrable hN mu beta v)

theorem cube_averaged_pressure_bounds {N k K : ℕ} (hN : 0< N) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) :
    0≤ cubeAveragedPressure N k K mu beta v-expectedLogSlicePartition N k mu beta ∧
      cubeAveragedPressure N k K mu beta v-expectedLogSlicePartition N k mu beta≤4*v^2 := by
  have hI := perturbed_pressure_cube_integrable (k := k) (K := K) hN hmu beta v
  have hD := hI.sub (integrable_const (expectedLogSlicePartition N k mu beta))
  have hEq : (∫a,(expectedLogPerturbedSlicePartition N k K mu beta v a-expectedLogSlicePartition N k mu beta)
      ∂positiveCubeLaw K)=cubeAveragedPressure N k K mu beta v-expectedLogSlicePartition N k mu beta := by
    rw [integral_sub hI (integrable_const _),integral_const,probReal_univ,one_smul]
    rfl
  have hLo := integral_nonneg_of_ae ((positiveCubeLaw_abs_le_two K).mono
    (fun a ha => (pressure_perturbation_bounds (k := k) hN hmu beta v a ha).1))
  have hHi := integral_mono_ae hD (integrable_const (4*v^2)) ((positiveCubeLaw_abs_le_two K).mono
    (fun a ha => (pressure_perturbation_bounds (k := k) hN hmu beta v a ha).2))
  simp only [Pi.sub_apply] at hHi
  rw [hEq] at hLo hHi
  simpa only [integral_const,probReal_univ,one_smul] using And.intro hLo hHi

theorem eventually_cube_averaged_ass_increment_lower (M k K : ℕ) (hM : 0< M) (hk : 3≤ k)
    {mu delta gamma : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (hdelta : 0< delta)
    (hgamma0 : 0< gamma) (hgamma1 : gamma<1/2) (beta : ℝ) {eps : ℝ} (heps : 0< eps) :
    ∀ᶠ N : ℕ in atTop,
      (∫a,perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a∂positiveCubeLaw K)+
        Real.log (annulusMass M delta)-(M : ℝ)*delta*beta^2*deriv (Scalar.xiSlice k mu) 1-eps≤
      cubeAveragedPressure (N+M) k K mu beta (((N+M : ℕ) : ℝ)^gamma)-
        cubeAveragedPressure N k K mu beta ((N : ℝ)^gamma) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_perturbed_ass_increment_lower M k K hM hk hmu hdelta hgamma0 hgamma1 beta heps] with N hN hASS
  have hPhi := perturbed_cavity_cube_integrable (k := k) (K := K) hN hM hmu beta ((N : ℝ)^gamma)
  have hC := perturbed_pressure_cube_integrable (k := k) (K := K) hN hmu beta ((N : ℝ)^gamma)
  have hCP := perturbed_pressure_cube_integrable (k := k) (K := K) (show 0< N+M by omega) hmu beta (((N+M : ℕ) : ℝ)^gamma)
  let L := (M : ℝ)*delta*beta^2*deriv (Scalar.xiSlice k mu) 1
  have hPlus : Integrable (fun a => perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a+Real.log (annulusMass M delta)) (positiveCubeLaw K) :=
    hPhi.add (integrable_const _)
  have hMinus : Integrable (fun a => perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a+Real.log (annulusMass M delta)-L) (positiveCubeLaw K) :=
    hPlus.sub (integrable_const L)
  have H := integral_mono_ae (hMinus.sub (integrable_const eps))
    (hCP.sub hC) ((positiveCubeLaw_abs_le_two K).mono (fun a ha => hASS a ha))
  have hLhs : (∫a,(perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a+
      Real.log (annulusMass M delta)-L-eps)∂positiveCubeLaw K)=
      (∫a,perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a∂positiveCubeLaw K)+
        Real.log (annulusMass M delta)-L-eps := by
    rw [integral_sub hMinus (integrable_const eps),
      integral_sub hPlus (integrable_const L),integral_add hPhi (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [hLhs,integral_sub hCP hC] at H
  exact H

theorem normalized_cube_averaged_pressure_cost (k K : ℕ) {mu gamma : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (hgamma0 : 0< gamma) (hgamma1 : gamma<1/2) (beta : ℝ)
    {eps : ℝ} (heps : 0< eps) :
    ∀ᶠ N : ℕ in atTop,
      |cubeAveragedPressure N k K mu beta ((N : ℝ)^gamma)/(N : ℝ)-
        expectedLogSlicePartition N k mu beta/(N : ℝ)|≤ eps := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    normalized_pressure_perturbation_cost k K hmu hgamma0 hgamma1 beta heps] with N hN hBudget
  have hI := perturbed_pressure_cube_integrable (k := k) (K := K) hN hmu beta ((N : ℝ)^gamma)
  have hF := (hI.div_const (N : ℝ)).sub (integrable_const (expectedLogSlicePartition N k mu beta/(N : ℝ)))
  have H := integral_mono_ae hF.abs (integrable_const eps)
    ((positiveCubeLaw_abs_le_two K).mono (fun a ha => hBudget a ha))
  have H' := (abs_integral_le_integral_abs).trans H
  simp only [Pi.sub_apply,Pi.div_apply] at H'
  rw [integral_sub (hI.div_const (N : ℝ)) (integrable_const _),integral_div] at H'
  simpa only [integral_const,probReal_univ,one_smul,cubeAveragedPressure] using H'

theorem normalized_cube_averaged_pressure_transfer (k K : ℕ) {mu gamma : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (hgamma0 : 0< gamma) (hgamma1 : gamma<1/2) (beta : ℝ) :
    Tendsto (fun N : ℕ => cubeAveragedPressure N k K mu beta ((N : ℝ)^gamma)/(N : ℝ)-
      expectedLogSlicePartition N k mu beta/(N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [normalized_cube_averaged_pressure_cost k K hmu hgamma0 hgamma1 beta (half_pos heps)] with N hN
  simpa only [Real.dist_eq,sub_zero] using lt_of_le_of_lt hN (half_lt_self heps)

end
end TensorPCA.NonRSLowerProofs.FiniteCavitySameCubePressure
