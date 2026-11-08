-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltJoint

/-! The finite fractional-moment inequality retaining a spin shell under the one-step
Gaussian tilt, including a cutoff on the outer field.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltFractional
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTilt
open scoped RealInnerProductSpace Topology
noncomputable section

theorem restricted_fractional_moment_lower {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (f p : Ω → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) mu) (hp : Measurable p)
    (hp01 : ∀ x, p x ∈ Icc (0 : ℝ) 1) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    {A : Set Ω} (hA : MeasurableSet A) :
    (∫ x, Real.exp (f x) ∂mu)*(∫ x in A, p x ∂mu.tilted f) ≤
      ∫ x in A, Real.exp (f x)*(p x)^m ∂mu := by
  have hZ : 0 < ∫ x, Real.exp (f x) ∂mu := integral_exp_pos hf
  have hPow (x : Ω) : p x ≤ (p x)^m := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (hp01 x).1 (hp01 x).2 hm0.le hm1
  have hIp := hf.mul_bdd hp.aestronglyMeasurable
    (Eventually.of_forall fun x => show ‖p x‖ ≤ (1 : ℝ) by
      rw [Real.norm_eq_abs,abs_of_nonneg (hp01 x).1]
      exact (hp01 x).2)
  have hIpm := hf.mul_bdd (hp.pow_const m).aestronglyMeasurable
    (Eventually.of_forall fun x => show ‖(p x)^m‖ ≤ (1 : ℝ) by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hp01 x).1 _)]
      exact Real.rpow_le_one (hp01 x).1 (hp01 x).2 hm0.le)
  calc
    _ = ∫ x in A, Real.exp (f x)*p x ∂mu := by
      rw [setIntegral_tilted' f p hA,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul]
      field_simp [hZ.ne']
    _ ≤ _ := integral_mono hIp.integrableOn hIpm.integrableOn
      (fun x => mul_le_mul_of_nonneg_left (hPow x) (Real.exp_pos _).le)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Literal conditional probability of the desired spin set under the
independent conditional Gaussian. -/
def conditionalShellProbability (B v : ℝ) (y : E) (S : Set E) (g : E) : ℝ :=
  ∫ z : E, S.indicator (fun _ => (1 : ℝ))
    ((1/B) • (y+Real.sqrt v • g)+(Real.sqrt B)⁻¹ • z) ∂stdGaussian E

theorem conditionalShellProbability_measurable (B v : ℝ) (y : E)
    {S : Set E} (hS : MeasurableSet S) :
    Measurable (conditionalShellProbability B v y S) := by
  have hF : Measurable (fun p : E×E => S.indicator (fun _ => (1 : ℝ))
      ((1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2)) :=
    (measurable_const.indicator hS).comp (by fun_prop)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem conditionalShellProbability_mem_Icc (B v : ℝ) (y g : E)
    {S : Set E} (hS : MeasurableSet S) :
    conditionalShellProbability B v y S g ∈ Icc (0 : ℝ) 1 := by
  let F : E → E := fun z => (1/B) • (y+Real.sqrt v • g)+(Real.sqrt B)⁻¹ • z
  have hF : Measurable (fun z : E => S.indicator (fun _ => (1 : ℝ)) (F z)) :=
    (measurable_const.indicator hS).comp (by dsimp [F]; fun_prop)
  have hI : Integrable (fun z : E => S.indicator (fun _ => (1 : ℝ)) (F z)) (stdGaussian E) := by
    apply (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : F z ∈ S <;> simp [hz]
  constructor
  · change 0 ≤ ∫ z, S.indicator (fun _ => (1 : ℝ)) (F z) ∂stdGaussian E
    apply integral_nonneg
    intro z
    change (0 : ℝ) ≤ S.indicator (fun _ => (1 : ℝ)) (F z)
    by_cases hz : F z ∈ S
    · rw [indicator_of_mem hz]
      norm_num
    · rw [indicator_of_notMem hz]
  · have H := integral_mono hI (integrable_const (1 : ℝ)) (fun z => by
      by_cases hz : F z ∈ S <;> simp [hz])
    simpa only [conditionalShellProbability,integral_const,probReal_univ,one_smul] using H

theorem integral_conditionalShellProbability_eq_joint (B v : ℝ) (y : E)
    (mu : Measure E) [IsProbabilityMeasure mu] {A S : Set E}
    (hA : MeasurableSet A) (hS : MeasurableSet S) :
    (∫ g in A, conditionalShellProbability B v y S g ∂mu) =
      (mu.prod (stdGaussian E)).real {p : E×E | p.1 ∈ A ∧
        (1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2 ∈ S} := by
  let T : Set (E×E) := {p | p.1 ∈ A ∧
    (1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2 ∈ S}
  have hT : MeasurableSet T := (hA.preimage measurable_fst).inter
    (hS.preimage (by fun_prop))
  have hInt : Integrable (T.indicator (fun _ => (1 : ℝ)))
      (mu.prod (stdGaussian E)) := (integrable_const _).indicator hT
  calc
    _ = ∫ g, A.indicator (conditionalShellProbability B v y S) g ∂mu :=
      (integral_indicator hA).symm
    _ = ∫ g, ∫ z, T.indicator (fun _ => (1 : ℝ)) (g,z) ∂stdGaussian E ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with g
      by_cases hg : g ∈ A
      · rw [indicator_of_mem hg]
        unfold conditionalShellProbability
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : (1/B) • (y+Real.sqrt v • g)+(Real.sqrt B)⁻¹ • z ∈ S
        · rw [indicator_of_mem hz,indicator_of_mem (show (g,z) ∈ T from ⟨hg,hz⟩)]
        · rw [indicator_of_notMem hz,indicator_of_notMem (show (g,z) ∉ T from
            fun h => hz h.2)]
      · rw [indicator_of_notMem hg]
        symm
        apply integral_eq_zero_of_ae
        filter_upwards [] with z
        exact indicator_of_notMem (show (g,z) ∉ T from fun h => hg h.1) _
    _ = ∫ p, T.indicator (fun _ => (1 : ℝ)) p ∂mu.prod (stdGaussian E) :=
      (integral_prod _ hInt).symm
    _ = _ := by simpa only [T,smul_eq_mul,mul_one] using integral_indicator_const (1 : ℝ) hT

/-- Exact finite Gaussian fractional-shell lower bound. No norm-shell
concentration, endpoint pressure formula, or independence of a selected
configuration is assumed. -/
theorem fractional_shell_moment_lower {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (hm0 : 0 < m) (hm1 : m ≤ 1) (y : E)
    {A S : Set E} (hA : MeasurableSet A) (hS : MeasurableSet S) :
    (∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian E)*
      ((((stdGaussian E).tilted (tiltExponent B v m y)).prod (stdGaussian E)).real
        {p : E×E | p.1 ∈ A ∧
          (1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2 ∈ S}) ≤
      ∫ g in A, (Real.exp (‖y+Real.sqrt v • g‖^2/(2*B))*
        conditionalShellProbability B v y S g)^m ∂stdGaussian E := by
  letI := tilted_probability hB hv hD y
  have H := restricted_fractional_moment_lower (stdGaussian E) (tiltExponent B v m y)
    (conditionalShellProbability B v y S) (tiltExponent_exp_integrable hB hv hD y)
    (conditionalShellProbability_measurable B v y hS)
    (fun g => conditionalShellProbability_mem_Icc B v y g hS) hm0 hm1 hA
  rw [integral_conditionalShellProbability_eq_joint B v y _ hA hS] at H
  convert H using 1
  apply integral_congr_ae
  filter_upwards [] with g
  rw [Real.mul_rpow (Real.exp_pos _).le
    (conditionalShellProbability_mem_Icc B v y g hS).1,← Real.exp_mul]
  congr 1
  congr 1
  unfold tiltExponent
  ring

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltFractional
