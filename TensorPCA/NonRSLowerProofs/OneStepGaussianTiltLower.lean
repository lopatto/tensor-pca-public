-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltEndpoint
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltShellIdentity
public import TensorPCA.NonRSLowerProofs.OneStepGaussianShellPolar

/-! Finite lower bound for the literal one-step spherical endpoint. The intermediate
good-event probability is the tilted Gaussian spin/field event; Gaussian
concentration discharges this finite input in the next module.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLower
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTilt OneStepGaussianTiltFractional
open OneStepGaussianTiltEndpoint OneStepGaussianTiltShellIdentity
open OneStepGaussianShellChernoff OneStepGaussianShellPolar
open scoped RealInnerProductSpace Topology
noncomputable section

theorem shell_kernel_le_sphericalLaplace {N : ℕ} (hN : 0 < N) {B eps C v : ℝ}
    (hB : 0 < B) (heps : 0 ≤ eps) (hC : 0 ≤ C) (y g : Model.Vector N)
    (hh : ‖y+Real.sqrt v • g‖ ≤ C*Real.sqrt (N : ℝ)) :
    Real.exp (‖y+Real.sqrt v • g‖^2/(2*B))*
      conditionalShellProbability B v y
        {x | |‖x‖^2-(N : ℝ)| ≤ eps*(N : ℝ)} g ≤
    Real.exp ((N : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2)))*
      sphericalLaplace N (y+Real.sqrt v • g) := by
  have hS : MeasurableSet {x : Model.Vector N |
      |‖x‖^2-(N : ℝ)| ≤ eps*(N : ℝ)} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [conditional_shell_factor_eq_reference_integral hB v y g hS]
  have H := polar_shell_comparison hN hB heps hC (y+Real.sqrt v • g) hh
  have Hb := shell_probability_upper (E := Model.Vector N) hB heps
  simp only [Model.Vector, finrank_euclideanSpace, Fintype.card_fin] at Hb
  apply H.trans
  change _ ≤ _*sphericalLaplace N (y+Real.sqrt v • g)
  calc
    _ ≤ Real.exp ((N : ℝ)*(-(B-1-Real.log B)/2+|B-1| * eps/2))*
        Real.exp (eps*C*(N : ℝ))*sphericalLaplace N (y+Real.sqrt v • g) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right Hb (Real.exp_pos _).le)
        (sphericalLaplace_pos hN _).le
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- A fixed positive good-event probability already suffices. Every integral and event
in this bound uses the finite Gaussian and spherical laws.
-/
theorem normalizer_half_le_fractional_moment {N : ℕ} (hN : 0 < N)
    {B v m eps C : ℝ} (hB : 0 < B) (hv : 0 ≤ v) (hD : 0 < B-m*v)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (heps : 0 ≤ eps) (hC : 0 ≤ C)
    (y : Model.Vector N)
    (hgood : (1 : ℝ)/2 ≤
      ((((stdGaussian (Model.Vector N)).tilted (tiltExponent B v m y)).prod
        (stdGaussian (Model.Vector N))).real
        {p : Model.Vector N×Model.Vector N |
          ‖y+Real.sqrt v • p.1‖ ≤ C*Real.sqrt (N : ℝ) ∧
          |‖(1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2‖^2-(N : ℝ)| ≤
            eps*(N : ℝ)})) :
    (∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian (Model.Vector N))/2 ≤
      Real.exp (m*(N : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2)))*
        fractionalSphereMoment N m v y := by
  let A : Set (Model.Vector N) := {g | ‖y+Real.sqrt v • g‖ ≤ C*Real.sqrt (N : ℝ)}
  let S : Set (Model.Vector N) := {x | |‖x‖^2-(N : ℝ)| ≤ eps*(N : ℝ)}
  let F : Model.Vector N → ℝ := fun g =>
    (Real.exp (‖y+Real.sqrt v • g‖^2/(2*B))*conditionalShellProbability B v y S g)^m
  let K := Real.exp (m*(N : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2)))
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hFm : Measurable F :=
    ((by fun_prop : Measurable (fun g : Model.Vector N =>
      Real.exp (‖y+Real.sqrt v • g‖^2/(2*B)))).mul
        (conditionalShellProbability_measurable B v y hS)).pow_const m
  have hF0 (g : Model.Vector N) : 0 ≤ F g :=
    Real.rpow_nonneg (mul_nonneg (Real.exp_pos _).le
      (conditionalShellProbability_mem_Icc B v y g hS).1) m
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hBound (g : Model.Vector N) (hg : g ∈ A) :
      F g ≤ K*(sphericalLaplace N (y+Real.sqrt v • g))^m := by
    have H := Real.rpow_le_rpow (mul_nonneg (Real.exp_pos _).le
        (conditionalShellProbability_mem_Icc B v y g hS).1)
      (shell_kernel_le_sphericalLaplace hN hB heps hC y g hg) hm0.le
    calc
      F g ≤ (Real.exp ((N : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2)))*
        sphericalLaplace N (y+Real.sqrt v • g))^m := H
      _ = (Real.exp ((N : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2))))^m*
        (sphericalLaplace N (y+Real.sqrt v • g))^m :=
          Real.mul_rpow (Real.exp_pos _).le (sphericalLaplace_pos hN _).le
      _ = _ := by rw [← Real.exp_mul]; dsimp only [K]; congr 2; ring
  have hJm : Measurable (A.indicator F) := hFm.indicator hA
  have hJBound (g : Model.Vector N) :
      ‖A.indicator F g‖ ≤ K*(sphericalLaplace N (y+Real.sqrt v • g))^m := by
    by_cases hg : g ∈ A
    · rw [indicator_of_mem hg,Real.norm_eq_abs,abs_of_nonneg (hF0 g)]
      exact hBound g hg
    · rw [indicator_of_notMem hg,norm_zero]
      exact mul_nonneg hK0 (Real.rpow_nonneg (sphericalLaplace_pos hN _).le _)
  have hMaj := (fractionalSphereMoment_integrable hN hm0.le v y).const_mul K
  have hJInt : Integrable (A.indicator F) (stdGaussian (Model.Vector N)) :=
    hMaj.mono' hJm.aestronglyMeasurable (Eventually.of_forall hJBound)
  have hIntBound : (∫ g in A, F g ∂stdGaussian (Model.Vector N)) ≤
      K*fractionalSphereMoment N m v y := by
    rw [← integral_indicator hA]
    apply (integral_mono hJInt hMaj (fun g =>
      (show A.indicator F g ≤ ‖A.indicator F g‖ by
        simpa only [Real.norm_eq_abs] using le_abs_self (A.indicator F g)).trans
          (hJBound g))).trans_eq
    rw [integral_const_mul]
    rfl
  have H := fractional_shell_moment_lower hB hv hD hm0 hm1 y hA hS
  have hZ : 0 ≤ ∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian (Model.Vector N) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  calc
    _ ≤ (∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian (Model.Vector N))*
      ((((stdGaussian (Model.Vector N)).tilted (tiltExponent B v m y)).prod
        (stdGaussian (Model.Vector N))).real
        {p : Model.Vector N×Model.Vector N | p.1 ∈ A ∧
          (1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2 ∈ S}) := by
      simpa only [A,S,mem_ofPred_eq,div_eq_mul_inv,one_mul] using
        mul_le_mul_of_nonneg_left hgood hZ
    _ ≤ ∫ g in A, F g ∂stdGaussian (Model.Vector N) := H
    _ ≤ _ := hIntBound

/-- The explicit finite lower bound.  Its good-event premise is discharged
from Gaussian norm moments under the stationary precision condition. -/
theorem normalized_log_fractional_moment_lower {N : ℕ} (hN : 0 < N)
    {B v m eps C : ℝ} (hB : 0 < B) (hv : 0 ≤ v) (hD : 0 < B-m*v)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (heps : 0 ≤ eps) (hC : 0 ≤ C)
    (y : Model.Vector N)
    (hgood : (1 : ℝ)/2 ≤
      ((((stdGaussian (Model.Vector N)).tilted (tiltExponent B v m y)).prod
        (stdGaussian (Model.Vector N))).real
        {p : Model.Vector N×Model.Vector N |
          ‖y+Real.sqrt v • p.1‖ ≤ C*Real.sqrt (N : ℝ) ∧
          |‖(1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2‖^2-(N : ℝ)| ≤
            eps*(N : ℝ)})) :
    ‖y‖^2/(2*(N : ℝ)*(B-m*v)) + Real.log (B/(B-m*v))/(2*m) +
      (B-1-Real.log B)/2 - eps*(C+|B-1|/2) - Real.log 2/(m*(N : ℝ)) ≤
      Real.log (fractionalSphereMoment N m v y)/(m*(N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hZ : 0 < ∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian (Model.Vector N) :=
    integral_exp_pos (tiltExponent_exp_integrable hB hv hD y)
  have hM : 0 < fractionalSphereMoment N m v y :=
    fractionalSphereMoment_pos hN hm0.le v y
  have H := Real.log_le_log (div_pos hZ (by norm_num))
    (normalizer_half_le_fractional_moment hN hB hv hD hm0 hm1 heps hC y hgood)
  rw [Real.log_div hZ.ne' (by norm_num),
    Real.log_mul (Real.exp_pos _).ne' hM.ne',Real.log_exp,
    log_integral_exp_tiltExponent hB hv hD] at H
  simp only [Model.Vector,finrank_euclideanSpace,Fintype.card_fin] at H
  apply (le_div_iff₀ (mul_pos hm0 hNr)).mpr
  have heq :
      (‖y‖^2/(2*(N : ℝ)*(B-m*v)) + Real.log (B/(B-m*v))/(2*m) +
        (B-1-Real.log B)/2 - eps*(C+|B-1|/2) - Real.log 2/(m*(N : ℝ)))*
          (m*(N : ℝ)) =
      ((N : ℝ)/2)*Real.log (B/(B-m*v)) + m*‖y‖^2/(2*(B-m*v)) - Real.log 2 -
        m*(N : ℝ)*(-(B-1-Real.log B)/2+eps*(C+|B-1|/2)) := by
    field_simp [hNr.ne',hm0.ne',hD.ne']
    ring
  rw [heq]
  linarith

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLower
