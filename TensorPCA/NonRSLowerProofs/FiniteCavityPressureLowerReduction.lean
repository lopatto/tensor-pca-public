-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavitySameCubePressure
public import TensorPCA.NonRSLowerProofs.FiniteCavityIncrementTransfer
public import TensorPCA.NonRSLowerProofs.FiniteCavityAnnulusMassAsymptotics
public import TensorPCA.NonRSLowerProofs.PhysicalPressureGroundReduction

/-! The fixed-cavity pressure passage uses expected log partitions and a dimension-
uniform lower bound on the same-cube cavity functional. One cavity size and one
perturbation bank are chosen before the ambient dimension.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPressureLowerReduction
open MeasureTheory ProbabilityTheory Filter Set
open FiniteCavitySameCubePressure FiniteCavityIncrementTransfer
open FiniteCavityAnnulusMassAsymptotics FiniteCavityPerturbedASSLower
open FiniteCavityASSLower FiniteCavityRetainedMass PhysicalPressureGroundReduction
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two literal physical pressure definitions differ only by beta*N. -/
theorem expectedSlicePressure_eq_raw_div (N k : ℕ) (mu beta : ℝ) :
    expectedSlicePressure N k mu beta = expectedLogSlicePartition N k mu beta/(beta*(N : ℝ)) := by
  unfold expectedSlicePressure expectedLogSlicePartition
    GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    GaussianSpinInterpolation.weight
  simp only [one_mul,innerSL_apply_apply,real_inner_smul_left]

/-- An M-first lower bound on the cavity functional yields an expected-log-partition
lower bound. The finite bank K is fixed for all large ambient dimensions and is
averaged over the same positive cube.
-/
theorem eventually_raw_pressure_lower_of_cavity (k : ℕ) (hk : 3≤k) {mu gamma : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (hgamma0 : 0<gamma) (hgamma1 : gamma<1/2)
    (beta L : ℝ)
    (hCavity : ∀ eps : ℝ,0<eps → ∀ᶠ M : ℕ in atTop,∃ K : ℕ,
      ∀ᶠ N : ℕ in atTop,L-eps≤
        (∫a,perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a
          ∂positiveCubeLaw K)/(M : ℝ))
    {eta : ℝ} (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,L-eta≤expectedLogSlicePartition N k mu beta/(N : ℝ) := by
  let e : ℝ := eta/8
  have he : 0<e := by dsimp [e]; positivity
  let d : ℝ := deriv (Scalar.xiSlice k mu) 1
  let delta : ℝ := e/(beta^2*|d|+1)
  have hden : 0<beta^2*|d|+1 := by positivity
  have hdelta : 0<delta := div_pos he hden
  have hdeltaEq : delta*(beta^2*|d|+1)=e := by
    exact div_mul_cancel₀ e hden.ne'
  have hLoss : delta*beta^2*d≤e := by
    have H := mul_le_mul_of_nonneg_left (le_abs_self d)
      (mul_nonneg hdelta.le (sq_nonneg beta))
    nlinarith only [H,hdeltaEq,hdelta.le]
  have hAnn : ∀ᶠ M : ℕ in atTop,-e≤Real.log (annulusMass M delta)/(M : ℝ) :=
    (annulus_log_div_dimension_tendsto_zero hdelta).eventually
      (Ici_mem_nhds (show -e<(0 : ℝ) by linarith only [he]))
  obtain ⟨M,hM,hAnnM,K,hLower⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and (hAnn.and (hCavity e he))).exists
  have hMr : (0 : ℝ)<M := Nat.cast_pos.mpr hM
  let C : ℕ→ℝ := fun N => cubeAveragedPressure N k K mu beta ((N : ℝ)^gamma)
  have hInc : ∀ᶠ N : ℕ in atTop,(M : ℝ)*(L-4*e)≤C (N+M)-C N := by
    filter_upwards [hLower,
      eventually_cube_averaged_ass_increment_lower M k K hM hk hmu hdelta
        hgamma0 hgamma1 beta (mul_pos hMr he)] with N hPhi hASS
    have hPhiMul := (le_div_iff₀ hMr).1 hPhi
    have hAnnMul := (le_div_iff₀ hMr).1 hAnnM
    have hLossMul := mul_le_mul_of_nonneg_left hLoss hMr.le
    dsimp only [C]
    dsimp only [d] at hLossMul
    nlinarith only [hPhiMul,hAnnMul,hLossMul,hASS]
  have hTransfer := eventual_normalized_lower_of_increment C hM hInc he
  filter_upwards [hTransfer,
    normalized_cube_averaged_pressure_cost k K hmu hgamma0 hgamma1 beta he] with N hN hCost
  have hCost' := (abs_le.1 hCost).2
  change L-4*e-e≤cubeAveragedPressure N k K mu beta ((N : ℝ)^gamma)/(N : ℝ) at hN
  dsimp only [e] at hN hCost'
  linarith only [hN,hCost',heta]

/-- The final beta division is performed exactly once. -/
theorem eventually_expectedSlicePressure_lower_of_cavity (k : ℕ) (hk : 3≤k)
    {mu gamma beta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (hgamma0 : 0<gamma) (hgamma1 : gamma<1/2) (hbeta : 0<beta)
    (hCavity : ∀ eps : ℝ,0<eps → ∀ᶠ M : ℕ in atTop,∃ K : ℕ,
      ∀ᶠ N : ℕ in atTop,beta*(FiniteCS.rawValue k beta mu).toReal/2-eps≤
        (∫a,perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a
          ∂positiveCubeLaw K)/(M : ℝ))
    {eta : ℝ} (heta : 0<eta) :
    ∀ᶠ n : ℕ in atTop,(FiniteCS.rawValue k beta mu).toReal/2-eta≤
      expectedSlicePressure (n+1) k mu beta := by
  have H := eventually_raw_pressure_lower_of_cavity k hk hmu hgamma0 hgamma1
    beta (beta*(FiniteCS.rawValue k beta mu).toReal/2) hCavity (mul_pos hbeta heta)
  obtain ⟨N0,hN0⟩ := eventually_atTop.1 H
  filter_upwards [eventually_ge_atTop N0] with n hn
  have hRaw := hN0 (n+1) (by omega)
  rw [expectedSlicePressure_eq_raw_div]
  have Hdiv : (FiniteCS.rawValue k beta mu).toReal/2-eta≤
      (expectedLogSlicePartition (n+1) k mu beta/((n+1 : ℕ) : ℝ))/beta := by
    apply (le_div_iff₀ hbeta).2
    nlinarith only [hRaw]
  simpa only [div_div,mul_comm ((n+1 : ℕ) : ℝ) beta] using Hdiv

/-- The finite-pressure reduction uses cavity bounds for each fixed positive temperature
parameter.
-/
theorem finitePressureLower_of_cavity (k : ℕ) (hk : 3≤k) {mu gamma : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (hgamma0 : 0<gamma) (hgamma1 : gamma<1/2)
    (hCavity : ∀ beta : ℝ,0<beta → ∀ eps : ℝ,0<eps →
      ∀ᶠ M : ℕ in atTop,∃ K : ℕ,∀ᶠ N : ℕ in atTop,
        beta*(FiniteCS.rawValue k beta mu).toReal/2-eps≤
        (∫a,perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a
          ∂positiveCubeLaw K)/(M : ℝ)) :
    FinitePressureLower k mu := by
  intro beta hbeta eta heta
  exact eventually_expectedSlicePressure_lower_of_cavity k hk hmu hgamma0 hgamma1
    hbeta (hCavity beta hbeta) heta

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPressureLowerReduction
