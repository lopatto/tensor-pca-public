-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FreeEnergyProofs

/-! All-orders smoothness of bounded linear Gibbs integrals. The derivative is
a finite sum of weighted scalar moments, permitting induction on differentiability order. -/

@[expose] public section
namespace TensorPCA.GibbsSmoothProofs
open Set Filter MeasureTheory ProbabilityTheory GaussianSpinInterpolation
open scoped Topology RealInnerProductSpace ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V E : Type*} [MeasurableSpace V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem momentDerivative_decomposition {ι : Type*} [Fintype ι]
    (ν : Measure V) [IsFiniteMeasure ν] (ρ : V → ℝ) (L : V → E →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ}
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (b : OrthonormalBasis ι ℝ E) (w : E) :
    momentDerivative ν ρ L w =
      ∑ i, moment ν (fun v ↦ ρ v*L v (b i)) L w • innerSL ℝ (b i) := by
  classical
  ext d
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  calc
    momentDerivative ν ρ L w d =
      ∑ i, inner ℝ (b i) d*momentDerivative ν ρ L w (b i) := by
      have H := congrArg (fun u : E ↦ momentDerivative ν ρ L w u) (b.sum_repr' d)
      simpa only [map_sum, map_smul, smul_eq_mul] using H.symm
    _ = _ := by
      simp_rw [momentDerivative_apply ν ρ L hρ hL hb w]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem moment_contDiff_nat (ν : Measure V) [IsFiniteMeasure ν]
    (L : V → E →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hLb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) :
    ∀ (ρ : V → ℝ), Measurable ρ → ∀ C : ℝ, 0 ≤ C →
      (∀ᵐ v ∂ν, |ρ v| ≤ C) → ContDiff ℝ (n : ℕ∞ω) (moment ν ρ L) := by
  induction n with
  | zero =>
      intro ρ hρ C hC hρb
      exact contDiff_zero.mpr (moment_contDiff ν ρ L hρ hL hC hK (hρb.and hLb)).continuous
  | succ n ih =>
      intro ρ hρ C hC hρb
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨momentDerivative ν ρ L, ?_, fun w ↦ moment_hasFDerivAt ν ρ L hρ hL hC hK
        (hρb.and hLb) w⟩
      let b := stdOrthonormalBasis ℝ E
      have hfun : momentDerivative ν ρ L = (fun w : E ↦
          ∑ i, moment ν (fun v ↦ ρ v*L v (b i)) L w • innerSL ℝ (b i)) :=
        funext (momentDerivative_decomposition ν ρ L hρ hL (hρb.and hLb) b)
      rw [hfun]
      apply ContDiff.sum
      intro i _
      have hLi : Measurable (fun v ↦ L v (b i)) :=
        (ContinuousLinearMap.apply ℝ ℝ (b i)).continuous.measurable.comp hL
      have hnew : ∀ᵐ v ∂ν, |ρ v*L v (b i)| ≤ C*K := by
        filter_upwards [hρb.and hLb] with v hv
        have hLiNorm := (L v).le_opNorm (b i)
        rw [Real.norm_eq_abs, b.orthonormal.norm_eq_one i, mul_one] at hLiNorm
        rw [abs_mul]
        exact mul_le_mul hv.1 (hLiNorm.trans hv.2) (abs_nonneg _) hC
      exact (ih (fun v ↦ ρ v*L v (b i)) (hρ.mul hLi) (C*K) (mul_nonneg hC hK) hnew).smul
        contDiff_const

theorem moment_contDiff_infty (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → E →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) :
    ContDiff ℝ ∞ (moment ν ρ L) := by
  apply contDiff_infty.mpr
  intro n
  exact moment_contDiff_nat ν L hL hK (hb.mono (fun _ hv ↦ hv.2)) n ρ hρ C hC
    (hb.mono (fun _ hv ↦ hv.1))


theorem logPartition_contDiff_infty (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → E →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : ContDiff ℝ ∞ (logPartition ν L) := by
  have H := moment_contDiff_infty ν (fun _ ↦ 1) L measurable_const hL zero_le_one hK
    (hb.mono (fun v hv ↦ ⟨by norm_num, hv⟩))
  exact H.log (fun w ↦ (moment_one_pos ν L hL hb w).ne')

/-- The genuine global smoothness required by the sharp Gaussian Poincare
domain, proved from bounded spherical features rather than supplied as a premise. -/
theorem freeEnergy_contDiff_infty {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    ContDiff ℝ ∞ (Model.freeEnergy N k lam) := by
  have H := (logPartition_contDiff_infty (Model.spherePrior N)
    (FreeEnergyProofs.thermalLinear N k lam)
    (FreeEnergyProofs.thermalLinear_continuous N k lam).measurable
    (by positivity : 0 ≤ |lam| * Real.sqrt N) (FreeEnergyProofs.thermalLinear_bound hN lam)).div_const
      (N : ℝ)
  convert H using 1
  funext w
  exact FreeEnergyProofs.freeEnergy_eq_logPartition N k lam w

end
end TensorPCA.GibbsSmoothProofs
