-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairWindowReflectionProofs

/-! Compact-uniform control of the N=1 branch of the coupled trial bound. This uses the coarse partition bound and full parameter
continuity, retaining the absolute window and EReal convention. -/

@[expose] public section
namespace TensorPCA.CoupledFinitePaddingProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- The literal four-parameter trial is continuous at every admissible point.
The positive m and all three logarithm margins are checked explicitly. -/
theorem continuousAt_trial_vector (k : ℕ) {barLam : ℝ} {p : Fin 4 → ℝ}
    (hp : Coupled.Admissible k barLam p) :
    ContinuousAt (fun z : Fin 4 → ℝ ↦ Coupled.trial k (z 0) (z 1) (z 2) (z 3)) p := by
  rcases hp with ⟨_hlam,hm,hL,hu,hmargin⟩
  let a : (Fin 4 → ℝ) → ℝ := fun z ↦ Coupled.xiPrime k (z 0) (z 3)
  let A : (Fin 4 → ℝ) → ℝ := fun z ↦ 1+a z-z 2
  let B : (Fin 4 → ℝ) → ℝ := fun z ↦ 1+a z+z 2
  let D : (Fin 4 → ℝ) → ℝ := fun z ↦ 1+(1-z 1)*a z-z 2
  have ha : 0 ≤ a p := by
    dsimp [a]
    unfold Coupled.xiPrime
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)) (pow_nonneg hu.1 _)
  have hmpos : 0 < p 1 := lt_of_lt_of_le zero_lt_one hm.1
  have hDpos : 0 < D p := hmargin
  have hApos : 0 < A p := by
    change 0 < 1+a p-p 2
    change 0 < 1+(1-p 1)*a p-p 2 at hmargin
    nlinarith [hm.1]
  have hBpos : 0 < B p := by change 0 < 1+a p+p 2; linarith [hL.1]
  have hA : Continuous A := by dsimp [A,a]; unfold Coupled.xiPrime; fun_prop
  have hB : Continuous B := by dsimp [B,a]; unfold Coupled.xiPrime; fun_prop
  have hD : Continuous D := by dsimp [D,a]; unfold Coupled.xiPrime; fun_prop
  have hBase : Continuous (fun z : Fin 4 → ℝ ↦
      (z 0)^2+(1-z 1)*Coupled.theta k (z 0) (z 3)-z 2*z 3) := by
    unfold Coupled.theta
    fun_prop
  have hInv : ContinuousAt (fun z : Fin 4 → ℝ ↦ (1 : ℝ)/z 1) p :=
    continuousAt_const.div (continuous_apply 1).continuousAt hmpos.ne'
  have hRatio := (hA.continuousAt.div hD.continuousAt hDpos.ne').log (div_ne_zero hApos.ne' hDpos.ne')
  have hLogs := (hB.continuousAt.log hBpos.ne').add (hA.continuousAt.log hApos.ne')
  change ContinuousAt (fun z : Fin 4 → ℝ ↦
    (z 0)^2+(1-z 1)*Coupled.theta k (z 0) (z 3)-z 2*z 3+
      (1/z 1)*Real.log (A z/D z)-(1/2 : ℝ)*(Real.log (B z)+Real.log (A z))) p
  exact (hBase.continuousAt.add (hInv.mul hRatio)).sub (continuousAt_const.mul hLogs)

/-- The one-dimensional physical branch has a compact-uniform trial
bound; no signed-window substitution or scalar lower-bound assumption is used. -/
theorem dimension_one_compact_trial_bound (k : ℕ) (heven : Even k) (barLam : ℝ)
    (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) (hKad : K ⊆ {p | Coupled.Admissible k barLam p}) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ eta : ℝ, 0 < eta →
      Coupled.expectedCoupledFreeEnergy 1 k (p 0) (p 3) eta ≤
        ((Coupled.trial k (p 0) (p 1) (p 2) (p 3)+C*eta+C*Real.log 2 : ℝ) : EReal) := by
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨1,zero_lt_one,?_⟩
    intro p hp
    exact hp.elim
  have hcont : ContinuousOn (fun p : Fin 4 → ℝ ↦
      (p 0)^2-Coupled.trial k (p 0) (p 1) (p 2) (p 3)) K := by
    intro p hp
    exact (((continuous_apply (0 : Fin 4)).pow 2).continuousAt.sub
      (continuousAt_trial_vector k (hKad hp))).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hcont
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := (|M|+1)/Real.log 2
  have hC : 0 < C := div_pos (by positivity) hlog
  have hCeq : C*Real.log 2 = |M|+1 := div_mul_cancel₀ _ hlog.ne'
  refine ⟨C,hC,?_⟩
  intro p hp eta heta
  have hgap : (p 0)^2-Coupled.trial k (p 0) (p 1) (p 2) (p 3) ≤ M :=
    hM (mem_image_of_mem _ hp)
  have hreal : (p 0)^2 ≤ Coupled.trial k (p 0) (p 1) (p 2) (p 3)+C*eta+C*Real.log 2 := by
    nlinarith [le_abs_self M, mul_pos hC heta]
  apply (PairWindowReflectionProofs.expectedCoupledFreeEnergy_le_sq (by decide : 0 < 1)
    heven (p 0) (hKad hp).1.1 (p 3) eta).trans
  exact_mod_cast hreal

end
end TensorPCA.CoupledFinitePaddingProofs
