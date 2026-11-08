-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledSmallOverlapProofs
public import TensorPCA.CoupledMacroscopicProofs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Polynomial-scale absorption of the compact coupled trial remainder. -/
@[expose] public section
namespace TensorPCA.CoupledQuadraticProofs
open Set Filter CoupledSmallOverlapProofs CoupledMacroscopicProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem logarithmic_remainder_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => (1+Real.log ((N : ℝ)+1))/(N : ℝ)^r) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hden := (tendsto_rpow_atTop hr).comp hcast
  have hc := hden.const_div_atTop (1+Real.log 2)
  have hl := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero.comp hcast
  have hu : Tendsto (fun N : ℕ => (1+Real.log 2)/(N : ℝ)^r+Real.log (N : ℝ)/(N : ℝ)^r)
      atTop (𝓝 0) := by simpa only [Function.comp_def, add_zero] using hc.add hl
  apply tendsto_const_nhds.squeeze' hu
  · exact Eventually.of_forall (fun N => div_nonneg (by
      have hlog : 0 ≤ Real.log ((N : ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hlog : Real.log ((N : ℝ)+1) ≤ Real.log 2+Real.log (N : ℝ) := by
      have hh := Real.log_le_log (by linarith : (0 : ℝ) < (N : ℝ)+1)
        (by linarith : (N : ℝ)+1 ≤ 2*(N : ℝ))
      simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne'] using hh
    have hnum : 1+Real.log ((N : ℝ)+1) ≤ (1+Real.log 2)+Real.log (N : ℝ) := by linarith
    have hh := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (Nat.cast_nonneg N) r)
    simpa only [add_div] using hh

/-- The local gap of Lemma 4.2 follows from the compact-uniform trial bound and an explicit logarithmic-remainder limit. -/
theorem small_overlap_gap_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 4 ≤ k) (heven : Even k) {barLam eps : ℝ}
    (hbar : 0 ≤ barLam) (_hsub : barLam < Scalar.lambdaC k) (heps : eps ∈ Ioo (0 : ℝ) (1/2)) :
    ∃ c : ℝ, c ∈ Ioo (0 : ℝ) (1/2) ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ lam ∈ Icc (0 : ℝ) barLam, ∀ N : ℕ, N0 ≤ N → ∀ u : ℝ,
        (N : ℝ)^((-1/2 : ℝ)+eps) ≤ u → u < c →
        Coupled.expectedCoupledFreeEnergy N k lam u (1/(N : ℝ)) ≤
          ((lam^2-u^2/8 : ℝ) : EReal) := by
  obtain ⟨c,hc,hgap⟩ := uniform_diagonal_trial_gap k hk hbar
  let S : Set (ℝ×ℝ) := Icc (0 : ℝ) barLam ×ˢ Icc (0 : ℝ) c
  let F : (ℝ×ℝ) → Fin 4 → ℝ := fun z => trialParams z.1 1 z.2 z.2
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    unfold F trialParams
    split_ifs <;> fun_prop
  let K : Set (Fin 4 → ℝ) := F '' S
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hF
  have hKad : K ⊆ {p | Coupled.Admissible k barLam p} := by
    rintro p ⟨z,hz,rfl⟩
    obtain ⟨hp0,hp1,hp2,hp3⟩ := trialParams_apply z.1 1 z.2 z.2
    change Coupled.Admissible k barLam (trialParams z.1 1 z.2 z.2)
    simp only [Coupled.Admissible,hp0,hp1,hp2,hp3]
    have hmarg := (hgap z.1 hz.1 z.2 hz.2).1
    have hu1 : z.2 ≤ 1 := by linarith [hz.2.2,hc.2]
    exact ⟨hz.1,⟨le_rfl,by norm_num⟩,⟨hz.2.1,hu1⟩,
      ⟨hz.2.1,hu1⟩,by linarith⟩
  obtain ⟨C,hC,hbound⟩ := htrial k (by omega) heven barLam hbar K hK hKad
  have hrem := (logarithmic_remainder_tendsto (by linarith [heps.1] : 0 < 2*eps)).const_mul C
  have hevent : ∀ᶠ N : ℕ in atTop,
      C*((1+Real.log ((N : ℝ)+1))/(N : ℝ)^(2*eps)) < 1/8 :=
    hrem.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hevent
  refine ⟨c,hc,max N0 1,le_max_right _ _,?_⟩
  intro lam hlam N hN u hulo huc
  have hN1 : 1 ≤ N := (le_max_right N0 1).trans hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hu0 : 0 < u := (Real.rpow_pos_of_pos hNpos _).trans_le hulo
  have hupow : ((N : ℝ)^((-1/2 : ℝ)+eps))^2 ≤ u^2 :=
    (sq_le_sq₀ (Real.rpow_pos_of_pos hNpos _).le hu0.le).mpr hulo
  have hpow : ((N : ℝ)^((-1/2 : ℝ)+eps))^2 = (N : ℝ)^(-1+2*eps) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  rw [hpow] at hupow
  have hpowN : (N : ℝ)*(N : ℝ)^(-1+2*eps) = (N : ℝ)^(2*eps) := by
    calc
      _ = (N : ℝ)^(1 : ℝ)*(N : ℝ)^(-1+2*eps) := by rw [Real.rpow_one]
      _ = (N : ℝ)^((1 : ℝ)+(-1+2*eps)) := (Real.rpow_add hNpos _ _).symm
      _ = _ := by congr 1; ring
  have hmul := mul_le_mul_of_nonneg_left hupow hNpos.le
  rw [hpowN] at hmul
  have hbudget := (hN0 N ((le_max_left N0 1).trans hN)).le
  rw [← mul_div_assoc] at hbudget
  have hb := (div_le_iff₀ (Real.rpow_pos_of_pos hNpos (2*eps))).mp hbudget
  have herror : C/(N : ℝ)+C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤ u^2/8 := by
    have heq : C/(N : ℝ)+C*Real.log ((N : ℝ)+1)/(N : ℝ) = C*(1+Real.log ((N : ℝ)+1))/(N : ℝ) := by ring
    rw [heq]
    apply (div_le_iff₀ hNpos).mpr
    nlinarith
  have hp : F (lam,u) ∈ K := ⟨(lam,u),⟨hlam,⟨hu0.le,huc.le⟩⟩,rfl⟩
  have htrialN := hbound (F (lam,u)) hp N hN1 (1/(N : ℝ)) (one_div_pos.mpr hNpos)
  obtain ⟨hp0,hp1,hp2,hp3⟩ := trialParams_apply lam 1 u u
  dsimp only [F] at htrialN
  rw [hp0,hp1,hp2,hp3] at htrialN
  apply htrialN.trans
  have hreal : Coupled.trial k lam 1 u u+C*(1/(N : ℝ))+C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤ lam^2-u^2/8 := by
    have hg := (hgap lam hlam u ⟨hu0.le,huc.le⟩).2
    have heq : C*(1/(N : ℝ)) = C/(N : ℝ) := by ring
    rw [heq]
    linarith
  exact_mod_cast hreal

end
end TensorPCA.CoupledQuadraticProofs
