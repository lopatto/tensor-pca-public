-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledSignedEndpointProofs
public import TensorPCA.CoupledPressureComparisonProofs
public import TensorPCA.CoupledFinitePaddingProofs

/-! Endpoint constants and final coupled-trial assembly. The physical
angular interpolation comparison is required before the final trial export. -/
@[expose] public section
namespace TensorPCA.CoupledTrialProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def trialErrorConstant (k : ℕ) (barLam : ℝ) : ℝ :=
  CoupledEndpointBoundProofs.endpointErrorConstant (1+(k : ℝ)*barLam^2)+1

theorem trialErrorConstant_pos (k : ℕ) (barLam : ℝ) :
    0 < trialErrorConstant k barLam := by
  have H := CoupledEndpointBoundProofs.endpointErrorConstant_pos
    (show 1 ≤ 1+(k : ℝ)*barLam^2 from
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg barLam)))
  unfold trialErrorConstant
  linarith

theorem reflection_cost_absorbed {N : ℕ} (hN : 0 < N) (C : ℝ) {eta : ℝ} (heta : 0 ≤ eta) :
    C*eta+C*Real.log ((N : ℝ)+1)/(N : ℝ)+Real.log 2/(N : ℝ) ≤
      (C+1)*eta+(C+1)*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log 2 ≤ Real.log ((N : ℝ)+1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have H := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) N)
  ring_nf at H ⊢
  linarith

theorem actual_trial_endpoint_bound {N k : ℕ} (hN : 2 ≤ N)
    {barLam : ℝ} {p : Fin 4 → ℝ} (hp : Coupled.Admissible k barLam p)
    {eta : ℝ} (heta : 0 < eta) :
    CoupledSignedEndpointProofs.signedCommonFreshPressure N
      (Coupled.xiPrime k (p 0) (p 3)) (Coupled.xiPrime k (p 0) 1) (p 1) (p 3) eta-
        Coupled.theta k (p 0) 1+(1-p 1)*Coupled.theta k (p 0) (p 3)+Real.log 2/(N : ℝ) ≤
      Coupled.trial k (p 0) (p 1) (p 2) (p 3)+
        trialErrorConstant k barLam*eta+
          trialErrorConstant k barLam*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have ha := CoupledInterpolationProofs.trial_auxiliary_variances k (p 0) (p 3) hp.2.2.2.1
  have hB := CoupledMatrixProofs.admissible_radial_parameter k barLam hp 0
  rw [CoupledMatrixProofs.A4_diagonal] at hB
  have H := CoupledSignedEndpointProofs.signedCommonFreshPressure_uniform_bound hN
    ha.1 ha.2 hp.2.2.1 hp.2.1.1 hp.2.2.2.2 hB.2 hp.2.2.2.1 heta
  have ht := CoupledMatrixProofs.trial_matrix_representation k (p 0)
    hp.2.2.2.1.1 hp.2.1.1 hp.2.2.1.1 hp.2.2.2.2
  rw [CoupledMatrixProofs.determinant_ratio ha.1 hp.2.2.1.1 hp.2.2.2.2] at ht
  have He := reflection_cost_absorbed (by omega : 0 < N)
    (CoupledEndpointBoundProofs.endpointErrorConstant (1+(k : ℝ)*barLam^2)) heta.le
  unfold trialErrorConstant
  linarith

theorem actual_trial_bound_dimension_ge_two {N k : ℕ} (hN : 2 ≤ N)
    (hk : 2 ≤ k) (heven : Even k) {barLam : ℝ} {p : Fin 4 → ℝ}
    (hp : Coupled.Admissible k barLam p) {eta : ℝ} (heta : 0 < eta) :
    Coupled.expectedCoupledFreeEnergy N k (p 0) (p 3) eta ≤
      ((Coupled.trial k (p 0) (p 1) (p 2) (p 3)+
        (trialErrorConstant k barLam+2*(k : ℝ)*barLam^2)*eta+
          (trialErrorConstant k barLam+2*(k : ℝ)*barLam^2)*
            Real.log ((N : ℝ)+1)/(N : ℝ) : ℝ) : EReal) := by
  have Habs := PairWindowReflectionProofs.expectedCoupledFreeEnergy_le_signed
    hN heven (p 0) hp.2.2.2.1 heta
  have Hspin := CoupledPressureComparisonProofs.signed_freeEnergy_le_common_endpoint
    hN hk heven (p 0) hp.2.1 hp.2.2.2.1 heta
  have Hend := actual_trial_endpoint_bound hN hp heta
  have hB := CoupledMatrixProofs.admissible_radial_parameter k barLam hp 0
  rw [CoupledMatrixProofs.A4_diagonal] at hB
  have hd : Coupled.xiPrime k (p 0) 1 ≤ (k : ℝ)*barLam^2 := by linarith [hB.2]
  have hd2 : 2*Coupled.xiPrime k (p 0) 1 ≤ 2*((k : ℝ)*barLam^2) :=
    mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)
  have Heta : 2*Coupled.xiPrime k (p 0) 1*eta ≤ 2*(k : ℝ)*barLam^2*eta := by
    have H := mul_le_mul_of_nonneg_right hd2 heta.le
    nlinarith
  have hD : 0 ≤ 2*(k : ℝ)*barLam^2 := by positivity
  have hlog : 0 ≤ Real.log ((N : ℝ)+1) := Real.log_nonneg (by have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have HExtra : 0 ≤ (2*(k : ℝ)*barLam^2)*Real.log ((N : ℝ)+1)/(N : ℝ) :=
    div_nonneg (mul_nonneg hD hlog) (Nat.cast_nonneg N)
  apply Habs.trans
  have Hreal : PairWindowReflectionProofs.meanSignedPairFreeEnergy N k (p 0) (p 3) eta+
      Real.log 2/(N : ℝ) ≤ Coupled.trial k (p 0) (p 1) (p 2) (p 3)+
        (trialErrorConstant k barLam+2*(k : ℝ)*barLam^2)*eta+
          (trialErrorConstant k barLam+2*(k : ℝ)*barLam^2)*Real.log ((N : ℝ)+1)/(N : ℝ) := by
    ring_nf at Hspin Hend Heta HExtra ⊢
    linarith
  exact_mod_cast Hreal

theorem trial_remainder_mono {N : ℕ} (_hN : 0 < N) {C D eta : ℝ}
    (hCD : C ≤ D) (heta : 0 ≤ eta) :
    C*eta+C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      D*eta+D*Real.log ((N : ℝ)+1)/(N : ℝ) := by
  have hlog : 0 ≤ Real.log ((N : ℝ)+1) := Real.log_nonneg (by have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  exact add_le_add (mul_le_mul_of_nonneg_right hCD heta)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hlog) (Nat.cast_nonneg N))

theorem coupledTrialBound : Coupled.CoupledTrialBound := by
  intro k hk heven barLam hbar K hK hKad
  obtain ⟨C1,hC1,hPad⟩ := CoupledFinitePaddingProofs.dimension_one_compact_trial_bound
    k heven barLam K hK hKad
  let C2 := trialErrorConstant k barLam+2*(k : ℝ)*barLam^2
  have hC2 : 0 < C2 := add_pos_of_pos_of_nonneg (trialErrorConstant_pos k barLam) (by positivity)
  let C := C2+C1
  have hC : 0 < C := add_pos hC2 hC1
  refine ⟨C,hC,?_⟩
  intro p hp N hN eta heta
  by_cases hN2 : 2 ≤ N
  · have H := actual_trial_bound_dimension_ge_two hN2 hk heven (hKad hp) heta
    apply H.trans
    have hrem := trial_remainder_mono (N := N) (by omega : 0 < N)
      (C := C2) (D := C) (by dsimp [C]; linarith) heta.le
    have Hreal : Coupled.trial k (p 0) (p 1) (p 2) (p 3)+C2*eta+
        C2*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      Coupled.trial k (p 0) (p 1) (p 2) (p 3)+C*eta+
        C*Real.log ((N : ℝ)+1)/(N : ℝ) := by linarith
    dsimp only [C2] at Hreal
    exact_mod_cast Hreal
  · have hN1 : N = 1 := by omega
    subst N
    have H := hPad p hp eta heta
    apply H.trans
    have hrem := trial_remainder_mono (N := 1) (by decide : 0 < 1)
      (C := C1) (D := C) (by dsimp [C]; linarith) heta.le
    norm_num only [Nat.cast_one,div_one] at hrem
    have Hreal : Coupled.trial k (p 0) (p 1) (p 2) (p 3)+C1*eta+C1*Real.log 2 ≤
      Coupled.trial k (p 0) (p 1) (p 2) (p 3)+C*eta+C*Real.log 2 := by linarith
    norm_num only [Nat.cast_one,div_one]
    exact_mod_cast Hreal


end
end TensorPCA.CoupledTrialProofs
