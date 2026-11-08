-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTOneKnotProfileProofs

/-! Equality of the variational infima. Given any admissible competitor,
minimize above its own positive terminal value. The resulting constrained
minimizer has the exact four-parameter form and no greater cost. This proves
cofinality without asserting an unrestricted attained minimum. -/
@[expose] public section
namespace TensorPCA.FourParameterReductionProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem parisiFunctional_congr_on_Icc (xi : ℝ → ℝ) (h : ℝ) {p q : ℝ → ℝ}
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, p t = q t) :
    Scalar.parisiFunctional xi h p = Scalar.parisiFunctional xi h q := by
  unfold Scalar.parisiFunctional
  rw [heq 0 (by norm_num)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change deriv (deriv xi) t*p t+1/p t = deriv (deriv xi) t*q t+1/q t
  rw [heq t (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)]

theorem fourParameter_cost_cofinal (k : ℕ) (hk : 3 ≤ k) {m : ℝ} (hm : |m| < 1)
    (h : ℝ) {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    ∃ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q ∧
      Scalar.parisiFunctional (Scalar.xiSlice k m) h (Scalar.fourParameterProfile delta a b q) ≤
        Scalar.parisiFunctional (Scalar.xiSlice k m) h p := by
  have heps : 0 < p 1 := hp.2.2.2 1 (by norm_num)
  have hfloor : ∀ t ∈ Icc (0 : ℝ) 1, p 1 ≤ p t :=
    fun t ht => hp.2.1 ht (by norm_num) ht.2
  obtain ⟨r,hr,hrfloor,hrmin⟩ := JTFloorAttainmentProofs.exists_xiSlice_floor_minimizer k (by omega) hm h heps
  obtain ⟨delta,a,b,q,hAd,heq⟩ := JTOneKnotProfileProofs.xiSlice_floor_minimizer_eq_fourParameter
    k hk hm hr h heps hrfloor hrmin
  refine ⟨delta,a,b,q,hAd,?_⟩
  rw [← parisiFunctional_congr_on_Icc (Scalar.xiSlice k m) h heq]
  exact hrmin p hp hfloor

theorem xiSlice_variationalValue_eq_fourParameterValue (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm : |m| < 1) (h : ℝ) :
    Scalar.variationalValue (Scalar.xiSlice k m) h =
      Scalar.fourParameterValue (Scalar.xiSlice k m) h := by
  let xi := Scalar.xiSlice k m
  let S : Set ℝ := {v | ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧ v = Scalar.parisiFunctional xi h p}
  let T : Set ℝ := {v | ∃ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q ∧
    v = Scalar.parisiFunctional xi h (Scalar.fourParameterProfile delta a b q)}
  have hSne : S.Nonempty := ⟨Scalar.parisiFunctional xi h (fun _ => 1),
    (fun _ => 1),Scalar.admissibleProfile_const zero_lt_one,rfl⟩
  have hTne : T.Nonempty := ⟨Scalar.parisiFunctional xi h (Scalar.fourParameterProfile 1 0 0 0),
    1,0,0,0,⟨by norm_num,by norm_num,by norm_num,by norm_num⟩,rfl⟩
  have hsub : T ⊆ S := by
    rintro v ⟨delta,a,b,q,hAd,rfl⟩
    exact ⟨_,VariationalProofs.fourParameterProfile_admissible delta a b q hAd,rfl⟩
  have hSbb : BddBelow S := by
    refine ⟨0,?_⟩
    rintro v ⟨p,hp,rfl⟩
    have H := JTProfileBoundsProofs.functional_coercive hp
      (JTProfileBoundsProofs.xiSlice_secondDeriv_continuous k (by omega) m).continuousOn h
      (fun t ht => JTProfileBoundsProofs.xiSlice_secondDeriv_nonneg k (by omega) hm ht)
      (JTProfileBoundsProofs.xiSlice_boundary_nonneg k hm h)
    exact (mul_nonneg (hp.2.2.2 0 (by norm_num)).le
      (JTProfileBoundsProofs.xiSlice_coercivityConstant_pos k (by omega) hm).le).trans H
  have hTbb : BddBelow T := hSbb.mono hsub
  have Hinf : sInf S = sInf T := by
    apply le_antisymm
    · apply le_csInf hTne
      intro v hv
      exact csInf_le hSbb (hsub hv)
    · apply le_csInf hSne
      rintro v ⟨p,hp,rfl⟩
      obtain ⟨delta,a,b,q,hAd,hcost⟩ := fourParameter_cost_cofinal k hk hm h hp
      exact (csInf_le hTbb ⟨delta,a,b,q,hAd,rfl⟩).trans hcost
  exact congrArg (fun z : ℝ => (1/2 : ℝ)*z) Hinf

theorem fourParameterReduction (k : ℕ) (hk : 3 ≤ k) {m : ℝ} (hm : |m| < 1) :
    Scalar.FourParameterReduction k m :=
  xiSlice_variationalValue_eq_fourParameterValue k hk hm 0


end
end TensorPCA.FourParameterReductionProofs
