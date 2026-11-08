-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedLogSeries

/-! A single finite analytic budget for both clipped cavity marks. The cutoffs and
finite moment order/tolerance are chosen before every hierarchy. This is scalar
error selection, not a physical moment identity.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteMarkedCavityAnalyticBudget
open BoundedMarkedLogSeries
noncomputable section

theorem log_tail_mono {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b<1) (n : ℕ) :
    a^(n+1)/(1-a)≤b^(n+1)/(1-b) :=
  div_le_div₀ (pow_nonneg (ha.trans hab) _) (pow_le_pow_left₀ ha hab _) (sub_pos.mpr hb) (by linarith)

theorem exists_joint_budget (M : ℕ) (YN YC : ℝ) {error : ℝ} (he : 0<error) :
    ∃ LN b cap : ℝ,1≤LN ∧ 0<b ∧ b≤1 ∧ 1≤cap ∧ ∃ n : ℕ,∃ delta : ℝ,0<delta ∧
      let a := max (1-1/LN) (1-b/cap)
      0≤a ∧ a<1 ∧
      Real.exp (2*(M : ℝ)*YN)/LN+
        (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*YC)+
        (2*Real.exp (9*((M : ℝ)*YC)/2)/cap+2*b*Real.exp (2*((M : ℝ)*YC)))+
        2*(2*(a^(n+1)/(1-a))+(n : ℝ)*delta)≤error := by
  let A := Real.exp (2*(M : ℝ)*YN)
  let C := Real.exp (3/2*(M : ℝ)*YC)
  let U := C+2*Real.exp (9*((M : ℝ)*YC)/2)
  let V := C+2*Real.exp (2*((M : ℝ)*YC))
  have hA : 0<A := Real.exp_pos _
  have hC : 0<C := Real.exp_pos _
  have hU : 0<U := add_pos hC (mul_pos (by norm_num) (Real.exp_pos _))
  have hV : 0<V := add_pos hC (mul_pos (by norm_num) (Real.exp_pos _))
  let LN := 1+4*A/error
  let cap := 1+8*U/error
  let b := min 1 (error/(8*V))
  have hLN : 1≤LN := by dsimp [LN]; linarith [div_pos (mul_pos (by norm_num : (0 : ℝ)<4) hA) he]
  have hc : 1≤cap := by dsimp [cap]; linarith [div_pos (mul_pos (by norm_num : (0 : ℝ)<8) hU) he]
  have hb : 0<b := lt_min zero_lt_one (div_pos he (mul_pos (by norm_num) hV))
  have hb1 : b≤1 := min_le_left _ _
  have hLN0 : 0<LN := zero_lt_one.trans_le hLN
  have hc0 : 0<cap := zero_lt_one.trans_le hc
  have hAN : A/LN≤error/4 := by
    rw [div_le_iff₀ hLN0]
    dsimp [LN]
    field_simp
    nlinarith
  have hUC : U/cap≤error/8 := by
    rw [div_le_iff₀ hc0]
    dsimp [cap]
    field_simp
    nlinarith
  have hVB : b*V≤error/8 := by
    have H := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (error/(8*V))) hV.le
    change b*V≤_ at H
    convert H using 1 <;> field_simp <;> ring
  let a := max (1-1/LN) (1-b/cap)
  have ha : 0≤a := (sub_nonneg.mpr ((div_le_one hLN0).mpr hLN)).trans (le_max_left _ _)
  have ha1 : a<1 := max_lt
    (by linarith [div_pos (by norm_num : (0 : ℝ)<1) hLN0]) (by linarith [div_pos hb hc0])
  obtain ⟨n,delta,hd,hApprox⟩ := exists_log_approximation_parameters ha ha1 (show 0<error/4 by positivity)
  refine ⟨LN,b,cap,hLN,hb,hb1,hc,n,delta,hd,ha,ha1,?_⟩
  have HE : (b+cap⁻¹)*C+(2*Real.exp (9*((M : ℝ)*YC)/2)/cap+2*b*Real.exp (2*((M : ℝ)*YC)))=
      U/cap+b*V := by dsimp [U,V]; ring
  change A/LN+(b+cap⁻¹)*C+(2*Real.exp (9*((M : ℝ)*YC)/2)/cap+2*b*Real.exp (2*((M : ℝ)*YC)))+
    2*(2*(a^(n+1)/(1-a))+(n : ℝ)*delta)≤error
  rw [add_assoc (A/LN),HE]
  linarith

end
end TensorPCA.NonRSLowerProofs.FiniteMarkedCavityAnalyticBudget
