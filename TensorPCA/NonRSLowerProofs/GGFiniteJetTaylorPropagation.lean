-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteReweightingJets
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Bounds

/-! Real Taylor propagation for derivative chains, with the family and its bounds
explicit.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteJetTaylorPropagation
open Filter Set
open scoped BigOperators Topology
noncomputable section

theorem iteratedDeriv_eq_jet (J : ℕ → ℝ → ℝ)
    (hJ : ∀ k t, HasDerivAt (J k) (J (k+1) t) t) (k : ℕ) :
    iteratedDeriv k (J 0)=J k := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact (hJ k t).deriv

theorem jet_contDiff (J : ℕ → ℝ → ℝ)
    (hJ : ∀ k t, HasDerivAt (J k) (J (k+1) t) t) (m : ℕ) : ContDiff ℝ m (J 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  rw [iteratedDeriv_eq_jet J hJ k]
  exact fun t ↦ (hJ k t).differentiableAt

theorem jet_taylor_remainder (J : ℕ → ℝ → ℝ)
    (hJ : ∀ k t, HasDerivAt (J k) (J (k+1) t) t)
    {c x : ℝ} (hx : c≠x) (m : ℕ) :
    ∃ y ∈ uIoo c x, J 0 x-(∑ i ∈ Finset.range (m+1), J i c*(x-c)^i/(i.factorial : ℝ))=
      J (m+1) y*(x-c)^(m+1)/((m+1).factorial : ℝ) := by
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx (jet_contDiff J hJ (m+1)).contDiffOn
  refine ⟨y,hy,?_⟩
  rw [iteratedDeriv_eq_jet J hJ] at he
  convert he using 1
  rw [taylor_within_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
    (jet_contDiff J hJ i).contDiffAt (left_mem_uIcc),iteratedDeriv_eq_jet J hJ]
  simp only [smul_eq_mul]
  ring

theorem jet_taylor_abs_remainder (J : ℕ → ℝ → ℝ)
    (hJ : ∀ k t, HasDerivAt (J k) (J (k+1) t) t)
    {c x C A : ℝ} (hx : c≠x) (m : ℕ)
    (hb : ∀ k y, y ∈ uIcc c x → |J k y|≤C*A^k*(k.factorial : ℝ)) :
    |J 0 x-(∑ i ∈ Finset.range (m+1), J i c*(x-c)^i/(i.factorial : ℝ))|≤
      C*(A*|x-c|)^(m+1) := by
  obtain ⟨y,hy,he⟩ := jet_taylor_remainder J hJ hx m
  rw [he,abs_div,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg ((m+1).factorial) : (0 : ℝ)≤(m+1).factorial)]
  have hfac : (0 : ℝ)<(m+1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  calc
    _ ≤ ((C*A^(m+1)*((m+1).factorial : ℝ))*|x-c|^(m+1))/((m+1).factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hb (m+1) y ⟨hy.1.le,hy.2.le⟩) (pow_nonneg (abs_nonneg _) _)) hfac.le
    _ = _ := by rw [mul_pow]; field_simp [hfac.ne']

/-- Uniform factorial derivative control lets every fixed Taylor
coefficient tend to zero before sending the Taylor order to infinity. -/
theorem local_tendsto_zero (J : ℕ → ℕ → ℝ → ℝ)
    (hJ : ∀ N k t, HasDerivAt (J N k) (J N (k+1) t) t)
    {c x C A : ℝ} (hA : 0≤A)
    (hb : ∀ N k y, y ∈ uIcc c x → |J N k y|≤C*A^k*(k.factorial : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ J N k c) atTop (𝓝 0))
    (hsmall : A*|x-c|<1) : Tendsto (fun N ↦ J N 0 x) atTop (𝓝 0) := by
  by_cases hx : c=x
  · simpa only [hx] using hzero 0
  let r : ℝ := A*|x-c|
  have hr0 : 0≤r := mul_nonneg hA (abs_nonneg _)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hsmall
  have hrem : Tendsto (fun m : ℕ ↦ C*r^(m+1)) atTop (𝓝 0) := by
    simpa only [pow_succ,mul_zero,zero_mul] using (hpow.mul_const r).const_mul C
  have hpoly (m : ℕ) : Tendsto
      (fun N ↦ ∑ i ∈ Finset.range (m+1), J N i c*(x-c)^i/(i.factorial : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_div,Finset.sum_const_zero] using
      (tendsto_finset_sum (Finset.range (m+1)) (fun i _ ↦ ((hzero i).mul_const ((x-c)^i)).div_const (i.factorial : ℝ)))
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨m,hm⟩ := ((tendsto_order.1 hrem).2 (eps/2) (half_pos heps)).exists
  have hp := (Metric.tendsto_nhds.1 (hpoly m)) (eps/2) (half_pos heps)
  filter_upwards [hp] with N hN
  have hpabs : |∑ i ∈ Finset.range (m+1), J N i c*(x-c)^i/(i.factorial : ℝ)|<eps/2 := by
    simpa only [Real.dist_eq,sub_zero] using hN
  have hbound := jet_taylor_abs_remainder (J N) (hJ N) hx m (hb N)
  have htri := abs_add_le
    (J N 0 x-(∑ i ∈ Finset.range (m+1), J N i c*(x-c)^i/(i.factorial : ℝ)))
    (∑ i ∈ Finset.range (m+1), J N i c*(x-c)^i/(i.factorial : ℝ))
  simp only [sub_add_cancel] at htri
  rw [Real.dist_eq,sub_zero]
  exact lt_of_le_of_lt htri (by dsimp only [r] at hm; linarith)

theorem shifted_factorial_bound (J : ℕ → ℝ → ℝ) (n j k : ℕ)
    {C A y : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : |J (j+k) y|≤C*A^(j+k)*((n+1).ascFactorial (j+k) : ℝ)) :
    |J (j+k) y|≤
      (C*A^j*((n+1).ascFactorial j : ℝ)*(2 : ℝ)^(n+j))*(2*A)^k*(k.factorial : ℝ) := by
  have hf : (n+1+j).ascFactorial k≤k.factorial*2^(n+j+k) := by
    rw [show n+1+j=(n+j)+1 by omega,Nat.ascFactorial_eq_factorial_mul_choose]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
  have hfR : ((n+1+j).ascFactorial k : ℝ)≤(k.factorial : ℝ)*(2 : ℝ)^(n+j+k) := by exact_mod_cast hf
  have hc : 0≤C*A^j*((n+1).ascFactorial j : ℝ) := by positivity
  calc
    _ ≤ (C*A^j*((n+1).ascFactorial j : ℝ))*((n+1+j).ascFactorial k : ℝ)*A^k := by
      convert hb using 1
      rw [← Nat.ascFactorial_mul_ascFactorial (n+1) j k,pow_add]
      push_cast
      ring
    _ ≤ (C*A^j*((n+1).ascFactorial j : ℝ))*((k.factorial : ℝ)*(2 : ℝ)^(n+j+k))*A^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfR hc) (pow_nonneg hA _)
    _ = _ := by rw [pow_add,mul_pow]; ring

/-- Every fixed derivative order propagates across the same small step.
Only the harmless prefactor depends on that fixed order. -/
theorem local_all_jets_tendsto_zero (J : ℕ → ℕ → ℝ → ℝ)
    (hJ : ∀ N k t, HasDerivAt (J N k) (J N (k+1) t) t)
    (n : ℕ) {c x C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : ∀ N k y, y ∈ uIcc c x → |J N k y|≤C*A^k*((n+1).ascFactorial k : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ J N k c) atTop (𝓝 0))
    (hsmall : (2*A)*|x-c|<1) : ∀ k, Tendsto (fun N ↦ J N k x) atTop (𝓝 0) := by
  intro k
  have H := local_tendsto_zero (J := fun N i ↦ J N (k+i))
    (fun N i t ↦ by simpa only [Nat.add_assoc] using hJ N (k+i) t)
    (mul_nonneg (by norm_num) hA)
    (fun N i y hy ↦ shifted_factorial_bound (J N) n k i hC hA (hb N (k+i) y hy))
    (fun i ↦ hzero (k+i)) hsmall
  simpa only [Nat.add_zero] using H

/-- Finitely many common short steps propagate every fixed jet over an
arbitrary fixed compact segment. -/
theorem all_jets_tendsto_zero_on_segment (J : ℕ → ℕ → ℝ → ℝ)
    (hJ : ∀ N k t, HasDerivAt (J N k) (J N (k+1) t) t)
    (n : ℕ) {c x C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : ∀ N k y, y ∈ uIcc c x → |J N k y|≤C*A^k*((n+1).ascFactorial k : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ J N k c) atTop (𝓝 0)) :
    ∀ k, Tendsto (fun N ↦ J N k x) atTop (𝓝 0) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (2*A*|x-c|+1)
  have hM0 : (0 : ℝ)<M := lt_trans (by positivity) hM
  have hMne : (M : ℝ)≠0 := hM0.ne'
  let center : ℕ → ℝ := fun i ↦ c+((i : ℝ)/(M : ℝ))*(x-c)
  have hc0 : center 0=c := by simp only [center,Nat.cast_zero,zero_div,zero_mul,add_zero]
  have hcM : center M=x := by simp only [center,div_self hMne,one_mul,add_sub_cancel]
  have hmem (i : ℕ) (hi : i≤M) : center i ∈ uIcc c x := by
    have hiR : (i : ℝ)≤M := Nat.cast_le.mpr hi
    have hr0 : (0 : ℝ)≤(i : ℝ)/(M : ℝ) := div_nonneg (Nat.cast_nonneg _) hM0.le
    have hr1 : (i : ℝ)/(M : ℝ)≤1 := (div_le_one hM0).mpr hiR
    rcases le_total c x with hcx|hxc
    · rw [uIcc_of_le hcx]
      dsimp only [center]
      constructor <;> nlinarith
    · rw [uIcc_of_ge hxc]
      dsimp only [center]
      constructor <;> nlinarith
  have hsmall (i : ℕ) : (2*A)*|center (i+1)-center i|<1 := by
    have he : center (i+1)-center i=(x-c)/(M : ℝ) := by
      dsimp only [center]
      push_cast
      ring
    calc
      _ = (2*A*|x-c|)/(M : ℝ) := by rw [he,abs_div,abs_of_pos hM0]; ring
      _ < 1 := (div_lt_one hM0).mpr (by linarith)
  have hsteps (i : ℕ) : i≤M → ∀ k, Tendsto (fun N ↦ J N k (center i)) atTop (𝓝 0) := by
    induction i with
    | zero => intro _; simpa only [hc0] using hzero
    | succ i ih =>
      intro hi
      have hi0 : i≤M := (Nat.le_succ i).trans hi
      exact local_all_jets_tendsto_zero J hJ n hC hA
        (fun N k y hy ↦ hb N k y ((uIcc_subset_uIcc (hmem i hi0) (hmem (i+1) hi)) hy))
        (ih hi0) (hsmall i)
  simpa only [hcM] using hsteps M le_rfl

/-- The original value at zero is arbitrary. Vanishing of positive jets
forces the value difference and all positive jets at a fixed point to vanish. -/
theorem positive_jets_imply_value_invariance (J : ℕ → ℕ → ℝ → ℝ)
    (hJ : ∀ N k t, HasDerivAt (J N k) (J N (k+1) t) t)
    (n : ℕ) {x C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : ∀ N k y, y ∈ uIcc 0 x → |J N k y|≤C*A^k*((n+1).ascFactorial k : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ J N (k+1) 0) atTop (𝓝 0)) :
    Tendsto (fun N ↦ J N 0 x-J N 0 0) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun N ↦ J N (k+1) x) atTop (𝓝 0) := by
  let K : ℕ → ℕ → ℝ → ℝ := fun N k y ↦ if k=0 then J N 0 y-J N 0 0 else J N k y
  have hK : ∀ N k t, HasDerivAt (K N k) (K N (k+1) t) t := by
    intro N k t
    cases k with
    | zero => simpa [K] using (hJ N 0 t).sub_const (J N 0 0)
    | succ k => simpa only [K,if_false,Nat.succ_ne_zero] using hJ N (k+1) t
  have hKb : ∀ N k y, y ∈ uIcc 0 x → |K N k y|≤(2*C)*A^k*((n+1).ascFactorial k : ℝ) := by
    intro N k y hy
    by_cases hk : k=0
    · subst k
      simp only [K,if_pos rfl,pow_zero,Nat.ascFactorial_zero,Nat.cast_one,mul_one]
      have hyb := hb N 0 y hy
      have h0b := hb N 0 0 left_mem_uIcc
      simp only [pow_zero,Nat.ascFactorial_zero,Nat.cast_one,mul_one] at hyb h0b
      exact (abs_sub _ _).trans (by linarith)
    · simp only [K,if_neg hk]
      exact (hb N k y hy).trans (by gcongr; linarith)
  have hK0 : ∀ k, Tendsto (fun N ↦ K N k 0) atTop (𝓝 0) := by
    intro k
    cases k with
    | zero => simpa only [K,if_pos rfl,sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
    | succ k => simpa only [K,if_false,Nat.succ_ne_zero] using hzero k
  have H := all_jets_tendsto_zero_on_segment K hK n (mul_nonneg (by norm_num) hC) hA hKb hK0
  constructor
  · simpa only [K,if_pos rfl] using H 0
  · intro k
    simpa only [K,if_false,Nat.succ_ne_zero] using H (k+1)


end
end TensorPCA.NonRSLowerProofs.GGFiniteJetTaylorPropagation
