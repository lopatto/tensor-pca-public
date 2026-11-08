-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteJetTaylorPropagation

/-! Taylor propagation in the amplitude L1 norm. The amplitude law and its space may
depend on N. Conditional means remain inside the pointwise jet family; no pointwise
convergence in amplitudes is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteJetL1TaylorPropagation
open MeasureTheory ProbabilityTheory Filter Set
open GGFiniteJetTaylorPropagation
open scoped BigOperators Topology
noncomputable section

theorem integral_abs_taylor_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (J : X → ℕ → ℝ → ℝ)
    (hJ : ∀ a k t, HasDerivAt (J a k) (J a (k+1) t) t)
    (hMeas : ∀ k t, Measurable (fun a ↦ J a k t))
    {c x C A : ℝ} (hx : c≠x) (m : ℕ)
    (hb : ∀ a k y, y ∈ uIcc c x → |J a k y|≤C*A^k*(k.factorial : ℝ)) :
    (∫ a, |J a 0 x| ∂mu)≤
      (∑ i ∈ Finset.range (m+1), (|x-c|^i/(i.factorial : ℝ))*(∫ a, |J a i c| ∂mu))+
        C*(A*|x-c|)^(m+1) := by
  have hI (k : ℕ) (t : ℝ) (ht : t ∈ uIcc c x) : Integrable (fun a ↦ |J a k t|) mu := by
    apply Integrable.of_bound (continuous_abs.measurable.comp (hMeas k t)).aestronglyMeasurable
      (C*A^k*(k.factorial : ℝ))
    exact Eventually.of_forall (fun a ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,abs_abs] using hb a k t ht)
  let b : ℕ → ℝ := fun i ↦ |x-c|^i/(i.factorial : ℝ)
  let P : X → ℝ := fun a ↦ ∑ i ∈ Finset.range (m+1), b i*|J a i c|
  have hPi : Integrable P mu := integrable_finset_sum _
    (fun i _ ↦ (hI i c left_mem_uIcc).const_mul (b i))
  have hpoly (a : X) :
      |∑ i ∈ Finset.range (m+1), J a i c*(x-c)^i/(i.factorial : ℝ)|≤P a := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    dsimp only [b]
    rw [abs_div,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg i.factorial : (0 : ℝ) ≤ i.factorial)]
    apply le_of_eq
    ring
  have hpoint (a : X) : |J a 0 x|≤P a+C*(A*|x-c|)^(m+1) := by
    have hR := jet_taylor_abs_remainder (J a) (hJ a) hx m (hb a)
    have htri := abs_add_le
      (J a 0 x-(∑ i ∈ Finset.range (m+1), J a i c*(x-c)^i/(i.factorial : ℝ)))
      (∑ i ∈ Finset.range (m+1), J a i c*(x-c)^i/(i.factorial : ℝ))
    simp only [sub_add_cancel] at htri
    exact htri.trans (by linarith [hpoly a])
  have H := integral_mono (hI 0 x right_mem_uIcc) (hPi.add (integrable_const _)) hpoint
  change (∫ a, |J a 0 x| ∂mu)≤∫ a, P a+C*(A*|x-c|)^(m+1) ∂mu at H
  rw [integral_add hPi (integrable_const _),integral_const,probReal_univ,one_smul] at H
  have he : (∫ a, P a ∂mu)=∑ i ∈ Finset.range (m+1), b i*(∫ a, |J a i c| ∂mu) := by
    dsimp only [P]
    rw [integral_finsetSum _ (fun i _ ↦ (hI i c left_mem_uIcc).const_mul (b i))]
    simp_rw [integral_const_mul]
  simpa only [he,b] using H

theorem local_l1_tendsto_zero {X : ℕ → Type*} [∀ N, MeasurableSpace (X N)]
    (mu : ∀ N, Measure (X N)) [∀ N, IsProbabilityMeasure (mu N)]
    (J : (N : ℕ) → X N → ℕ → ℝ → ℝ)
    (hJ : ∀ N a k t, HasDerivAt (J N a k) (J N a (k+1) t) t)
    (hMeas : ∀ N k t, Measurable (fun a ↦ J N a k t))
    {c x C A : ℝ} (hA : 0≤A)
    (hb : ∀ N a k y, y ∈ uIcc c x → |J N a k y|≤C*A^k*(k.factorial : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ ∫ a, |J N a k c| ∂mu N) atTop (𝓝 0))
    (hsmall : A*|x-c|<1) :
    Tendsto (fun N ↦ ∫ a, |J N a 0 x| ∂mu N) atTop (𝓝 0) := by
  by_cases hx : c=x
  · simpa only [hx] using hzero 0
  let r : ℝ := A*|x-c|
  have hr0 : 0≤r := mul_nonneg hA (abs_nonneg _)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hsmall
  have hrem : Tendsto (fun m : ℕ ↦ C*r^(m+1)) atTop (𝓝 0) := by
    simpa only [pow_succ,mul_zero,zero_mul] using (hpow.mul_const r).const_mul C
  have hpoly (m : ℕ) : Tendsto
      (fun N ↦ ∑ i ∈ Finset.range (m+1), (|x-c|^i/(i.factorial : ℝ))*(∫ a, |J N a i c| ∂mu N)) atTop (𝓝 0) := by
    simpa only [mul_zero,Finset.sum_const_zero] using
      tendsto_finset_sum (Finset.range (m+1)) (fun i _ ↦ (hzero i).const_mul (|x-c|^i/(i.factorial : ℝ)))
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨m,hm⟩ := ((tendsto_order.1 hrem).2 (eps/2) (half_pos heps)).exists
  have hp := (tendsto_order.1 (hpoly m)).2 (eps/2) (half_pos heps)
  filter_upwards [hp] with N hN
  have hbound := integral_abs_taylor_bound (mu N) (J N) (hJ N) (hMeas N) hx m (hb N)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun a ↦ abs_nonneg _))]
  dsimp only [r] at hm
  linarith

theorem local_all_jets_l1_tendsto_zero {X : ℕ → Type*} [∀ N, MeasurableSpace (X N)]
    (mu : ∀ N, Measure (X N)) [∀ N, IsProbabilityMeasure (mu N)]
    (J : (N : ℕ) → X N → ℕ → ℝ → ℝ)
    (hJ : ∀ N a k t, HasDerivAt (J N a k) (J N a (k+1) t) t)
    (hMeas : ∀ N k t, Measurable (fun a ↦ J N a k t))
    (n : ℕ) {c x C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : ∀ N a k y, y ∈ uIcc c x → |J N a k y|≤C*A^k*((n+1).ascFactorial k : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ ∫ a, |J N a k c| ∂mu N) atTop (𝓝 0))
    (hsmall : (2*A)*|x-c|<1) :
    ∀ k, Tendsto (fun N ↦ ∫ a, |J N a k x| ∂mu N) atTop (𝓝 0) := by
  intro k
  have H := local_l1_tendsto_zero mu (J := fun N a i ↦ J N a (k+i))
    (fun N a i t ↦ by simpa only [Nat.add_assoc] using hJ N a (k+i) t)
    (fun N i t ↦ hMeas N (k+i) t) (mul_nonneg (by norm_num) hA)
    (fun N a i y hy ↦ shifted_factorial_bound (J N a) n k i hC hA (hb N a (k+i) y hy))
    (fun i ↦ hzero (k+i)) hsmall
  simpa only [Nat.add_zero] using H

theorem all_jets_l1_tendsto_zero_on_segment {X : ℕ → Type*} [∀ N, MeasurableSpace (X N)]
    (mu : ∀ N, Measure (X N)) [∀ N, IsProbabilityMeasure (mu N)]
    (J : (N : ℕ) → X N → ℕ → ℝ → ℝ)
    (hJ : ∀ N a k t, HasDerivAt (J N a k) (J N a (k+1) t) t)
    (hMeas : ∀ N k t, Measurable (fun a ↦ J N a k t))
    (n : ℕ) {c x C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : ∀ N a k y, y ∈ uIcc c x → |J N a k y|≤C*A^k*((n+1).ascFactorial k : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ ∫ a, |J N a k c| ∂mu N) atTop (𝓝 0)) :
    ∀ k, Tendsto (fun N ↦ ∫ a, |J N a k x| ∂mu N) atTop (𝓝 0) := by
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
  have hsteps (i : ℕ) : i≤M → ∀ k,
      Tendsto (fun N ↦ ∫ a, |J N a k (center i)| ∂mu N) atTop (𝓝 0) := by
    induction i with
    | zero => intro _; simpa only [hc0] using hzero
    | succ i ih =>
      intro hi
      have hi0 : i≤M := (Nat.le_succ i).trans hi
      exact local_all_jets_l1_tendsto_zero mu J hJ hMeas n hC hA
        (fun N a k y hy ↦ hb N a k y ((uIcc_subset_uIcc (hmem i hi0) (hmem (i+1) hi)) hy))
        (ih hi0) (hsmall i)
  simpa only [hcM] using hsteps M le_rfl

/-- Positive zero-jet L1 budgets suffice for value invariance in L1.
The subtracted zero-order value retains its own amplitude dependence. -/
theorem positive_jets_imply_l1_value_invariance {X : ℕ → Type*} [∀ N, MeasurableSpace (X N)]
    (mu : ∀ N, Measure (X N)) [∀ N, IsProbabilityMeasure (mu N)]
    (J : (N : ℕ) → X N → ℕ → ℝ → ℝ)
    (hJ : ∀ N a k t, HasDerivAt (J N a k) (J N a (k+1) t) t)
    (hMeas : ∀ N k t, Measurable (fun a ↦ J N a k t))
    (n : ℕ) {x C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hb : ∀ N a k y, y ∈ uIcc 0 x → |J N a k y|≤C*A^k*((n+1).ascFactorial k : ℝ))
    (hzero : ∀ k, Tendsto (fun N ↦ ∫ a, |J N a (k+1) 0| ∂mu N) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∫ a, |J N a 0 x-J N a 0 0| ∂mu N) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun N ↦ ∫ a, |J N a (k+1) x| ∂mu N) atTop (𝓝 0) := by
  let K : (N : ℕ) → X N → ℕ → ℝ → ℝ :=
    fun N a k y ↦ if k=0 then J N a 0 y-J N a 0 0 else J N a k y
  have hK : ∀ N a k t, HasDerivAt (K N a k) (K N a (k+1) t) t := by
    intro N a k t
    cases k with
    | zero => simpa [K] using (hJ N a 0 t).sub_const (J N a 0 0)
    | succ k => simpa only [K,if_false,Nat.succ_ne_zero] using hJ N a (k+1) t
  have hKM : ∀ N k t, Measurable (fun a ↦ K N a k t) := by
    intro N k t
    by_cases hk : k=0
    · subst k
      change Measurable (fun a ↦ J N a 0 t-J N a 0 0)
      convert (hMeas N 0 t).sub (hMeas N 0 0) using 1
    · simpa only [K,if_neg hk] using hMeas N k t
  have hKb : ∀ N a k y, y ∈ uIcc 0 x → |K N a k y|≤(2*C)*A^k*((n+1).ascFactorial k : ℝ) := by
    intro N a k y hy
    by_cases hk : k=0
    · subst k
      simp only [K,if_pos rfl,pow_zero,Nat.ascFactorial_zero,Nat.cast_one,mul_one]
      have hyb := hb N a 0 y hy
      have h0b := hb N a 0 0 left_mem_uIcc
      simp only [pow_zero,Nat.ascFactorial_zero,Nat.cast_one,mul_one] at hyb h0b
      exact (abs_sub _ _).trans (by linarith)
    · simp only [K,if_neg hk]
      exact (hb N a k y hy).trans (by gcongr; linarith)
  have hK0 : ∀ k, Tendsto (fun N ↦ ∫ a, |K N a k 0| ∂mu N) atTop (𝓝 0) := by
    intro k
    cases k with
    | zero => simpa only [K,if_pos rfl,sub_self,abs_zero,integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
    | succ k => simpa only [K,if_false,Nat.succ_ne_zero] using hzero k
  have H := all_jets_l1_tendsto_zero_on_segment mu K hK hKM n (mul_nonneg (by norm_num) hC) hA hKb hK0
  constructor
  · simpa only [K,if_pos rfl] using H 0
  · intro k
    simpa only [K,if_false,Nat.succ_ne_zero] using H (k+1)


end
end TensorPCA.NonRSLowerProofs.GGFiniteJetL1TaylorPropagation
