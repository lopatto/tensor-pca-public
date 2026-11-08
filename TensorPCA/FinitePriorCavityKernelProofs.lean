-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityBoundProofs
public import TensorPCA.PosteriorPairProofs

/-! Finite cavity and normalization-correction kernels. Every error
comes from a proved finite coefficient identity or the ordered-tuple collision
estimate; no Taylor remainder or asymptotic kernel hypothesis is supplied. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityKernelProofs
open Set FinitePriorCavityFieldProofs FinitePriorCavityNormalizationProofs
open FinitePriorCavityBoundProofs TensorOverlapKernelProofs TensorOrbitCountProofs
open TensorOrbitAggregationProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem ratio_pow_gap_le {x : ℝ} (hx : 0 < x) (r : ℕ) :
    0 ≤ 1-(x/(x+1))^r ∧ 1-(x/(x+1))^r ≤ (r : ℝ)/x := by
  have hv0 : 0 ≤ x/(x+1) := by positivity
  have hv1 : x/(x+1) ≤ 1 := (div_le_one (by linarith : 0 < x+1)).mpr (by linarith)
  have H := abs_pow_sub_pow_le (a := (1 : ℝ)) (b := x/(x+1)) (n := r)
  simp only [one_pow,abs_of_nonneg hv0,abs_one,max_eq_left hv1,one_pow,mul_one] at H
  have hgap : 0 ≤ 1-x/(x+1) := sub_nonneg.mpr hv1
  have hp : 0 ≤ 1-(x/(x+1))^r := sub_nonneg.mpr (pow_le_one₀ hv0 hv1)
  refine ⟨hp,?_⟩
  rw [abs_of_nonneg hp,abs_of_nonneg hgap] at H
  have hden : 1-x/(x+1) = 1/(x+1) := by field_simp; ring
  rw [hden] at H
  apply H.trans
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg r) hx (by linarith)

theorem normalization_gap_bounds {x : ℝ} (hx : 0 < x) (r : ℕ) :
    0 ≤ x*(1-(x/(x+1))^r) ∧ x*(1-(x/(x+1))^r) ≤ (r : ℝ) ∧
      |x*(1-(x/(x+1))^r)-(r : ℝ)| ≤ (r : ℝ)^2/x := by
  have hv0 : 0 ≤ x/(x+1) := by positivity
  have hv1 : x/(x+1) ≤ 1 := (div_le_one (by linarith : 0 < x+1)).mpr (by linarith)
  have hE : ∀ n : ℕ, 0 ≤ (n : ℝ)-x*(1-(x/(x+1))^n) ∧
      (n : ℝ)-x*(1-(x/(x+1))^n) ≤ (n : ℝ)^2/x := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hrec : ((n+1 : ℕ) : ℝ)-x*(1-(x/(x+1))^(n+1)) =
          (x/(x+1))*((n : ℝ)-x*(1-(x/(x+1))^n))+((n : ℝ)+1)/(x+1) := by
        rw [Nat.cast_add,Nat.cast_one,pow_succ]
        field_simp
        ring
      rw [hrec]
      refine ⟨add_nonneg (mul_nonneg hv0 ih.1) (by positivity),?_⟩
      calc
        _ ≤ ((n : ℝ)-x*(1-(x/(x+1))^n))+((n : ℝ)+1)/x := add_le_add
          (mul_le_of_le_one_left ih.1 hv1)
          (div_le_div_of_nonneg_left (by positivity) hx (by linarith))
        _ ≤ (n : ℝ)^2/x+((n : ℝ)+1)/x := add_le_add ih.2 le_rfl
        _ ≤ (((n+1 : ℕ) : ℝ))^2/x := by
          rw [← add_div]
          apply div_le_div_of_nonneg_right _ hx.le
          simp only [Nat.cast_add,Nat.cast_one]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨mul_nonneg hx.le (ratio_pow_gap_le hx r).1,by linarith [(hE r).1],?_⟩
  rw [abs_sub_comm,abs_of_nonneg (hE r).1]
  exact (hE r).2

variable {S : Type*}

theorem overlap_abs_le {N : ℕ} (hN : 0 < N) (a : S → ℝ) (x y : Fin N → S)
    {K : ℝ} (hK : 0 ≤ K) (hx : ∀ i, |a (x i)| ≤ K) (hy : ∀ i, |a (y i)| ≤ K) :
    |PosteriorPairProofs.overlap a (x,y)| ≤ K^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold PosteriorPairProofs.overlap
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ i, a (x i)*a (y i)| ≤ ∑ i, |a (x i)*a (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, K^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hx i) (hy i) (abs_nonneg _) hK)
    _ = K^2*(N : ℝ) := by simp; ring

theorem cavitySignal_inner_normalized {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (a : S → ℝ) (x y : Fin N → S) :
    inner ℝ (cavitySignal a N k gamma x) (cavitySignal a N k gamma y) =
      (k : ℝ)*gamma*((N : ℝ)/((N : ℝ)+1))^(k-1)*
        (((Nat.factorial (k-1) : ℝ)*(∑ T : KSubset N (k-1), ∏ i ∈ T.1, a (x i)*a (y i)))/(N : ℝ)^(k-1)) := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hf : (Nat.factorial k : ℝ) = (k : ℝ)*(Nat.factorial (k-1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred hk.ne').symm
  let _ : MeasurableSpace S := ⊥
  rw [cavitySignal_inner,aggregateCoefficient_sq (Nat.succ_pos N) hk hgamma,hf]
  simp only [Nat.cast_succ,div_pow]
  field_simp [hn]

theorem correctionSignal_inner (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x y : Fin N → S) :
    inner ℝ (correctionSignal a N k gamma x) (correctionSignal a N k gamma y) =
      (correctionCoefficient N k gamma)^2*
        ∑ T : KSubset N k, ∏ i ∈ T.1, a (x i)*a (y i) := by
  rw [correctionSignal,correctionSignal,real_inner_smul_left,real_inner_smul_right,
    monomialSignal,monomialSignal,EuclideanSpace.inner_toLp_toLp]
  change _*( _*(∑ T : KSubset N k, (∏ i ∈ T.1, a (y i))*(∏ i ∈ T.1, a (x i)))) = _
  rw [← mul_assoc,← pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib]
  ring

theorem correctionSignal_inner_normalized {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (a : S → ℝ) (x y : Fin N → S) :
    inner ℝ (correctionSignal a N k gamma x) (correctionSignal a N k gamma y) =
      gamma*((N : ℝ)*(1-((N : ℝ)/((N : ℝ)+1))^(k-1)))*
        (((Nat.factorial k : ℝ)*(∑ T : KSubset N k, ∏ i ∈ T.1, a (x i)*a (y i)))/(N : ℝ)^k) := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hn1 : (N : ℝ)+1 ≠ 0 := by positivity
  have hkpow : (N : ℝ)^k = (N : ℝ)*(N : ℝ)^(k-1) := by
    rw [← pow_succ']; congr 1; omega
  rw [correctionSignal_inner,correctionCoefficient_variance hN hk hgamma]
  simp only [Nat.cast_add,Nat.cast_one,div_pow]
  rw [hkpow]
  field_simp [hn,hn1]

theorem cavitySignal_covariance_error_le {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (a : S → ℝ) (x y : Fin N → S)
    (hx : ∀ i, |a (x i)| ≤ K) (hy : ∀ i, |a (y i)| ≤ K) :
    |inner ℝ (cavitySignal a N k gamma x) (cavitySignal a N k gamma y)-
      (k : ℝ)*gamma*(PosteriorPairProofs.overlap a (x,y))^(k-1)| ≤
        gamma*(k : ℝ)*(((k-1 : ℕ) : ℝ)^2+((k-1 : ℕ) : ℝ))*K^(2*(k-1))/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let r := k-1
  let v := (N : ℝ)/((N : ℝ)+1)
  let D := ((Nat.factorial r : ℝ)*(∑ T : KSubset N r, ∏ i ∈ T.1, a (x i)*a (y i)))/(N : ℝ)^r
  let R := PosteriorPairProofs.overlap a (x,y)
  let c := (k : ℝ)*gamma
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg k) hgamma
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    exact (div_le_one (by positivity : 0 < (N : ℝ)+1)).mpr (by linarith)
  have hpow0 := pow_nonneg hv0 r
  have hpow1 := pow_le_one₀ hv0 hv1 (n := r)
  have hgap : |v^r-1| ≤ (r : ℝ)/(N : ℝ) := by
    rw [abs_sub_comm,abs_of_nonneg (ratio_pow_gap_le hn r).1]
    exact (ratio_pow_gap_le hn r).2
  have hD : |D-R^r| ≤ (r : ℝ)^2*K^(2*r)/(N : ℝ) := by
    simpa only [D,R,PosteriorPairProofs.overlap] using
      abs_normalized_covariance_kernel_error_le (k := r) hN (by dsimp [r]; omega)
        (fun i => a (x i)) (fun i => a (y i)) hK hx hy
  have hR : |R^r| ≤ K^(2*r) := by
    rw [abs_pow]
    simpa only [← pow_mul] using pow_le_pow_left₀ (abs_nonneg R) (overlap_abs_le hN a x y hK hx hy) r
  rw [cavitySignal_inner_normalized hN (by omega) hgamma]
  change |c*v^r*D-c*R^r| ≤ _
  calc
    _ = |c*v^r*(D-R^r)+c*(v^r-1)*R^r| := congrArg abs (by ring)
    _ ≤ |c*v^r*(D-R^r)|+|c*(v^r-1)*R^r| := abs_add_le _ _
    _ = c*(v^r*|D-R^r|+|v^r-1| * |R^r|) := by
      simp only [abs_mul,abs_of_nonneg hc,abs_of_nonneg hpow0]
      ring
    _ ≤ c*((r : ℝ)^2*K^(2*r)/(N : ℝ)+((r : ℝ)/(N : ℝ))*K^(2*r)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply add_le_add
      · exact (mul_le_of_le_one_left (abs_nonneg (D-R^r)) hpow1).trans hD
      · exact mul_le_mul hgap hR (abs_nonneg _) (div_nonneg (Nat.cast_nonneg r) hn.le)
    _ = _ := by dsimp [c,r]; ring

theorem correctionSignal_covariance_error_le {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (a : S → ℝ) (x y : Fin N → S)
    (hx : ∀ i, |a (x i)| ≤ K) (hy : ∀ i, |a (y i)| ≤ K) :
    |inner ℝ (correctionSignal a N k gamma x) (correctionSignal a N k gamma y)-
      ((k-1 : ℕ) : ℝ)*gamma*(PosteriorPairProofs.overlap a (x,y))^k| ≤
        gamma*(((k-1 : ℕ) : ℝ)*(k : ℝ)^2+((k-1 : ℕ) : ℝ)^2)*K^(2*k)/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let r := k-1
  let F := (N : ℝ)*(1-((N : ℝ)/((N : ℝ)+1))^r)
  let D := ((Nat.factorial k : ℝ)*(∑ T : KSubset N k, ∏ i ∈ T.1, a (x i)*a (y i)))/(N : ℝ)^k
  let R := PosteriorPairProofs.overlap a (x,y)
  obtain ⟨hF0,hFle,hFerr⟩ := normalization_gap_bounds hn r
  change 0 ≤ F at hF0
  change F ≤ (r : ℝ) at hFle
  change |F-(r : ℝ)| ≤ (r : ℝ)^2/(N : ℝ) at hFerr
  have hD : |D-R^k| ≤ (k : ℝ)^2*K^(2*k)/(N : ℝ) := by
    simpa only [D,R,PosteriorPairProofs.overlap] using
      abs_normalized_covariance_kernel_error_le (k := k) hN (by omega)
        (fun i => a (x i)) (fun i => a (y i)) hK hx hy
  have hR : |R^k| ≤ K^(2*k) := by
    rw [abs_pow]
    simpa only [← pow_mul] using pow_le_pow_left₀ (abs_nonneg R) (overlap_abs_le hN a x y hK hx hy) k
  rw [correctionSignal_inner_normalized hN (by omega) hgamma]
  change |gamma*F*D-(r : ℝ)*gamma*R^k| ≤ _
  calc
    _ = |gamma*F*(D-R^k)+gamma*(F-(r : ℝ))*R^k| := congrArg abs (by ring)
    _ ≤ |gamma*F*(D-R^k)|+|gamma*(F-(r : ℝ))*R^k| := abs_add_le _ _
    _ = gamma*(F*|D-R^k|+|F-(r : ℝ)| * |R^k|) := by
      simp only [abs_mul,abs_of_nonneg hgamma,abs_of_nonneg hF0]
      ring
    _ ≤ gamma*((r : ℝ)*((k : ℝ)^2*K^(2*k)/(N : ℝ))+((r : ℝ)^2/(N : ℝ))*K^(2*k)) := by
      apply mul_le_mul_of_nonneg_left _ hgamma
      apply add_le_add
      · exact mul_le_mul hFle hD (abs_nonneg _) (Nat.cast_nonneg r)
      · exact mul_le_mul hFerr hR (abs_nonneg _) (div_nonneg (sq_nonneg _) hn.le)
    _ = _ := by dsimp [r]; ring


end
end TensorPCA.FinitePriorCavityKernelProofs
