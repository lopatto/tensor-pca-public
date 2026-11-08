-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.ReplicaMeshProofs
public import TensorPCA.CoupledQuadraticProofs
public import TensorPCA.NullGronwallProofs
public import TensorPCA.NullVarianceProofs

/-! Uniform finite replica bounds and the quantitative mean-gap reduction.
The coupled interpolation theorem remains an explicit prerequisite. -/

@[expose] public section
namespace TensorPCA.ReplicaRateProofs
open MeasureTheory ProbabilityTheory Set Filter ReplicaMeshProofs ThermalReplicaProofs
open scoped Topology RealInnerProductSpace ENNReal BigOperators
noncomputable section

/-- Uniform concentration includes zero strength by bounding the actual
Lipschitz constant by a fixed positive strength budget. -/
theorem windowLogProbability_gaussian_tail_uniform {N k : ℕ} (hN : 0 < N)
    (lam u eta : ℝ) (hm : Coupled.windowMass N u eta ≠ 0)
    {B : ℝ} (hB : 0 < B) (hlam : |lam| ≤ B) (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w |
      |(Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w)-
        (Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam)| > t} ≤
      ENNReal.ofReal (2*Real.exp (-(N : ℝ)*t^2/(32*B^2))) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hLip := (windowLogProbability_lipschitz (k := k) hN lam u eta hm).weaken
    (Real.toNNReal_mono (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlam (by norm_num : (0 : ℝ) ≤ 4)) hs.le))
  have hL : 0 < 4*B/Real.sqrt N := div_pos (mul_pos (by norm_num) hB) hs
  have hb := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (fun w : Model.Tensor N k ↦ Real.log (Coupled.pairPartition N k lam u eta w)/N-
      2*Model.freeEnergy N k lam w) (4*B/Real.sqrt N) t hL ht hLip
  have hMean := integral_windowLogProbability (k := k) hN lam u eta hm
  change (∫ w, Real.log (Coupled.pairPartition N k lam u eta w)/N-
    2*Model.freeEnergy N k lam w ∂stdGaussian (Model.Tensor N k)) = _ at hMean
  have he : -t^2/(2*(4*B/Real.sqrt N)^2) = -(N : ℝ)*t^2/(32*B^2) := by
    rw [div_pow, mul_pow]
    field_simp [hs.ne', hB.ne']
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  rw [hMean, he] at hb
  exact hb

/-- A finite deterministic pair mean gap gives a window bound uniform in all
strengths in the chosen positive budget. -/
theorem expected_windowProbability_le_uniform {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) {B b : ℝ}
    (hB : 0 < B) (hlam : |lam| ≤ B) (hb : 0 < b)
    (hgap : Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam ≤ -2*b) :
    (∫ w, windowProbability N k lam u eta w ∂Model.noiseLaw N k) ≤
      Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*B^2)) := by
  have hsub : {w : Model.Tensor N k | Real.exp (-(N : ℝ)*b) < windowProbability N k lam u eta w} ⊆
      {w | |(Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w)-
        (Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam)| > b} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [windowProbability_eq_exp hN lam u eta hm, Real.exp_lt_exp] at hw
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hr : -b < Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w := by
      apply (mul_lt_mul_iff_right₀ hn).mp
      simpa only [mul_neg, neg_mul] using hw
    exact (by linarith : b < (Real.log (Coupled.pairPartition N k lam u eta w)/N-
      2*Model.freeEnergy N k lam w)-(Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam)).trans_le
        (le_abs_self _)
  have htail := (measure_mono hsub).trans (windowLogProbability_gaussian_tail_uniform hN lam u eta hm hB hlam b hb)
  have htailReal : (Model.noiseLaw N k).real
      {w | Real.exp (-(N : ℝ)*b) < windowProbability N k lam u eta w} ≤
      2*Real.exp (-(N : ℝ)*b^2/(32*B^2)) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mp htail
  exact (integral_le_threshold_add_tail (Model.noiseLaw N k)
    (windowProbability N k lam u eta) (windowProbability_continuous hN lam u eta hm).measurable
    (windowProbability_nonneg N k lam u eta) (windowProbability_le_one hN lam u eta)
    (Real.exp_pos _).le).trans (add_le_add (le_refl _) htailReal)

/-- Uniform finite-mesh averaging, including every strength in the budget. -/
theorem replicaMean_le_of_mesh_gaps_uniform {N r : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    {B v b : ℝ} (hB : 0 < B) (hlam : |lam| ≤ B)
    (hv : v ∈ Icc (0 : ℝ) 1) (hb : 0 < b)
    (hgap : ∀ i : Fin (N+1),
      Coupled.meanPairFreeEnergy N (2*r) lam (overlapCenter N (Real.sqrt v) i) (1/(N : ℝ))-
        2*Coupled.meanNullFE N (2*r) lam ≤ -2*b) :
    replicaMean N (2*r) lam ≤ v^r+(N+1 : ℕ)*
      (Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*B^2))) := by
  classical
  have hNp : 0 < N := by omega
  obtain ⟨_, hc, hcover⟩ := overlap_mesh hNp hv
  have hm (i : Fin (N+1)) :
      Coupled.windowMass N (overlapCenter N (Real.sqrt v) i) (1/(N : ℝ)) ≠ 0 :=
    (WindowMassProofs.positiveWindowMass N hN _ (hc i).1 _
      (one_div_pos.mpr (Nat.cast_pos.mpr hNp))).ne'
  apply (replicaMean_le_cover hNp lam (overlapCenter N (Real.sqrt v)) (1/(N : ℝ)) hv.1 hm hcover).trans
  apply add_le_add (le_refl _)
  calc
    _ ≤ ∑ i : Fin (N+1), (Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*B^2))) :=
      Finset.sum_le_sum (fun i _ ↦ expected_windowProbability_le_uniform hNp lam _ _ (hm i) hB hlam hb (hgap i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A finite actual quadratic pair-mean gap yields the replica cover bound.
The cutoff condition is on sqrt(v), exactly as required by the mesh. -/
theorem replicaMean_le_of_quadratic_gap {N r : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    {B v b a c : ℝ} (hB : 0 < B) (hlam : |lam| ≤ B)
    (hv : 0 ≤ v) (hb : 0 < b) (hc : 0 ≤ c)
    (hcut : a^2 ≤ v)
    (hbudget : 2*freeEnergyGap N (2*r) lam+2*b ≤ c*v)
    (hquad : ∀ u ∈ Icc a 1, Coupled.meanPairFreeEnergy N (2*r) lam u (1/(N : ℝ)) ≤ lam^2-c*u^2) :
    replicaMean N (2*r) lam ≤ v^r+(N+1 : ℕ)*
      (Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*B^2))) := by
  by_cases hv1 : v ≤ 1
  · apply replicaMean_le_of_mesh_gaps_uniform hN lam hB hlam ⟨hv, hv1⟩ hb
    intro i
    have hcenter := (overlap_mesh (by omega : 0 < N) ⟨hv, hv1⟩).2.1 i
    have hca : a ≤ overlapCenter N (Real.sqrt v) i := by nlinarith [hcenter.1.1, hcenter.2]
    have hq := hquad _ ⟨hca, hcenter.1.2⟩
    have hmul := mul_le_mul_of_nonneg_left hcenter.2 hc
    unfold freeEnergyGap at hbudget
    linarith
  · have hp := one_le_pow₀ (le_of_not_ge hv1) (n := r)
    have hrem : 0 ≤ ((N+1 : ℕ) : ℝ)*
        (Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*B^2))) := by positivity
    exact (replicaMean_le_one (by omega : 0 < N) lam).trans (hp.trans (le_add_of_nonneg_right hrem))

/-- The accepted local and macroscopic trial reductions combine into the
actual real quadratic pair-mean gap, with one coefficient on the full interval. -/
theorem quadratic_mean_gap_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 4 ≤ k) (heven : Even k) {barLam delta : ℝ}
    (hbar : 0 ≤ barLam) (hsub : barLam < Scalar.lambdaC k)
    (hdelta : delta ∈ Ioo (0 : ℝ) (1/2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ lam ∈ Icc (0 : ℝ) barLam, ∀ N : ℕ, N0 ≤ N →
        ∀ u ∈ Icc ((N : ℝ)^((-1/2 : ℝ)+delta)) 1,
          Coupled.meanPairFreeEnergy N k lam u (1/(N : ℝ)) ≤ lam^2-c*u^2 := by
  obtain ⟨d, hd, N0, hN0, hsmall⟩ :=
    CoupledQuadraticProofs.small_overlap_gap_of_trialBound htrial k hk heven hbar hsub hdelta
  obtain ⟨gamma, C, hgamma, hC, hmacro⟩ :=
    CoupledMacroscopicProofs.macroscopic_gap_of_trialBound htrial k hk heven hbar hsub
      (show d ∈ Ioc (0 : ℝ) 1 from ⟨hd.1, by linarith [hd.2]⟩)
  have hrem : Tendsto (fun N : ℕ ↦ C*((1+Real.log ((N : ℝ)+1))/(N : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero] using
      (CoupledQuadraticProofs.logarithmic_remainder_tendsto (by norm_num : (0 : ℝ) < 1)).const_mul C
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hrem.eventually
    (Iio_mem_nhds (half_pos hgamma)))
  let c : ℝ := min (1/8) (gamma/2)
  have hc : 0 < c := lt_min (by norm_num) (half_pos hgamma)
  refine ⟨c, hc, max (max N0 N1) 2, le_max_right _ _, ?_⟩
  intro lam hlam N hN u hu
  have hN2 : 2 ≤ N := (le_max_right (max N0 N1) 2).trans hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  have hu0 : 0 ≤ u := (Real.rpow_pos_of_pos hNp _).le.trans hu.1
  have hmass : Coupled.windowMass N u (1/(N : ℝ)) ≠ 0 :=
    (WindowMassProofs.positiveWindowMass N hN2 u ⟨hu0, hu.2⟩ _ (one_div_pos.mpr hNp)).ne'
  have hreal : Coupled.expectedCoupledFreeEnergy N k lam u (1/(N : ℝ)) ≤
      ((lam^2-c*u^2 : ℝ) : EReal) := by
    by_cases hud : u < d
    · have hs := hsmall lam hlam N (by omega) u hu.1 hud
      apply hs.trans
      have hle : lam^2-u^2/8 ≤ lam^2-c*u^2 := by
        have hh := mul_le_mul_of_nonneg_right (min_le_left (1/8 : ℝ) (gamma/2)) (sq_nonneg u)
        change c*u^2 ≤ (1/8 : ℝ)*u^2 at hh
        linarith
      exact_mod_cast hle
    · have hm := hmacro lam hlam u ⟨le_of_not_gt hud, hu.2⟩ N (by omega)
      have hbudget := (hN1 N (by omega)).le
      have hremBound : C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤ gamma/2 := by
        have hh : C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
            C*((1+Real.log ((N : ℝ)+1))/(N : ℝ)) := by
          rw [← mul_div_assoc]
          apply (div_le_div_iff_of_pos_right hNp).mpr
          nlinarith
        exact hh.trans hbudget
      have hcu : c*u^2 ≤ gamma/2 := by
        have hsq : u^2 ≤ 1 := by nlinarith [hu.2, hu0]
        have hh := mul_le_mul_of_nonneg_left hsq hc.le
        have hcGamma : c ≤ gamma/2 := min_le_right _ _
        nlinarith
      apply hm.trans
      exact_mod_cast (by linarith : lam^2-gamma+C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤ lam^2-c*u^2)
  rw [PairConcentrationProofs.expectedCoupledFreeEnergy_eq N k lam u _ hmass] at hreal
  exact_mod_cast hreal

/-- Every stretched exponential dominates every fixed polynomial, along the
actual integer dimensions. -/
theorem nat_rpow_mul_exp_stretched_tendsto (s : ℝ) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)^s*Real.exp (-c*(N : ℝ)^p)) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop hp).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s/p) c hc).comp hpow
  apply H.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hn, mul_div_cancel₀ s hp.ne']

/-- A concrete polynomial remainder bound, uniform after a deterministic
dimension threshold. -/
theorem eventually_nat_mul_exp_stretched_le_rpow (s : ℝ) {p c C : ℝ}
    (hp : 0 < p) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ((N+1 : ℕ) : ℝ)*C*Real.exp (-c*(N : ℝ)^p) ≤ (N : ℝ)^s := by
  have H := (nat_rpow_mul_exp_stretched_tendsto (1-s) hp hc).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1/(2*C) from
      div_pos zero_lt_one (mul_pos (by norm_num) hC)))
  filter_upwards [H, eventually_ge_atTop (1 : ℕ)] with N hH hN
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  have hdim : ((N+1 : ℕ) : ℝ) ≤ 2*(N : ℝ) := by push_cast; exact_mod_cast (by omega : N+1 ≤ 2*N)
  have hunit : 2*C*((N : ℝ)^(1-s)*Real.exp (-c*(N : ℝ)^p)) ≤ 1 :=
    by simpa only [mul_comm] using (le_div_iff₀ (mul_pos (by norm_num) hC)).mp hH.le
  have hsplit : (N : ℝ) = (N : ℝ)^s*(N : ℝ)^(1-s) := by
    rw [← Real.rpow_add hn]
    simp only [add_sub_cancel, Real.rpow_one]
  calc
    _ ≤ (2*(N : ℝ))*C*Real.exp (-c*(N : ℝ)^p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdim hC.le) (Real.exp_pos _).le
    _ = ((N : ℝ)^s*(N : ℝ)^(1-s))*(2*C*Real.exp (-c*(N : ℝ)^p)) := by rw [← hsplit]; ring
    _ = (N : ℝ)^s*(2*C*((N : ℝ)^(1-s)*Real.exp (-c*(N : ℝ)^p))) := by ring
    _ ≤ (N : ℝ)^s*1 := mul_le_mul_of_nonneg_left hunit (Real.rpow_nonneg hn.le _)
    _ = _ := mul_one _

/-- The explicit finite-mesh Gaussian remainder is polynomially negligible. -/
theorem eventually_mesh_remainder_le (r : ℕ) {B delta : ℝ} (hB : 0 < B)
    (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      ((N+1 : ℕ) : ℝ)*(Real.exp (-(N : ℝ)*(N : ℝ)^((-1/2 : ℝ)+delta))+
        2*Real.exp (-(N : ℝ)*((N : ℝ)^((-1/2 : ℝ)+delta))^2/(32*B^2))) ≤
        2*((N : ℝ)^((-1/2 : ℝ)+delta))^r := by
  let e : ℝ := (-1/2 : ℝ)+delta
  let s : ℝ := (r : ℝ)*e
  have H1 := eventually_nat_mul_exp_stretched_le_rpow s
    (show (0 : ℝ) < (1/2 : ℝ)+delta by linarith) (c := 1) (C := 1) (by norm_num) (by norm_num)
  have H2 := eventually_nat_mul_exp_stretched_le_rpow s
    (show (0 : ℝ) < 2*delta by positivity) (c := 1/(32*B^2)) (C := 2) (by positivity) (by norm_num)
  filter_upwards [H1, H2, eventually_ge_atTop (1 : ℕ)] with N h1 h2 hN
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  have hp1 : (N : ℝ)*(N : ℝ)^e = (N : ℝ)^((1/2 : ℝ)+delta) := by
    calc
      _ = (N : ℝ)^(1 : ℝ)*(N : ℝ)^e := by rw [Real.rpow_one]
      _ = (N : ℝ)^((1 : ℝ)+e) := (Real.rpow_add hn _ _).symm
      _ = _ := by congr 1; dsimp [e]; ring
  have hp2 : (N : ℝ)*((N : ℝ)^e)^2/(32*B^2) = (1/(32*B^2))*(N : ℝ)^(2*delta) := by
    rw [← Real.rpow_mul_natCast hn.le e 2]
    have hh : (N : ℝ)*(N : ℝ)^(e*(2 : ℕ)) = (N : ℝ)^(2*delta) := by
      calc
        _ = (N : ℝ)^(1 : ℝ)*(N : ℝ)^(e*(2 : ℕ)) := by rw [Real.rpow_one]
        _ = (N : ℝ)^((1 : ℝ)+e*(2 : ℕ)) := (Real.rpow_add hn _ _).symm
        _ = _ := by congr 1; dsimp [e]; ring
    rw [hh]
    ring
  have hpow : ((N : ℝ)^e)^r = (N : ℝ)^s := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    dsimp [s]
    ring
  change ((N+1 : ℕ) : ℝ)*(Real.exp (-(N : ℝ)*(N : ℝ)^e)+
    2*Real.exp (-(N : ℝ)*((N : ℝ)^e)^2/(32*B^2))) ≤ 2*((N : ℝ)^e)^r
  have hneg1 : -(N : ℝ)*(N : ℝ)^e = -(N : ℝ)^((1/2 : ℝ)+delta) := by rw [neg_mul, hp1]
  have hneg2 : -(N : ℝ)*((N : ℝ)^e)^2/(32*B^2) = -(1/(32*B^2))*(N : ℝ)^(2*delta) := by
    rw [neg_mul, neg_div, hp2, neg_mul]
  rw [hneg1, hneg2, hpow]
  simp only [neg_one_mul, mul_one] at h1
  linarith

/-- The genuine uniform quadratic pair gap yields the actual polynomial
replica bound, with a single coefficient for every strength in the interval. -/
theorem eventual_replica_bound_of_quadratic_gap (r : ℕ) {barLam delta c : ℝ}
    (hbar : 0 ≤ barLam) (hdelta : delta ∈ Ioo (0 : ℝ) (1/2)) (hc : 0 < c)
    (hquad : ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      ∀ u ∈ Icc ((N : ℝ)^((-1/2 : ℝ)+delta)) 1,
        Coupled.meanPairFreeEnergy N (2*r) lam u (1/(N : ℝ)) ≤ lam^2-c*u^2) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N (2*r) lam ≤ K*((freeEnergyGap N (2*r) lam)^r+
        ((N : ℝ)^((-1/2 : ℝ)+delta))^r) := by
  let B := barLam+1
  have hB : 0 < B := by dsimp [B]; linarith
  let e : ℝ := (-1/2 : ℝ)+delta
  let D : ℝ := (2/c)^r*2^(r-1)
  have hD : 0 < D := mul_pos (pow_pos (div_pos (by norm_num) hc) r) (by positivity)
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ)^e) atTop (𝓝 0) := by
    have he : -((1/2 : ℝ)-delta) = e := by dsimp [e]; ring
    simpa only [Function.comp_def, he] using
      (tendsto_rpow_neg_atTop (by linarith [hdelta.2] : 0 < (1/2 : ℝ)-delta)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := ht.eventually (Iio_mem_nhds (div_pos (by norm_num) hc : (0 : ℝ) < 2/c))
  refine ⟨D+2, by linarith, ?_⟩
  filter_upwards [hquad, hsmall, eventually_mesh_remainder_le r hB hdelta.1,
    eventually_ge_atTop (2 : ℕ)] with N hq hs hrem hN
  intro lam hlam
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  have hpsi : 0 ≤ freeEnergyGap N (2*r) lam :=
    (freeEnergyGap_bounds (by omega : 0 < N) (show Even (2*r) from ⟨r, by omega⟩) hlam.1).1
  let b := (N : ℝ)^e
  let v := (2*freeEnergyGap N (2*r) lam+2*b)/c
  have hb : 0 < b := Real.rpow_pos_of_pos hn e
  have hv : 0 ≤ v := div_nonneg (by positivity) hc.le
  have hbudget : c*v = 2*freeEnergyGap N (2*r) lam+2*b := mul_div_cancel₀ _ hc.ne'
  have hcb : c*b ≤ 2 := by simpa only [mul_comm] using (le_div_iff₀ hc).mp hs.le
  have hcut : b^2 ≤ v := by
    apply (le_div_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_right hcb hb.le
    nlinarith
  have hbound := replicaMean_le_of_quadratic_gap hN lam hB
    (show |lam| ≤ B by rw [abs_of_nonneg hlam.1]; dsimp [B]; linarith [hlam.2]) hv hb hc.le hcut
      hbudget.ge (hq lam hlam)
  have hvEq : v = (2/c)*(freeEnergyGap N (2*r) lam+b) := by dsimp [v]; ring
  have hVpow : v^r ≤ D*((freeEnergyGap N (2*r) lam)^r+b^r) := by
    rw [hvEq, mul_pow]
    have hh := mul_le_mul_of_nonneg_left (add_pow_le hpsi hb.le r) (pow_nonneg (show (0 : ℝ) ≤ 2/c by positivity) r)
    simpa only [D, mul_assoc] using hh
  have htail : ((N+1 : ℕ) : ℝ)*(Real.exp (-(N : ℝ)*b)+
      2*Real.exp (-(N : ℝ)*b^2/(32*B^2))) ≤ 2*b^r := hrem
  have hpn : 0 ≤ (freeEnergyGap N (2*r) lam)^r := pow_nonneg hpsi r
  change replicaMean N (2*r) lam ≤ (D+2)*((freeEnergyGap N (2*r) lam)^r+b^r)
  nlinarith

/-- The checked finite Gaussian covariance derivative and Gronwall comparison
turn the actual uniform replica bound into the quantitative null mean bound. -/
theorem eventual_mean_bound_of_replica_bound (r : ℕ) (hr : 1 ≤ r)
    {barLam delta : ℝ} (hbar : 0 ≤ barLam)
    (hrep : ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N (2*r) lam ≤ K*((freeEnergyGap N (2*r) lam)^r+
        ((N : ℝ)^((-1/2 : ℝ)+delta))^r)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      freeEnergyGap N (2*r) lam ≤ D*((N : ℝ)^((-1/2 : ℝ)+delta))^r := by
  obtain ⟨K,hK,hrep⟩ := hrep
  let M := barLam^2/2
  have hM : 0 ≤ M := div_nonneg (sq_nonneg _) (by norm_num)
  let B := barLam+1
  have hB : 0 < B := by dsimp [B]; linarith
  let C := B*K*(M^(r-1)+1)
  have hC : 0 < C := mul_pos (mul_pos hB hK) (by positivity)
  refine ⟨Real.exp (C*barLam), Real.exp_pos _, ?_⟩
  filter_upwards [hrep, eventually_ge_atTop (1 : ℕ)] with N hrep hN
  have hNp : 0 < N := by omega
  let a := ((N : ℝ)^((-1/2 : ℝ)+delta))^r
  have ha : 0 ≤ a := pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) r
  have hlin : ∀ t ∈ Icc (0 : ℝ) barLam,
      t*replicaMean N (2*r) t ≤ C*(freeEnergyGap N (2*r) t+a) := by
    intro t ht
    have hpsi0 := (freeEnergyGap_bounds hNp (show Even (2*r) from ⟨r, by omega⟩) ht.1).1
    have hpsiM : freeEnergyGap N (2*r) t ≤ M :=
      (freeEnergyGap_bounds hNp (show Even (2*r) from ⟨r, by omega⟩) ht.1).2.trans
        (div_le_div_of_nonneg_right ((sq_le_sq₀ ht.1 hbar).mpr ht.2) (by norm_num))
    have hpower : (freeEnergyGap N (2*r) t)^r ≤ M^(r-1)*freeEnergyGap N (2*r) t := by
      simpa only [← pow_succ, Nat.sub_add_cancel hr] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpsi0 hpsiM (r-1)) hpsi0
    have htB : t ≤ B := by dsimp [B]; linarith [ht.2]
    have hsmall : M^(r-1)*freeEnergyGap N (2*r) t+a ≤
        (M^(r-1)+1)*(freeEnergyGap N (2*r) t+a) := by
      nlinarith [mul_nonneg (pow_nonneg hM (r-1)) ha]
    calc
      _ ≤ t*(K*((freeEnergyGap N (2*r) t)^r+a)) :=
        mul_le_mul_of_nonneg_left (hrep t ht) ht.1
      _ ≤ B*(K*((freeEnergyGap N (2*r) t)^r+a)) :=
        mul_le_mul_of_nonneg_right htB (mul_nonneg hK.le (add_nonneg (pow_nonneg hpsi0 r) ha))
      _ ≤ B*(K*(M^(r-1)*freeEnergyGap N (2*r) t+a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hpower (le_refl a)) hK.le) hB.le
      _ ≤ B*(K*((M^(r-1)+1)*(freeEnergyGap N (2*r) t+a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall hK.le) hB.le
      _ = _ := by dsimp [C]; ring
  intro lam hlam
  have H := NullGronwallProofs.freeEnergyGap_le_uniform_of_replicaMean_bound hNp
    barLam C a hC.le ha hlin hlam
  exact H.trans (mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) ha)

/-- Conditional quantitative mean bound: the sole substantial physical premise
is the actual coupled trial/interpolation theorem, not any replica or mean rate. -/
theorem eventual_mean_bound_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (r : ℕ) (hr : 2 ≤ r) {barLam delta : ℝ}
    (hbar : 0 ≤ barLam) (hsub : barLam < Scalar.lambdaC (2*r))
    (hdelta : delta ∈ Ioo (0 : ℝ) (1/2)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      freeEnergyGap N (2*r) lam ≤ D*((N : ℝ)^((-1/2 : ℝ)+delta))^r := by
  obtain ⟨c,hc,N0,hN0,hgap⟩ := quadratic_mean_gap_of_trialBound htrial (2*r) (by omega)
    (show Even (2*r) from ⟨r, by omega⟩) hbar hsub hdelta
  apply eventual_mean_bound_of_replica_bound r (by omega) hbar
  apply eventual_replica_bound_of_quadratic_gap r hbar hdelta hc
  filter_upwards [eventually_ge_atTop N0] with N hN
  exact fun lam hlam u hu ↦ hgap lam hlam N hN u hu

/-- Extending finitely many dimensions uses the actual finite gap bound,
with no finiteness or moment premise left implicit. -/
theorem all_dimension_mean_bound_of_eventual {k : ℕ} (heven : Even k)
    {barLam s : ℝ} (hbar : 0 ≤ barLam) (hs : s ≤ 0)
    (hevent : ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      freeEnergyGap N k lam ≤ D*(N : ℝ)^s) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Icc (0 : ℝ) barLam,
      freeEnergyGap N k lam ≤ C*(N : ℝ)^s := by
  obtain ⟨D,hD,hDall⟩ := hevent
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hDall
  let J := max N0 1
  have hJ : (0 : ℝ) < J := Nat.cast_pos.mpr (by dsimp [J]; omega)
  let M := barLam^2/2
  have hM : 0 ≤ M := div_nonneg (sq_nonneg _) (by norm_num)
  let A := M*(J : ℝ)^(-s)
  have hA : 0 ≤ A := mul_nonneg hM (Real.rpow_nonneg hJ.le _)
  let C := D+A+1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro N hN lam hlam
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hNp
  by_cases hNJ : J ≤ N
  · have hh := hN0 N (by dsimp [J] at hNJ; omega) lam hlam
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
      (Real.rpow_nonneg hn.le _))
  · have hNle : (N : ℝ) ≤ J := Nat.cast_le.mpr (by omega)
    have hp := Real.rpow_le_rpow_of_nonpos hn hNle hs
    have hcancel : (J : ℝ)^(-s)*(J : ℝ)^s = 1 := by
      rw [← Real.rpow_add hJ, neg_add_cancel, Real.rpow_zero]
    have hgap : freeEnergyGap N k lam ≤ M :=
      (freeEnergyGap_bounds hNp heven hlam.1).2.trans
        (div_le_div_of_nonneg_right ((sq_le_sq₀ hlam.1 hbar).mpr hlam.2) (by norm_num))
    calc
      _ ≤ M := hgap
      _ = A*(J : ℝ)^s := by dsimp [A]; rw [mul_assoc, hcancel, mul_one]
      _ ≤ A*(N : ℝ)^s := mul_le_mul_of_nonneg_left hp hA
      _ ≤ C*(N : ℝ)^s := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (Real.rpow_nonneg hn.le _)

/-- Quantitative mean decay, uniform over a fixed subcritical strength interval. -/
theorem uniform_mean_bound_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (r : ℕ) (hr : 2 ≤ r) {barLam eps : ℝ}
    (hbar : 0 ≤ barLam) (hsub : barLam < Scalar.lambdaC (2*r)) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Icc (0 : ℝ) barLam,
      freeEnergyGap N (2*r) lam ≤ C*(N : ℝ)^(-(r : ℝ)/2+eps) := by
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  let delta := min (1/4 : ℝ) (eps/(2*(r : ℝ)))
  have hdpos : 0 < delta := lt_min (by norm_num) (div_pos heps (by positivity))
  have hdhi : delta < (1/2 : ℝ) := (min_le_left _ _).trans_lt (by norm_num)
  let s := (r : ℝ)*((-1/2 : ℝ)+delta)
  have hs : s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrpos.le (by dsimp [delta] at hdhi; linarith)
  have hrate := eventual_mean_bound_of_trialBound htrial r hr hbar hsub ⟨hdpos,hdhi⟩
  have hpow (N : ℕ) : ((N : ℝ)^((-1/2 : ℝ)+delta))^r = (N : ℝ)^s := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    congr 1
    dsimp [s]
    ring
  simp_rw [hpow] at hrate
  obtain ⟨C,hC,hCall⟩ := all_dimension_mean_bound_of_eventual
    (show Even (2*r) from ⟨r, by omega⟩) hbar hs hrate
  refine ⟨C,hC,?_⟩
  intro N hN lam hlam
  apply (hCall N hN lam hlam).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have hmul : delta*(2*(r : ℝ)) ≤ eps :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(r : ℝ))).mp (min_le_right _ _)
  dsimp [s]
  nlinarith

/-- The complete reviewed Theorem 2.3 contract is reduced to the genuine
physical coupled trial theorem; no mean-rate conclusion is assumed. -/
theorem meanFreeEnergyRate_of_trialBound (htrial : Coupled.CoupledTrialBound) :
    Coupled.MeanFreeEnergyRate := by
  intro k hk heven lam hlam hsub eps heps
  obtain ⟨r,hr⟩ := heven
  have hkEq : k = 2*r := by omega
  rw [hkEq] at hk hsub ⊢
  obtain ⟨C,hC,hbound⟩ := uniform_mean_bound_of_trialBound htrial r (by omega) hlam hsub heps
  refine ⟨C,hC,?_⟩
  intro N hN
  rw [abs_sub_comm]
  change |freeEnergyGap N (2*r) lam| ≤ _
  rw [abs_of_nonneg (freeEnergyGap_bounds (by omega : 0 < N)
    (show Even (2*r) from ⟨r, by omega⟩) hlam).1]
  convert hbound N hN lam ⟨hlam,le_rfl⟩ using 1
  push_cast
  ring

/-- Feeding the checked mean bound back into the finite replica inequality
produces the actual replica decay at the same polynomial scale. -/
theorem eventual_replica_decay_of_replica_bound (r : ℕ) (hr : 1 ≤ r)
    {barLam delta : ℝ} (hbar : 0 ≤ barLam)
    (hrep : ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N (2*r) lam ≤ K*((freeEnergyGap N (2*r) lam)^r+
        ((N : ℝ)^((-1/2 : ℝ)+delta))^r)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N (2*r) lam ≤ D*((N : ℝ)^((-1/2 : ℝ)+delta))^r := by
  obtain ⟨K,hK,hrep⟩ := hrep
  obtain ⟨D,hD,hmean⟩ := eventual_mean_bound_of_replica_bound r hr hbar ⟨K,hK,hrep⟩
  let M := barLam^2/2
  have hM : 0 ≤ M := div_nonneg (sq_nonneg _) (by norm_num)
  refine ⟨K*(M^(r-1)*D+1), mul_pos hK (by positivity), ?_⟩
  filter_upwards [hrep,hmean,eventually_ge_atTop (1 : ℕ)] with N hrep hmean hN
  intro lam hlam
  have hNp : 0 < N := by omega
  have hpsi0 := (freeEnergyGap_bounds hNp (show Even (2*r) from ⟨r, by omega⟩) hlam.1).1
  have hpsiM : freeEnergyGap N (2*r) lam ≤ M :=
    (freeEnergyGap_bounds hNp (show Even (2*r) from ⟨r, by omega⟩) hlam.1).2.trans
      (div_le_div_of_nonneg_right ((sq_le_sq₀ hlam.1 hbar).mpr hlam.2) (by norm_num))
  have hpower : (freeEnergyGap N (2*r) lam)^r ≤ M^(r-1)*freeEnergyGap N (2*r) lam := by
    simpa only [← pow_succ, Nat.sub_add_cancel hr] using
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpsi0 hpsiM (r-1)) hpsi0
  calc
    _ ≤ K*((freeEnergyGap N (2*r) lam)^r+((N : ℝ)^((-1/2 : ℝ)+delta))^r) := hrep lam hlam
    _ ≤ K*(M^(r-1)*freeEnergyGap N (2*r) lam+((N : ℝ)^((-1/2 : ℝ)+delta))^r) :=
      mul_le_mul_of_nonneg_left (add_le_add hpower (le_refl _)) hK.le
    _ ≤ K*(M^(r-1)*(D*((N : ℝ)^((-1/2 : ℝ)+delta))^r)+((N : ℝ)^((-1/2 : ℝ)+delta))^r) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hmean lam hlam)
        (pow_nonneg hM (r-1))) (le_refl _)) hK.le
    _ = _ := by ring

/-- Finite exceptional dimensions in a replica rate are controlled by the
actual Gibbs probability bound rather than a new integrability premise. -/
theorem all_dimension_replica_bound_of_eventual {k : ℕ} {barLam s : ℝ} (hs : s ≤ 0)
    (hevent : ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N k lam ≤ D*(N : ℝ)^s) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N k lam ≤ C*(N : ℝ)^s := by
  obtain ⟨D,hD,hDall⟩ := hevent
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hDall
  let J := max N0 1
  have hJ : (0 : ℝ) < J := Nat.cast_pos.mpr (by dsimp [J]; omega)
  let A := (J : ℝ)^(-s)
  have hA : 0 ≤ A := Real.rpow_nonneg hJ.le _
  let C := D+A+1
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro N hN lam hlam
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hNp
  by_cases hNJ : J ≤ N
  · exact (hN0 N (by dsimp [J] at hNJ; omega) lam hlam).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg hn.le _))
  · have hp := Real.rpow_le_rpow_of_nonpos hn (Nat.cast_le.mpr (by omega : N ≤ J)) hs
    have hcancel : A*(J : ℝ)^s = 1 := by
      dsimp [A]
      rw [← Real.rpow_add hJ, neg_add_cancel, Real.rpow_zero]
    calc
      _ ≤ 1 := replicaMean_le_one hNp lam
      _ = A*(J : ℝ)^s := hcancel.symm
      _ ≤ A*(N : ℝ)^s := mul_le_mul_of_nonneg_left hp hA
      _ ≤ C*(N : ℝ)^s := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (Real.rpow_nonneg hn.le _)

/-- Corollary 3.1's replica decay, with constants uniform on each compact
subcritical strength interval and all positive dimensions. -/
theorem uniform_replica_rate_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (r : ℕ) (hr : 2 ≤ r) {barLam eps : ℝ}
    (hbar : 0 ≤ barLam) (hsub : barLam < Scalar.lambdaC (2*r)) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Icc (0 : ℝ) barLam,
      replicaMean N (2*r) lam ≤ C*(N : ℝ)^(-(r : ℝ)/2+eps) := by
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  let delta := min (1/4 : ℝ) (eps/(2*(r : ℝ)))
  have hdpos : 0 < delta := lt_min (by norm_num) (div_pos heps (by positivity))
  have hdhi : delta < (1/2 : ℝ) := (min_le_left _ _).trans_lt (by norm_num)
  obtain ⟨c,hc,N0,_,hgap⟩ := quadratic_mean_gap_of_trialBound htrial (2*r) (by omega)
    (show Even (2*r) from ⟨r, by omega⟩) hbar hsub ⟨hdpos,hdhi⟩
  have hquad : ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) barLam,
      ∀ u ∈ Icc ((N : ℝ)^((-1/2 : ℝ)+delta)) 1,
        Coupled.meanPairFreeEnergy N (2*r) lam u (1/(N : ℝ)) ≤ lam^2-c*u^2 :=
    (eventually_ge_atTop N0).mono (fun N hN lam hlam u hu ↦ hgap lam hlam N hN u hu)
  have hrep := eventual_replica_bound_of_quadratic_gap r hbar ⟨hdpos,hdhi⟩ hc hquad
  have hdec := eventual_replica_decay_of_replica_bound r (by omega) hbar hrep
  let s := (r : ℝ)*((-1/2 : ℝ)+delta)
  have hs : s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrpos.le (by linarith)
  have hpow (N : ℕ) : ((N : ℝ)^((-1/2 : ℝ)+delta))^r = (N : ℝ)^s := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    congr 1
    dsimp [s]
    ring
  simp_rw [hpow] at hdec
  obtain ⟨C,hC,hCall⟩ := all_dimension_replica_bound_of_eventual hs hdec
  refine ⟨C,hC,?_⟩
  intro N hN lam hlam
  apply (hCall N hN lam hlam).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have hmul : delta*(2*(r : ℝ)) ≤ eps :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(r : ℝ))).mp (min_le_right _ _)
  dsimp [s]
  nlinarith

/-- The actual replica rate used by the sharp null variance estimate. -/
theorem replica_rate_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 4 ≤ k) (heven : Even k) (lam : ℝ)
    (hlam : 0 ≤ lam) (hsub : lam < Scalar.lambdaC k) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → replicaMean N k lam ≤ C*(N : ℝ)^(-(k : ℝ)/4+eps) := by
  obtain ⟨r,hr⟩ := heven
  have hkEq : k = 2*r := by omega
  rw [hkEq] at hk hsub ⊢
  obtain ⟨C,hC,hbound⟩ := uniform_replica_rate_of_trialBound htrial r (by omega) hlam hsub heps
  refine ⟨C,hC,?_⟩
  intro N hN
  convert hbound N hN lam ⟨hlam,le_rfl⟩ using 1
  push_cast
  ring

/-- The full reviewed sharp variance contract follows from actual replica
decay and the accepted Gaussian Poincare/gradient identity. -/
theorem varianceFreeEnergyRate_of_trialBound (htrial : Coupled.CoupledTrialBound) :
    Coupled.VarianceFreeEnergyRate := by
  intro k hk heven lam hlam hsub eps heps
  obtain ⟨C,hC,hbound⟩ := replica_rate_of_trialBound htrial k hk heven lam hlam hsub eps heps
  refine ⟨(lam^2+1)*C, mul_pos (by positivity) hC, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  have ha : 0 ≤ lam^2/(N : ℝ) := div_nonneg (sq_nonneg _) hn.le
  have hnorm : (lam^2/(N : ℝ))*(C*(N : ℝ)^(-(k : ℝ)/4+eps)) =
      (lam^2*C)/(N : ℝ)^((k : ℝ)/4+1-eps) := by
    have hinv : (N : ℝ)^(-1 : ℝ) = (N : ℝ)⁻¹ := by rw [Real.rpow_neg hn.le, Real.rpow_one]
    calc
      _ = lam^2*C*((N : ℝ)^(-(k : ℝ)/4+eps)*(N : ℝ)^(-1 : ℝ)) := by rw [hinv]; ring
      _ = lam^2*C*(N : ℝ)^((-(k : ℝ)/4+eps)+(-1 : ℝ)) := by rw [← Real.rpow_add hn]
      _ = lam^2*C*(N : ℝ)^(-((k : ℝ)/4+1-eps)) := by congr 2; ring
      _ = _ := by rw [Real.rpow_neg hn.le]; ring
  calc
    _ ≤ (lam^2/(N : ℝ))*replicaMean N k lam :=
      NullVarianceProofs.varNullFE_le_replicaMean (by omega) lam
    _ ≤ (lam^2/(N : ℝ))*(C*(N : ℝ)^(-(k : ℝ)/4+eps)) :=
      mul_le_mul_of_nonneg_left (hbound N hN) ha
    _ = (lam^2*C)/(N : ℝ)^((k : ℝ)/4+1-eps) := hnorm
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith)
      (Real.rpow_nonneg hn.le _)

/-- Even-order replica moments in the actual Gibbs measure equal the absolute
moments in the manuscript's Corollary 3.1. -/
theorem replicaMean_eq_absolute_moment (N k : ℕ) (heven : Even k) (lam : ℝ) :
    replicaMean N k lam = ∫ w, ∫ z : Model.Vector N × Model.Vector N,
      |inner ℝ z.1 z.2|^k ∂(thermalGibbs N k lam w).prod (thermalGibbs N k lam w)
        ∂Model.noiseLaw N k := by
  unfold replicaMean replicaMoment
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [← abs_pow, abs_of_nonneg (heven.pow_nonneg _)]

/-- The exact actual bias-variance identity underlying Equation (2.6). -/
theorem freeEnergy_sq_deviation_eq_variance_bias {N k : ℕ} (hN : 0 < N) (lam a : ℝ) :
    (∫ w, (Model.freeEnergy N k lam w-a)^2 ∂Model.noiseLaw N k) =
      Coupled.varNullFE N k lam+(Coupled.meanNullFE N k lam-a)^2 := by
  have hFE := FreeEnergyProofs.freeEnergy_memLp (k := k) hN lam 2 (by norm_num)
  have hInt := hFE.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hvar : variance (Model.freeEnergy N k lam) (Model.noiseLaw N k) = Coupled.varNullFE N k lam := by
    rw [variance_eq_integral hFE.aemeasurable]
    rfl
  have hShift : MemLp (fun w ↦ Model.freeEnergy N k lam w-a) 2 (Model.noiseLaw N k) :=
    (hFE.sub (memLp_const a)).ae_eq (Eventually.of_forall (fun _ ↦ rfl))
  have H := variance_eq_sub hShift
  rw [variance_sub_const hFE.aestronglyMeasurable a, hvar] at H
  simp only [Pi.pow_apply] at H
  rw [integral_sub hInt (integrable_const a), integral_const, probReal_univ, one_smul] at H
  change Coupled.varNullFE N k lam =
    (∫ w, (Model.freeEnergy N k lam w-a)^2 ∂Model.noiseLaw N k)-
      (Coupled.meanNullFE N k lam-a)^2 at H
  linarith

/-- Genuine finite Chebyshev control, with the actual mean and centered second
moment and no assumed tail integrability. -/
theorem freeEnergy_chebyshev {N k : ℕ} (hN : 0 < N) (lam a t : ℝ) (ht : 0 < t) :
    (Model.noiseLaw N k).real {w | |Model.freeEnergy N k lam w-a| > t} ≤
      (Coupled.varNullFE N k lam+(Coupled.meanNullFE N k lam-a)^2)/t^2 := by
  have hFE := FreeEnergyProofs.freeEnergy_memLp (k := k) hN lam 2 (by norm_num)
  have hSq := (hFE.sub (memLp_const a)).integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun w : Model.Tensor N k ↦ sq_nonneg (Model.freeEnergy N k lam w-a))) hSq (t^2)
  have hsub : {w : Model.Tensor N k | |Model.freeEnergy N k lam w-a| > t} ⊆
      {w | t^2 ≤ (Model.freeEnergy N k lam w-a)^2} := by
    intro w hw
    have hh : t < |Model.freeEnergy N k lam w-a| := hw
    have habs := abs_nonneg (Model.freeEnergy N k lam w-a)
    have hs := sq_abs (Model.freeEnergy N k lam w-a)
    change t^2 ≤ (Model.freeEnergy N k lam w-a)^2
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = t^2*(Model.noiseLaw N k).real {w | |Model.freeEnergy N k lam w-a| > t} := mul_comm _ _
    _ ≤ t^2*(Model.noiseLaw N k).real {w | t^2 ≤ (Model.freeEnergy N k lam w-a)^2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg t)
    _ ≤ ∫ w, (Model.freeEnergy N k lam w-a)^2 ∂Model.noiseLaw N k := hm
    _ = _ := freeEnergy_sq_deviation_eq_variance_bias hN lam a

/-- The reviewed Theorem 2.2 fluctuation contract, reduced only to actual
physical coupled interpolation through the checked mean and variance rates. -/
theorem fluctuationFreeEnergyRate_of_trialBound (htrial : Coupled.CoupledTrialBound) :
    Coupled.FluctuationFreeEnergyRate := by
  intro k hk heven lam hlam hsub eps heps
  obtain ⟨Cm,hCm,hm⟩ := meanFreeEnergyRate_of_trialBound htrial k hk heven lam hlam hsub (eps/2) (half_pos heps)
  obtain ⟨Cv,hCv,hv⟩ := varianceFreeEnergyRate_of_trialBound htrial k hk heven lam hlam hsub eps heps
  let C := Cv+Cm^2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN x hx
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  let p : ℝ := (k : ℝ)/4+1-eps
  let q : ℝ := ((k : ℝ)-4)/4-eps
  have hBias : (Coupled.meanNullFE N k lam-lam^2/2)^2 ≤
      Cm^2*(N : ℝ)^(-(k : ℝ)/2+eps) := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hCm.le (Real.rpow_nonneg hn.le _))).mpr (hm N hN)
    rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast hn.le] at hh
    convert hh using 1
    congr 2
    ring
  have hBiasCommon : (Coupled.meanNullFE N k lam-lam^2/2)^2 ≤ Cm^2/(N : ℝ)^p := by
    apply hBias.trans
    rw [div_eq_mul_inv (Cm^2) ((N : ℝ)^p), ← Real.rpow_neg hn.le]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cm)
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    have hkr : (4 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [p]
    linarith
  have hSecond : Coupled.varNullFE N k lam+(Coupled.meanNullFE N k lam-lam^2/2)^2 ≤ C/(N : ℝ)^p := by
    have hh := add_le_add (hv N hN) hBiasCommon
    simpa only [C, ← add_div, p] using hh
  have hpower : (N : ℝ)^p = (N : ℝ)^q*(N : ℝ)^2 := by
    rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hn]
    congr 1
    dsimp [p,q]
    ring
  have hnormalize : (C/(N : ℝ)^p)/(x/(N : ℝ))^2 = C/(x^2*(N : ℝ)^q) := by
    rw [hpower]
    field_simp [hn.ne', hx.ne', (Real.rpow_pos_of_pos hn q).ne']
  calc
    _ ≤ (Coupled.varNullFE N k lam+(Coupled.meanNullFE N k lam-lam^2/2)^2)/(x/(N : ℝ))^2 :=
      freeEnergy_chebyshev (by omega) lam (lam^2/2) (x/(N : ℝ)) (div_pos hx hn)
    _ ≤ (C/(N : ℝ)^p)/(x/(N : ℝ))^2 := div_le_div_of_nonneg_right hSecond (sq_nonneg _)
    _ = _ := hnormalize

end
end TensorPCA.ReplicaRateProofs
