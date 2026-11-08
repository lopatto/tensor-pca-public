-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairConcentrationProofs
public import TensorPCA.FreeEnergyConcentrationProofs
public import TensorPCA.WindowMassProofs
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Finite overlap-window concentration and covering estimates. The bounds here
are conditional only on explicit finite deterministic mean gaps; no coupled
trial bound or replica asymptotic rate is assumed to be proved. -/

@[expose] public section
namespace TensorPCA.ReplicaMeshProofs
open MeasureTheory ProbabilityTheory Set Filter PairRegularityProofs ThermalReplicaProofs
open scoped Topology RealInnerProductSpace ENNReal BigOperators
noncomputable section

/-- Literal two-replica Gibbs probability of the manuscript's overlap window. -/
def windowProbability (N k : ℕ) (lam u eta : ℝ) (w : Model.Tensor N k) : ℝ :=
  ((thermalGibbs N k lam w).prod (thermalGibbs N k lam w)).real (Coupled.pairWindow N u eta)

/-- The exact physical partition-ratio identity on the positive branch. -/
theorem windowProbability_eq_exp {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (w : Model.Tensor N k) :
    windowProbability N k lam u eta w = Real.exp ((N : ℝ)*
      (Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w)) := by
  have hp := pairPartition_pos hN lam u eta hm w
  have hprob : 0 < windowProbability N k lam u eta w := by
    rw [windowProbability, PairGibbsProofs.thermalGibbs_pairWindow_real hN lam u eta w]
    exact div_pos hp (sq_pos_of_pos (FreeEnergyProofs.partitionFunction_pos hN lam w))
  rw [← PairGibbsProofs.log_thermalGibbs_pairWindow hN lam u eta w hp]
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  exact (Real.exp_log hprob).symm

/-- The two-replica log probability has uniform scale 4|λ|/sqrt(N). -/
theorem windowLogProbability_lipschitz {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) :
    LipschitzWith (4*|lam|/Real.sqrt N).toNNReal (fun w ↦
      Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  rw [Real.coe_toNNReal _ (by positivity)]
  have hp := (PairConcentrationProofs.pairFreeEnergy_lipschitz hN lam u eta hm).dist_le_mul w v
  have hn := (FreeEnergyConcentrationProofs.freeEnergy_lipschitz hN lam).dist_le_mul w v
  rw [Real.coe_toNNReal (2*|lam|/Real.sqrt N) (by positivity)] at hp
  rw [Real.coe_toNNReal (|lam|/Real.sqrt N) (by positivity)] at hn
  simp only [Real.dist_eq] at hp hn
  rw [Real.dist_eq]
  calc
    _ = |(Real.log (Coupled.pairPartition N k lam u eta w)/N-
      Real.log (Coupled.pairPartition N k lam u eta v)/N)-
      2*(Model.freeEnergy N k lam w-Model.freeEnergy N k lam v)| := by congr 1; ring
    _ ≤ |Real.log (Coupled.pairPartition N k lam u eta w)/N-
      Real.log (Coupled.pairPartition N k lam u eta v)/N|+
      |2*(Model.freeEnergy N k lam w-Model.freeEnergy N k lam v)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (Real.log (Coupled.pairPartition N k lam u eta w)/N-
            Real.log (Coupled.pairPartition N k lam u eta v)/N) 0
            (2*(Model.freeEnergy N k lam w-Model.freeEnergy N k lam v))
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact (add_le_add hp (mul_le_mul_of_nonneg_left hn (by norm_num))).trans_eq (by ring)

/-- Integrability identifies the centered log ratio with the actual pair and
null free-energy means, preserving the window-mass constant. -/
theorem integral_windowLogProbability {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) :
    (∫ w, Real.log (Coupled.pairPartition N k lam u eta w)/N-
      2*Model.freeEnergy N k lam w ∂Model.noiseLaw N k) =
      Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam := by
  have hp := ((log_pairPartition_memLp (k := k) hN lam u eta hm 1 (by norm_num)).integrable le_rfl).div_const (N : ℝ)
  have hn := (FreeEnergyProofs.freeEnergy_memLp (k := k) hN lam 1 (by norm_num)).integrable le_rfl
  rw [integral_sub hp (hn.const_mul 2), integral_const_mul]
  rfl

/-- Concentration of the actual positive-window partition log ratio. -/
theorem windowLogProbability_gaussian_tail {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w |
      |(Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w)-
        (Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam)| > t} ≤
      ENNReal.ofReal (2*Real.exp (-(N : ℝ)*t^2/(32*lam^2))) := by
  by_cases hlam : lam = 0
  · subst lam
    simp only [PairConcentrationProofs.pairPartition_zero,
      PairConcentrationProofs.meanPairFreeEnergy_zero, FreeEnergyConcentrationProofs.freeEnergy_zero,
      Coupled.meanNullFE, integral_zero, mul_zero, sub_zero, sub_self, abs_zero,
      not_lt.mpr ht.le, ofPred_false, measure_empty]
    exact zero_le
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hL : 0 < 4*|lam|/Real.sqrt N := div_pos (mul_pos (by norm_num) (abs_pos.mpr hlam)) hs
  have hb := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (fun w : Model.Tensor N k ↦ Real.log (Coupled.pairPartition N k lam u eta w)/N-
      2*Model.freeEnergy N k lam w) (4*|lam|/Real.sqrt N) t hL ht
        (windowLogProbability_lipschitz hN lam u eta hm)
  have he : -t^2/(2*(4*|lam|/Real.sqrt N)^2) = -(N : ℝ)*t^2/(32*lam^2) := by
    rw [div_pow, mul_pow, sq_abs]
    field_simp [hs.ne', hlam]
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  have hMean := integral_windowLogProbability (k := k) hN lam u eta hm
  change (∫ w, Real.log (Coupled.pairPartition N k lam u eta w)/N-
    2*Model.freeEnergy N k lam w ∂stdGaussian (Model.Tensor N k)) = _ at hMean
  rw [hMean, he] at hb
  exact hb

theorem windowProbability_nonneg (N k : ℕ) (lam u eta : ℝ) (w : Model.Tensor N k) :
    0 ≤ windowProbability N k lam u eta w := measureReal_nonneg

theorem windowProbability_le_one {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (w : Model.Tensor N k) : windowProbability N k lam u eta w ≤ 1 := by
  have := thermalGibbs_probability hN lam w
  exact measureReal_le_one

theorem windowProbability_continuous {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) : Continuous (windowProbability N k lam u eta) := by
  have heq : windowProbability N k lam u eta = (fun w ↦ Real.exp ((N : ℝ)*
      (Real.log (Coupled.pairPartition N k lam u eta w)/N-2*Model.freeEnergy N k lam w))) :=
    funext (windowProbability_eq_exp hN lam u eta hm)
  rw [heq]
  exact Real.continuous_exp.comp
    ((windowLogProbability_lipschitz hN lam u eta hm).continuous.const_mul (N : ℝ))

/-- Every bounded probability observable has mean at most a threshold plus its
tail probability; this elementary integration step needs no independence. -/
theorem integral_le_threshold_add_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) {q : ℝ} (hq : 0 ≤ q) :
    (∫ ω, f ω ∂μ) ≤ q+μ.real {ω | q < f ω} := by
  have hE : MeasurableSet {ω | q < f ω} := measurableSet_lt measurable_const hf
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ω)] using h1 ω))
  have hpoint (ω : Ω) : f ω ≤ q+({ω | q < f ω}.indicator (fun _ ↦ (1 : ℝ))) ω := by
    by_cases hω : q < f ω
    · rw [indicator_of_mem (show ω ∈ {ω | q < f ω} from hω)]
      linarith [h1 ω]
    · rw [indicator_of_notMem (show ω ∉ {ω | q < f ω} from hω), add_zero]
      exact le_of_not_gt hω
  have H := integral_mono hi ((integrable_const q).add ((integrable_const (1 : ℝ)).indicator hE)) hpoint
  simp only [Pi.add_apply] at H
  rw [integral_add (integrable_const q) ((integrable_const (1 : ℝ)).indicator hE),
    integral_const, integral_indicator_const (1 : ℝ) hE, probReal_univ, one_smul, smul_eq_mul, mul_one] at H
  exact H

/-- A genuine deterministic mean gap gives a finite per-window Gibbs mass
bound. No replica moment or coupled trial conclusion is hidden in the premise. -/
theorem expected_windowProbability_le_of_gap {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) {b : ℝ} (hb : 0 < b)
    (hgap : Coupled.meanPairFreeEnergy N k lam u eta-2*Coupled.meanNullFE N k lam ≤ -2*b) :
    (∫ w, windowProbability N k lam u eta w ∂Model.noiseLaw N k) ≤
      Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*lam^2)) := by
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
  have htail := (measure_mono hsub).trans (windowLogProbability_gaussian_tail hN lam u eta hm b hb)
  have htailReal : (Model.noiseLaw N k).real
      {w | Real.exp (-(N : ℝ)*b) < windowProbability N k lam u eta w} ≤
      2*Real.exp (-(N : ℝ)*b^2/(32*lam^2)) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mp htail
  exact (integral_le_threshold_add_tail (Model.noiseLaw N k)
    (windowProbability N k lam u eta) (windowProbability_continuous hN lam u eta hm).measurable
    (windowProbability_nonneg N k lam u eta) (windowProbability_le_one hN lam u eta)
    (Real.exp_pos _).le).trans (add_le_add (le_refl _) htailReal)

/-- A finite mesh anchored at the actual lower endpoint, never below it. -/
def overlapCenter (N : ℕ) (a : ℝ) (i : Fin (N+1)) : ℝ := max a ((i.val : ℝ)/N)

theorem overlapCenter_mem {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (i : Fin (N+1)) : overlapCenter N a i ∈ Icc a 1 := by
  refine ⟨le_max_left _ _, max_le ha.2 ?_⟩
  apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
  exact_mod_cast (Nat.le_of_lt_succ i.isLt)

/-- N+1 centers cover the full closed interval with open radius 1/N windows. -/
theorem exists_overlapCenter {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc a 1) : ∃ i : Fin (N+1), |t-overlapCenter N a i| < 1/(N : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht0 : 0 ≤ t := ha.1.trans ht.1
  let j : ℕ := Nat.ceil ((N : ℝ)*t)
  have hj : j ≤ N := Nat.ceil_le.mpr (by nlinarith [ht.2])
  let i : Fin (N+1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hjlo : (N : ℝ)*t ≤ (j : ℝ) := Nat.le_ceil _
  have hjhi : (j : ℝ) < (N : ℝ)*t+1 := Nat.ceil_lt_add_one (mul_nonneg hn.le ht0)
  have hgrid : t ≤ (j : ℝ)/N := (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hjlo)
  have hc : overlapCenter N a i = (j : ℝ)/N := max_eq_right (ht.1.trans hgrid)
  refine ⟨i, ?_⟩
  rw [hc, abs_of_nonpos (sub_nonpos.mpr hgrid), neg_sub]
  apply (lt_div_iff₀ hn).mpr
  have h := (div_mul_cancel₀ (j : ℝ) hn.ne')
  nlinarith

/-- The fixed-v mesh has at most 2N centers, each squared center at least v,
and covers [sqrt(v),1] with the exact manuscript window radius. -/
theorem overlap_mesh {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    Fintype.card (Fin (N+1)) ≤ 2*N ∧
    (∀ i : Fin (N+1), overlapCenter N (Real.sqrt v) i ∈ Icc (0 : ℝ) 1 ∧
      v ≤ (overlapCenter N (Real.sqrt v) i)^2) ∧
    ∀ t ∈ Icc (Real.sqrt v) 1, ∃ i : Fin (N+1),
      |t-overlapCenter N (Real.sqrt v) i| < 1/(N : ℝ) := by
  have ha : Real.sqrt v ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hv.2⟩
  refine ⟨by simp only [Fintype.card_fin]; omega, ?_, ?_⟩
  · intro i
    have hc := overlapCenter_mem hN ha i
    refine ⟨⟨ha.1.trans hc.1, hc.2⟩, ?_⟩
    have hh := (sq_le_sq₀ ha.1 (ha.1.trans hc.1)).mpr hc.1
    simpa only [Real.sq_sqrt hv.1] using hh
  · intro t ht
    exact exists_overlapCenter hN ha ht

/-- The deterministic low-overlap/high-overlap split for an arbitrary finite
cover. Only the high-overlap region [sqrt(v),1] must be covered. -/
theorem overlap_power_le_cover {N r : ℕ} {ι : Type*} [Fintype ι]
    (centers : ι → ℝ) (eta : ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hcover : ∀ t ∈ Icc (Real.sqrt v) 1, ∃ i, |t-centers i| < eta)
    (z : Model.Vector N × Model.Vector N) (hz : ‖z.1‖ = 1 ∧ ‖z.2‖ = 1) :
    (inner ℝ z.1 z.2)^(2*r) ≤ v^r+
      ∑ i, (Coupled.pairWindow N (centers i) eta).indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  have habs : |inner ℝ z.1 z.2| ≤ 1 := by
    simpa only [hz.1, hz.2, one_mul] using abs_real_inner_le_norm z.1 z.2
  have hnonneg (i : ι) : 0 ≤
      (Coupled.pairWindow N (centers i) eta).indicator (fun _ ↦ (1 : ℝ)) z := by
    by_cases hi : z ∈ Coupled.pairWindow N (centers i) eta <;> simp only [indicator_apply, hi, ite_true, ite_false] <;> norm_num
  have hsum0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hnonneg i)
  by_cases hlow : (inner ℝ z.1 z.2)^2 ≤ v
  · have hh := pow_le_pow_left₀ (sq_nonneg (inner ℝ z.1 z.2)) hlow r
    rw [← pow_mul] at hh
    exact hh.trans (le_add_of_nonneg_right hsum0)
  · have htlo : Real.sqrt v ≤ |inner ℝ z.1 z.2| := by
      have hs := Real.sq_sqrt hv
      have ha := abs_nonneg (inner ℝ z.1 z.2)
      have hsq := sq_abs (inner ℝ z.1 z.2)
      have hsn := Real.sqrt_nonneg v
      nlinarith
    obtain ⟨i, hi⟩ := hcover |inner ℝ z.1 z.2| ⟨htlo, habs⟩
    have hwin : z ∈ Coupled.pairWindow N (centers i) eta := by
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hi
      exact ⟨by linarith, by linarith⟩
    have hsum1 : 1 ≤ ∑ j, (Coupled.pairWindow N (centers j) eta).indicator (fun _ ↦ (1 : ℝ)) z := by
      have hh := Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
      simpa only [indicator_of_mem hwin] using hh
    have hpow : (inner ℝ z.1 z.2)^(2*r) ≤ 1 := by
      exact (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) habs)
    exact hpow.trans (hsum1.trans (le_add_of_nonneg_left (pow_nonneg hv r)))

/-- The actual fixed-disorder replica moment obeys the finite overlap cover. -/
theorem replicaMoment_le_cover {N r : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N (2*r))
    (centers : ι → ℝ) (eta : ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hcover : ∀ t ∈ Icc (Real.sqrt v) 1, ∃ i, |t-centers i| < eta) :
    replicaMoment N (2*r) lam w ≤ v^r+∑ i, windowProbability N (2*r) lam (centers i) eta w := by
  classical
  have := thermalGibbs_probability hN lam w
  let ν := (thermalGibbs N (2*r) lam w).prod (thermalGibbs N (2*r) lam w)
  have hunit : ∀ᵐ z ∂ν, ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 :=
    (Measure.quasiMeasurePreserving_fst.ae (thermalGibbs_unit_ae hN lam w)).and
      (Measure.quasiMeasurePreserving_snd.ae (thermalGibbs_unit_ae hN lam w))
  have hR : Integrable (fun z : Model.Vector N × Model.Vector N ↦ (inner ℝ z.1 z.2)^(2*r)) ν := by
    apply Integrable.of_bound (continuous_inner.pow (2*r)).aestronglyMeasurable 1
    filter_upwards [hunit] with z hz
    rw [Real.norm_eq_abs, abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    simpa only [hz.1, hz.2, one_mul] using abs_real_inner_le_norm z.1 z.2
  have hwin (i : ι) : Integrable
      ((Coupled.pairWindow N (centers i) eta).indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator (PairGibbsProofs.pairWindow_measurableSet N (centers i) eta)
  have hpoint : ∀ᵐ z ∂ν, (inner ℝ z.1 z.2)^(2*r) ≤ v^r+
      ∑ i, (Coupled.pairWindow N (centers i) eta).indicator (fun _ ↦ (1 : ℝ)) z :=
    hunit.mono (fun z hz ↦ overlap_power_le_cover centers eta hv hcover z hz)
  have hsum := integrable_finsetSum Finset.univ (fun i _ ↦ hwin i)
  have H := integral_mono_ae hR ((integrable_const (v^r)).add hsum) hpoint
  simp only [Pi.add_apply] at H
  rw [integral_add (integrable_const (v^r)) hsum, integral_const, probReal_univ, one_smul,
    integral_finsetSum Finset.univ (fun i _ ↦ hwin i)] at H
  simpa only [integral_indicator_const (1 : ℝ), PairGibbsProofs.pairWindow_measurableSet,
    smul_eq_mul, mul_one, ν, windowProbability, replicaMoment] using H

/-- Averaging the actual finite cover is justified by bounded Gibbs window
probabilities and the already proved replica integrability. -/
theorem replicaMean_le_cover {N r : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0 < N) (lam : ℝ) (centers : ι → ℝ) (eta : ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hm : ∀ i, Coupled.windowMass N (centers i) eta ≠ 0)
    (hcover : ∀ t ∈ Icc (Real.sqrt v) 1, ∃ i, |t-centers i| < eta) :
    replicaMean N (2*r) lam ≤ v^r+
      ∑ i, ∫ w, windowProbability N (2*r) lam (centers i) eta w ∂Model.noiseLaw N (2*r) := by
  classical
  have hi (i : ι) : Integrable (windowProbability N (2*r) lam (centers i) eta)
      (Model.noiseLaw N (2*r)) := by
    apply Integrable.of_bound (windowProbability_continuous hN lam (centers i) eta (hm i)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (windowProbability_nonneg _ _ _ _ _ _)]
      exact windowProbability_le_one hN lam (centers i) eta w)
  have hsum := integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  have H := integral_mono (replicaMoment_integrable (k := 2*r) hN lam)
    ((integrable_const (v^r)).add hsum)
      (fun w ↦ replicaMoment_le_cover hN lam w centers eta hv hcover)
  simp only [Pi.add_apply] at H
  rw [integral_add (integrable_const (v^r)) hsum, integral_const, probReal_univ, one_smul,
    integral_finsetSum Finset.univ (fun i _ ↦ hi i)] at H
  exact H

/-- Genuine finite mean gaps on the correctly anchored mesh imply an actual
replica-moment bound. This is not an unconditional asymptotic replica rate. -/
theorem replicaMean_le_of_mesh_gaps {N r : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    {v b : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hb : 0 < b)
    (hgap : ∀ i : Fin (N+1),
      Coupled.meanPairFreeEnergy N (2*r) lam (overlapCenter N (Real.sqrt v) i) (1/(N : ℝ))-
        2*Coupled.meanNullFE N (2*r) lam ≤ -2*b) :
    replicaMean N (2*r) lam ≤ v^r+(N+1 : ℕ)*
      (Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*lam^2))) := by
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
    _ ≤ ∑ i : Fin (N+1), (Real.exp (-(N : ℝ)*b)+2*Real.exp (-(N : ℝ)*b^2/(32*lam^2))) :=
      Finset.sum_le_sum (fun i _ ↦ expected_windowProbability_le_of_gap hNp lam _ _ (hm i) hb (hgap i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end TensorPCA.ReplicaMeshProofs
