-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationChannelProofs
public import TensorPCA.GaussianRSNormalizationProofs
public import TensorPCA.LimitTools

/-! Exact scalar normalization and the two-index passage from finite-alphabet free-energy limits to the unordered Gaussian-prior free-energy limit.
The finite-alphabet convergence theorems remain explicit proof parameters;
quantization does not supply the independent finite-prior replica-symmetric
theorem. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationLimitProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianPriorTransferProofs
open GaussianFinitePriorApproximationAlphabetProofs
open GaussianFinitePriorApproximationScalarProofs
open GaussianFinitePriorApproximationChannelProofs
open FinitePriorChannelProofs GaussianRSNormalizationProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

def compactScalarValue {S : Type*} [MeasurableSpace S]
    (p : Measure S) (a : S → ℝ) (k : ℕ) (gamma : ℝ) : ℝ :=
  sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1)

/-- The scalar channel KL is the actual planted Gaussian scalar log-partition,
including its full quadratic signal penalty. -/
theorem gaussian_scalarFreeEnergy_eq {a : ℝ} (ha : 0 ≤ a) :
    mixtureFreeEnergy (stdGaussian ℝ) (fun x : ℝ ↦ Real.sqrt a*x) =
      ∫ z, GaussianScalarProofs.scalarLogPartition a z
        ∂(stdGaussian ℝ).prod (stdGaussian ℝ) := by
  rw [GaussianTwoChannelFreeEnergyProofs.mixtureFreeEnergy_eq_integral_experiment
    (stdGaussian ℝ) (fun x : ℝ ↦ Real.sqrt a*x) (by fun_prop)]
  apply integral_congr_ae
  exact .of_forall fun z ↦ by
    unfold mixtureLikelihood mixtureWeight GaussianScalarProofs.scalarLogPartition
      GaussianScalarProofs.scalarNormalizer GaussianScalarProofs.scalarField
    dsimp only
    congr 1
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      dsimp only
      apply congrArg Real.exp
      simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ha]
      ring_nf
      rw [Real.sq_sqrt ha]
      ring

theorem gaussian_scalarPotential_eq {k : ℕ} (hk : 1 ≤ k) {gamma q : ℝ}
    (hgamma : 0 ≤ gamma) (hq : 0 ≤ q) :
    scalarPotential (stdGaussian ℝ) id k gamma q = gaussianRSPotential k gamma q := by
  unfold scalarPotential gaussianRSPotential
  simp only [id_eq]
  rw [gaussian_scalarFreeEnergy_eq (by positivity)]
  have hcast : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
  rw [hcast]
  ring

theorem gaussian_scalarPotential_continuousOn (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    ContinuousOn (scalarPotential (stdGaussian ℝ) id k gamma) (Icc (0 : ℝ) 1) := by
  apply ((continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (1/2 : ℝ)) (Icc (0 : ℝ) 1)).mul
    (ScalarPhiProofs.continuousOn_phi k hk (Real.sqrt gamma))).congr
  intro q hq
  rw [gaussian_scalarPotential_eq (by omega) hgamma hq.1,
    gaussianRSPotential_eq_phi k hgamma hq.1]
  rfl

theorem gaussian_scalarPotential_bddAbove (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    BddAbove (scalarPotential (stdGaussian ℝ) id k gamma '' Icc (0 : ℝ) 1) :=
  (isCompact_Icc.image_of_continuousOn (gaussian_scalarPotential_continuousOn k hk hgamma)).bddAbove

theorem bddAbove_image_of_uniform_sub_bound {s : Set ℝ} {f g : ℝ → ℝ} {r : ℝ}
    (hf : BddAbove (f '' s)) (hfg : ∀ x ∈ s, |f x-g x| ≤ r) : BddAbove (g '' s) := by
  obtain ⟨M,hM⟩ := hf
  refine ⟨M+r,?_⟩
  rintro y ⟨x,hx,rfl⟩
  have h1 := hM (mem_image_of_mem f hx)
  have h2 := (abs_le.mp (hfg x hx)).1
  linarith

theorem abs_sSup_image_sub_le {s : Set ℝ} {f g : ℝ → ℝ} {r : ℝ}
    (hs : s.Nonempty) (hf : BddAbove (f '' s)) (hg : BddAbove (g '' s))
    (hfg : ∀ x ∈ s, |f x-g x| ≤ r) : |sSup (f '' s)-sSup (g '' s)| ≤ r := by
  apply abs_le.mpr
  constructor
  · have H : sSup (g '' s) ≤ sSup (f '' s)+r := by
      apply csSup_le (hs.image g)
      rintro y ⟨x,hx,rfl⟩
      have h1 := le_csSup hf (mem_image_of_mem f hx)
      have h2 := (abs_le.mp (hfg x hx)).1
      linarith
    linarith
  · have H : sSup (f '' s) ≤ sSup (g '' s)+r := by
      apply csSup_le (hs.image f)
      rintro y ⟨x,hx,rfl⟩
      have h1 := le_csSup hg (mem_image_of_mem g hx)
      have h2 := (abs_le.mp (hfg x hx)).2
      linarith
    linarith

theorem finite_scalarPotential_bddAbove (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (j : ℕ) :
    BddAbove (scalarPotential (liftedGaussianPrior j)
      (Subtype.val : QuantizedAlphabet j → ℝ) k gamma '' Icc (0 : ℝ) 1) :=
  bddAbove_image_of_uniform_sub_bound (gaussian_scalarPotential_bddAbove k hk hgamma)
    (fun _ hq ↦ lifted_scalarPotential_uniform_approx k hgamma j hq)

theorem compactScalarValue_uniform_approx (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (j : ℕ) :
    |compactScalarValue (stdGaussian ℝ) id k gamma-
      compactScalarValue (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) k gamma| ≤
        scalarApproximationError k gamma j := by
  exact abs_sSup_image_sub_le (nonempty_Icc.mpr (by norm_num))
    (gaussian_scalarPotential_bddAbove k hk hgamma) (finite_scalarPotential_bddAbove k hk hgamma j)
    (fun _ hq ↦ lifted_scalarPotential_uniform_approx k hgamma j hq)

theorem finite_compactScalarValue_tendsto (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    Tendsto (fun j ↦ compactScalarValue (liftedGaussianPrior j)
      (Subtype.val : QuantizedAlphabet j → ℝ) k gamma) atTop
      (𝓝 (compactScalarValue (stdGaussian ℝ) id k gamma)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun j ↦ abs_nonneg _) _ (scalarApproximationError_tendsto k gamma)
  intro j
  rw [abs_sub_comm]
  exact compactScalarValue_uniform_approx k hk hgamma j

/-- Actual finite-alphabet replica-symmetric limits, first at fixed quantizer,
give the actual Gaussian unordered-channel limit after sending the quantizer
resolution to infinity. This reduction assumes no Gaussian value limit. -/
theorem unordered_gaussian_limit_of_finiteAlphabet_limits (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hfinite : ∀ j : ℕ, Tendsto
      (fun N ↦ freeEnergy (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma)
      atTop (𝓝 (compactScalarValue (liftedGaussianPrior j)
        (Subtype.val : QuantizedAlphabet j → ℝ) k gamma))) :
    Tendsto (fun N ↦ TensorOrbitAggregationProofs.unorderedPriorFreeEnergy N k gamma)
      atTop (𝓝 (compactScalarValue (stdGaussian ℝ) id k gamma)) := by
  let v := fun j ↦ compactScalarValue (liftedGaussianPrior j)
    (Subtype.val : QuantizedAlphabet j → ℝ) k gamma
  let e := tensorApproximationError k gamma
  apply LimitTools.tendsto_of_eventual_envelopes
    (lo := fun j N ↦ freeEnergy (liftedGaussianPrior j)
      (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma-e j)
    (hi := fun j N ↦ freeEnergy (liftedGaussianPrior j)
      (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma+e j)
    (a := fun j ↦ v j-e j) (b := fun j ↦ v j+e j)
  · intro j
    exact (hfinite j).sub_const (e j)
  · intro j
    exact (hfinite j).add_const (e j)
  · intro j
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have H := abs_le.mp (lifted_unordered_freeEnergy_uniform_approx (by omega : 0 < N)
      (by omega : 1 ≤ k) hgamma j)
    dsimp [e]
    constructor <;> linarith
  · simpa only [sub_zero] using
      (finite_compactScalarValue_tendsto k hk hgamma).sub (tensorApproximationError_tendsto k gamma)
  · simpa only [add_zero] using
      (finite_compactScalarValue_tendsto k hk hgamma).add (tensorApproximationError_tendsto k gamma)

theorem gaussian_compactScalarValue_eq_bayesianLimit (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    compactScalarValue (stdGaussian ℝ) id k gamma = Statistical.bayesianLimit k gamma := by
  have hlam := Real.sqrt_pos.mpr hgamma
  have hq := (ScalarPhiProofs.qStar_isScalarMaximizer k hk hlam.le).1
  have hg : IsGreatest (scalarPotential (stdGaussian ℝ) id k gamma '' Icc (0 : ℝ) 1)
      ((1/2 : ℝ)*Scalar.f k (Real.sqrt gamma) (Scalar.qStar k (Real.sqrt gamma))) := by
    refine ⟨⟨_,⟨hq.1,hq.2.le⟩,?_⟩,?_⟩
    · rw [gaussian_scalarPotential_eq (by omega) hgamma.le hq.1,
        gaussianRSPotential_eq_phi k hgamma.le hq.1,
        ScalarPhiProofs.phi_qStar_eq_f k hk hlam]
    · rintro y ⟨q,hq',rfl⟩
      rw [gaussian_scalarPotential_eq (by omega) hgamma.le hq'.1,
        gaussianRSPotential_eq_phi k hgamma.le hq'.1]
      exact mul_le_mul_of_nonneg_left (ScalarPhiProofs.phi_le_qStar_f k hk hlam hq') (by norm_num)
  rw [compactScalarValue,hg.isLUB.csSup_eq ⟨_,hg.1⟩,Statistical.bayesianLimit,
    ScalarBayesianProofs.sSup_phi_eq_f_qStar k hk hlam]

theorem unordered_bayesian_limit_of_finiteAlphabet_limits (k : ℕ) (hk : 3 ≤ k)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hfinite : ∀ j : ℕ, Tendsto
      (fun N ↦ freeEnergy (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ) N k gamma)
      atTop (𝓝 (compactScalarValue (liftedGaussianPrior j)
        (Subtype.val : QuantizedAlphabet j → ℝ) k gamma))) :
    Tendsto (fun N ↦ TensorOrbitAggregationProofs.unorderedPriorFreeEnergy N k gamma)
      atTop (𝓝 (Statistical.bayesianLimit k gamma)) := by
  rw [← gaussian_compactScalarValue_eq_bayesianLimit k hk hgamma]
  exact unordered_gaussian_limit_of_finiteAlphabet_limits k hk hgamma.le hfinite

end
end TensorPCA.GaussianFinitePriorApproximationLimitProofs
