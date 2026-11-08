-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.ReplicaRateProofs
public import TensorPCA.TotalVariationProofs

/-! Null log-likelihood moments from the thermal rates. The
thermal exponent is negative, so the likelihood identity explicitly reflects
the Gaussian noise rather than silently changing the Hamiltonian convention. -/

@[expose] public section
namespace TensorPCA.NullLikelihoodRateProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

/-- Exact sign-aware relation between the actual likelihood and thermal
partition; the deterministic Gaussian density correction is retained. -/
theorem likelihoodRatio_eq_partition (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    Model.likelihoodRatio N k lam w = Real.exp (-(N : ℝ)*lam^2/2)*
      Model.partitionFunction N k lam (-w) := by
  unfold Model.likelihoodRatio Model.partitionFunction
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [← Real.exp_add]
  congr 1
  simp only [Model.hamiltonian, Model.score, inner_neg_right]
  ring

/-- The actual null log likelihood equals N times the reflected centered free
energy, with exactly the manuscript's likelihood normalization. -/
theorem nullLogLikelihood_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    Statistical.nullLogLikelihood N k lam w =
      (N : ℝ)*(Model.freeEnergy N k lam (-w)-lam^2/2) := by
  rw [Statistical.nullLogLikelihood, likelihoodRatio_eq_partition,
    Real.log_mul (Real.exp_ne_zero _)
      (FreeEnergyProofs.partitionFunction_pos hN lam (-w)).ne', Real.log_exp, Model.freeEnergy]
  field_simp [Nat.cast_ne_zero.mpr hN.ne']
  ring

/-- Canonical Gaussian reflection preserves every measurable scalar integral. -/
theorem integral_noise_neg {N k : ℕ} (F : Model.Tensor N k → ℝ) (hF : Continuous F) :
    (∫ w, F (-w) ∂Model.noiseLaw N k) = ∫ w, F w ∂Model.noiseLaw N k := by
  let T : Model.Tensor N k ≃ₗᵢ[ℝ] Model.Tensor N k := LinearIsometryEquiv.neg ℝ
  have hmap : (Model.noiseLaw N k).map T = Model.noiseLaw N k := stdGaussian_map T
  have H := integral_map (μ := Model.noiseLaw N k) T.continuous.measurable.aemeasurable
    hF.aestronglyMeasurable
  rw [hmap] at H
  exact H.symm

/-- The finite actual null log-likelihood second moment is exactly the physical
N²-scaled bias plus variance, with no Gaussian sign convention assumed. -/
theorem nullLogSecondMoment_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Statistical.nullLogSecondMoment N k lam = (N : ℝ)^2*
      (Coupled.varNullFE N k lam+(Coupled.meanNullFE N k lam-lam^2/2)^2) := by
  unfold Statistical.nullLogSecondMoment
  simp_rw [nullLogLikelihood_eq hN lam, mul_pow]
  rw [integral_const_mul]
  have hc : Continuous (fun w : Model.Tensor N k ↦ (Model.freeEnergy N k lam w-lam^2/2)^2) :=
    ((FreeEnergyProofs.freeEnergy_contDiff hN lam).continuous.sub continuous_const).pow 2
  rw [integral_noise_neg _ hc, ReplicaRateProofs.freeEnergy_sq_deviation_eq_variance_bias hN lam (lam^2/2)]

/-- Actual null log-likelihood L2 decay at its physical N exponent. The only
physical theorem premise is the coupled trial/interpolation bound. -/
theorem nullLogSecondMoment_le_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 4 ≤ k) (heven : Even k) (lam : ℝ)
    (hlam : 0 ≤ lam) (hsub : lam < Scalar.lambdaC k) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      Statistical.nullLogSecondMoment N k lam ≤ C*(N : ℝ)^((1 : ℝ)-(k : ℝ)/4+eps) := by
  obtain ⟨Cm,hCm,hm⟩ := ReplicaRateProofs.meanFreeEnergyRate_of_trialBound htrial
    k hk heven lam hlam hsub (eps/2) (half_pos heps)
  obtain ⟨Cv,hCv,hv⟩ := ReplicaRateProofs.varianceFreeEnergyRate_of_trialBound htrial
    k hk heven lam hlam hsub eps heps
  let C := Cv+Cm^2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hNp
  let p : ℝ := (k : ℝ)/4+1-eps
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
  calc
    _ = (N : ℝ)^2*(Coupled.varNullFE N k lam+(Coupled.meanNullFE N k lam-lam^2/2)^2) :=
      nullLogSecondMoment_eq hNp lam
    _ ≤ (N : ℝ)^2*(C/(N : ℝ)^p) := mul_le_mul_of_nonneg_left hSecond (sq_nonneg _)
    _ = _ := by
      have he : (1 : ℝ)-(k : ℝ)/4+eps = (2 : ℝ)-p := by dsimp [p]; ring
      rw [he, Real.rpow_sub hn (2 : ℝ) p, Real.rpow_two]
      ring

/-- The null log-likelihood second moment vanishes below threshold for
even orders k≥6, conditional only on interpolation. -/
theorem nullLogSecondMomentLimit_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 6 ≤ k) (heven : Even k) (lam : ℝ)
    (hlam : 0 ≤ lam) (hsub : lam < Scalar.lambdaC k) :
    Statistical.NullLogSecondMomentLimit k lam := by
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  let eps : ℝ := ((k : ℝ)-4)/8
  have heps : 0 < eps := by dsimp [eps]; linarith
  obtain ⟨C,_,hbound⟩ := nullLogSecondMoment_le_of_trialBound htrial k (by omega) heven lam hlam hsub eps heps
  let s : ℝ := (1 : ℝ)-(k : ℝ)/4+eps
  have hs : s < 0 := by dsimp [s,eps]; linarith
  have hd : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ by exact_mod_cast (Nat.le_succ n))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)^s) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_neg] using (tendsto_rpow_neg_atTop (neg_pos.mpr hs)).comp hd
  unfold Statistical.NullLogSecondMomentLimit
  apply squeeze_zero (fun n ↦ integral_nonneg (fun w ↦ sq_nonneg (Statistical.nullLogLikelihood (n+1) k lam w)))
    (fun n ↦ hbound (n+1) (by omega))
  simpa only [mul_zero] using hpow.const_mul C

/-- The subcritical testing limit follows from finite
likelihood-to-TV control and the coupled trial theorem. -/
theorem testingDistance_subcritical_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 6 ≤ k) (heven : Even k) (lam : ℝ)
    (hlam : 0 ≤ lam) (hsub : lam < Scalar.lambdaC k) :
    Tendsto (fun n : ℕ ↦ Model.testingDistance (n+1) k lam) atTop (𝓝 0) :=
  Statistical.testingDistance_tendsto_zero_of_logSecondMoment
    (TotalVariationProofs.finiteTVMomentBound k lam)
    (nullLogSecondMomentLimit_of_trialBound htrial k hk heven lam hlam hsub)

end
end TensorPCA.NullLikelihoodRateProofs
