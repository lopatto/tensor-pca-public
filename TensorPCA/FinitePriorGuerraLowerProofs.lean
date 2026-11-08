-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorRevealedInterpolationProofs
public import TensorPCA.FinitePriorScalarEndpointProofs
public import TensorPCA.GaussianZeroChannelProofs
public import TensorPCA.FiniteRevealFreeEnergyProofs

/-! # Removing the reveal perturbation from the finite Guerra lower bound -/
@[expose] public section

namespace TensorPCA.FinitePriorGuerraLowerProofs

open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianTwoChannelFreeEnergyProofs
open GaussianZeroChannelProofs FinitePriorChannelProofs FinitePriorScalarEndpointProofs
open FinitePriorRevealedInterpolationProofs FiniteRevealProofs FiniteRevealAveragingProofs
open FiniteRevealFreeEnergyProofs BayesianPinningProofs BayesianPinningVarianceProofs

attribute [local instance] posterior_probability

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N k : ℕ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def revealedSingleChannel (mu : Measure (Fin N → S)) (F : (Fin N → S) → E)
    (delta : ℝ) : ℝ :=
  uniformAverage Finset.univ delta (fun mask ↦ ∫ x, mixtureFreeEnergy (posterior mu mask x) F/(N:ℝ) ∂mu)

theorem revealedSingleChannel_bounds (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (F : (Fin N → S) → E) (hN : 0 < N) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    mixtureFreeEnergy mu F/(N:ℝ) ≤ revealedSingleChannel mu F delta ∧
    revealedSingleChannel mu F delta ≤ mixtureFreeEnergy mu F/(N:ℝ)+delta*Real.log (Fintype.card S) := by
  obtain ⟨K,_,hK⟩ := finite_signal_bound F
  have hc := normalized_uniform_revealFreeEnergyCost_bounds mu F (measurable_of_finite _)
    (.of_forall hK) hN hd0 hd1
  have hp := uniformInterval_probability hd0
  let values := fun mask ↦ ∫ x, mixtureFreeEnergy (posterior mu mask x) F ∂mu
  have hcost : uniformAverage Finset.univ delta (revealFreeEnergyCost mu F) =
      uniformAverage Finset.univ delta values-mixtureFreeEnergy mu F := by
    unfold uniformAverage revealFreeEnergyCost
    simp_rw [BayesianPinningVarianceProofs.average_sub, BayesianPinningVarianceProofs.average_const]
    rw [integral_sub ((memLp_uniformInterval (RevealPolynomialProofs.average_continuous _ _) hd0 1).integrable le_rfl)
      (integrable_const _), integral_const, probReal_univ, one_smul]
  have hsingle : revealedSingleChannel mu F delta = uniformAverage Finset.univ delta values/(N:ℝ) := by
    unfold revealedSingleChannel
    simp_rw [integral_div]
    have h := uniformAverage_const_mul Finset.univ delta values ((N:ℝ)⁻¹)
    simpa only [div_eq_mul_inv, mul_comm] using h
  change 0 ≤ uniformAverage Finset.univ delta (revealFreeEnergyCost mu F)/(N:ℝ) ∧
    uniformAverage Finset.univ delta (revealFreeEnergyCost mu F)/(N:ℝ) ≤ delta*Real.log (Fintype.card S) at hc
  rw [hcost, sub_div] at hc
  rw [hsingle]
  constructor <;> linarith [hc.1,hc.2]

theorem revealedInterpolation_zero (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (a : S → ℝ) (k : ℕ) (gamma m delta : ℝ) :
    revealedInterpolation mu a k gamma m delta 0 =
      revealedSingleChannel mu (scalarSignal a N k gamma m) delta := by
  unfold revealedInterpolation revealedSingleChannel
  simp only [Real.sqrt_zero, zero_smul, sub_zero, Real.sqrt_one, one_smul]
  simp_rw [twoChannelFreeEnergy_zero_left _ _ (measurable_of_finite _)]

theorem revealedInterpolation_one (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (a : S → ℝ) (k : ℕ) (gamma m delta : ℝ) :
    revealedInterpolation mu a k gamma m delta 1 =
      revealedSingleChannel mu (tensorSignal a N k gamma) delta := by
  unfold revealedInterpolation revealedSingleChannel
  simp only [Real.sqrt_one, one_smul, sub_self, Real.sqrt_zero, zero_smul]
  simp_rw [twoChannelFreeEnergy_zero_right _ _ (measurable_of_finite _)]

theorem finite_guerra_lower_bound (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (hN : 0 < N) (hk : 0 < k) {K gamma m delta : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K)
    (hgamma : 0 ≤ gamma) (hm : 0 ≤ m) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    scalarPotential p a k gamma m-
      (gamma/2)*((k : ℝ)*((K^2)^(k-1)+m^(k-1))*
        Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))+
        (k : ℝ)^2*K^(2*k)/(N : ℝ))-delta*Real.log (Fintype.card S) ≤
      freeEnergy p a N k gamma := by
  have he := revealedInterpolation_endpoint_lower_bound (configurationPrior p N) a hN hk hK ha hgamma hm hd0 hd1
  rw [revealedInterpolation_zero, revealedInterpolation_one] at he
  have hs := (revealedSingleChannel_bounds (configurationPrior p N) (scalarSignal a N k gamma m) hN hd0 hd1).1
  have ht := (revealedSingleChannel_bounds (configurationPrior p N) (tensorSignal a N k gamma) hN hd0 hd1).2
  rw [normalized_scalarSignal_freeEnergy p a hN k gamma m] at hs
  have hk' : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold scalarPotential freeEnergy
  rw [hk']
  linarith

/-- The actual bounded finite-prior free energy eventually lies above every
fixed nonnegative scalar trial, up to any prescribed positive error. -/
theorem finite_guerra_eventual_lower (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (hk : 0 < k) {gamma m : ℝ} (hgamma : 0 ≤ gamma) (hm : 0 ≤ m)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in Filter.atTop, scalarPotential p a k gamma m-epsilon ≤ freeEnergy p a N k gamma := by
  obtain ⟨K,hK,ha⟩ := finite_signal_bound a
  have ha' : ∀ s, |a s| ≤ K := by simpa only [Real.norm_eq_abs] using ha
  let C := (k : ℝ)*((K^2)^(k-1)+m^(k-1))
  let err : ℕ → ℝ := fun N ↦ (gamma/2)*
    (C*Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*(1/Real.sqrt N))))+
      (k : ℝ)^2*K^(2*k)/(N : ℝ))+(1/Real.sqrt N)*Real.log (Fintype.card S)
  have hn : Filter.Tendsto (fun n : ℕ ↦ (n:ℝ)+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n+1:ℕ)) Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using Real.tendsto_sqrt_atTop.comp hn
  have hz := ((GuerraPinningProofs.pinning_tensor_error_tendsto_zero
    (Real.log (Fintype.card S)) C K k).const_mul (gamma/2)).add
      ((hs.const_div_atTop 1).mul_const (Real.log (Fintype.card S)))
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    simpa only [err, mul_zero, zero_mul, add_zero] using hz
  have hev : ∀ᶠ N in Filter.atTop, err N < epsilon := (tendsto_order.1 herr).2 _ hepsilon
  filter_upwards [hev, Filter.eventually_gt_atTop (0:ℕ)] with N he hN
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : 0 < 1/Real.sqrt (N:ℝ) := div_pos zero_lt_one (Real.sqrt_pos.mpr hNp)
  have hd1 : 1/Real.sqrt (N:ℝ) ≤ 1 :=
    (div_le_one (Real.sqrt_pos.mpr hNp)).mpr (Real.one_le_sqrt.mpr hN1)
  have hb := finite_guerra_lower_bound p a hN hk hK ha' hgamma hm hd0 hd1
  change scalarPotential p a k gamma m-
    (gamma/2)*(C*Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*(1/Real.sqrt N))))+
      (k : ℝ)^2*K^(2*k)/(N : ℝ))-(1/Real.sqrt N)*Real.log (Fintype.card S) ≤ _ at hb
  dsimp only [err] at he
  linarith


end TensorPCA.FinitePriorGuerraLowerProofs
