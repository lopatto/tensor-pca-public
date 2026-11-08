-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealReplicaProofs
public import TensorPCA.GaussianZeroChannelProofs
public import TensorPCA.FiniteRevealAveragingProofs
public import TensorPCA.GuerraRemainderProofs

/-! Gaussian output/reveal transport for the nonlinear thermal replica
variance. The random posterior center stays inside the squared deviation. -/
@[expose] public section
namespace TensorPCA.GaussianRevealVarianceProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSideChannelProofs GaussianReplicaTransportProofs GaussianCombinedPosteriorProofs
open GaussianFiniteRevealProofs GaussianRevealTransportProofs GaussianZeroChannelProofs
open FiniteEntropyProofs FiniteRevealProofs FiniteRevealAveragingProofs PosteriorPairProofs
open BayesianPinningVarianceProofs GuerraRemainderProofs
open scoped RealInnerProductSpace ENNReal Classical
noncomputable section
attribute [local instance] condition_probability posterior_probability
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

theorem combinedPosteriorKernel_zero_left (mu : Measure Omega) [IsProbabilityMeasure mu]
    (B : Omega → D) (hB : Measurable B) (p : D × ℝ) :
    combinedPosteriorKernel mu (fun _ ↦ (0 : ℝ)) B p = posteriorKernel mu B p.1 := by
  rw [combinedPosteriorKernel, Kernel.withDensity_apply _
    (measurable_combinedPosteriorWeight mu (fun _ ↦ (0 : ℝ)) B measurable_const hB),
    Kernel.const_apply, posteriorKernel_apply mu B hB]
  congr 1
  funext x
  simp only [combinedPosteriorWeight, combinedLikelihood_zero_left, posteriorWeight,
    mixtureWeight, inner_zero_left, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_div, sub_self, Real.exp_zero, mul_one]

theorem pairObservationLaw_zero_left_map_fst (mu : Measure Omega) [IsProbabilityMeasure mu]
    (B : Omega → D) (hB : Measurable B) :
    (pairObservationLaw mu (fun _ ↦ (0 : ℝ)) B).map Prod.fst = mixtureLaw mu B := by
  have hobs : Measurable (fun z : (Omega × D) × ℝ ↦ (B z.1.1+z.1.2,(0 : ℝ)+z.2)) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk
      (measurable_const.add measurable_snd)
  have hsingle : Measurable (fun z : Omega × D ↦ B z.1+z.2) :=
    (hB.comp measurable_fst).add measurable_snd
  change (((mu.prod (stdGaussian D)).prod (stdGaussian ℝ)).map _).map Prod.fst =
    (mu.prod (stdGaussian D)).map _
  rw [Measure.map_map measurable_fst hobs]
  change (((mu.prod (stdGaussian D)).prod (stdGaussian ℝ)).map
    ((fun z : Omega × D ↦ B z.1+z.2) ∘ Prod.fst)) = _
  rw [← Measure.map_map hsingle measurable_fst, Measure.map_fst_prod]
  simp only [measure_univ, one_smul]

variable [Fintype Omega] [MeasurableSingletonClass Omega]

theorem posteriorKernel_condition {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (B : Omega → D) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (u : U) (y : D) :
    posteriorKernel (condition mu r u) B y = condition (posteriorKernel mu B y) r u := by
  have h := combinedPosteriorKernel_condition mu (fun _ ↦ (0 : ℝ)) B measurable_const hB r hr u (y,0)
  simpa only [combinedPosteriorKernel_zero_left _ B hB] using h

theorem integral_reveal_output_transport_single {U : Type*} [Fintype U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (B : Omega → D) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (F : U → D → ℝ)
    (hF : ∀ u, Measurable (F u)) {C : ℝ} (hFC : ∀ u y, |F u y| ≤ C) :
    (∫ x, ∫ y, F (r x) y ∂mixtureLaw (condition mu r (r x)) B ∂mu) =
      ∫ y, ∫ x, F (r x) y ∂posteriorKernel mu B y ∂mixtureLaw mu B := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hR : Measurable (fun y ↦ ∫ x, F (r x) y ∂posteriorKernel mu B y) := by
    simp_rw [integral_fintype Integrable.of_finite, smul_eq_mul]
    apply Finset.measurable_sum
    intro x _
    exact ((Kernel.measurable_coe _ (measurableSet_singleton x)).ennreal_toReal).mul (hF (r x))
  have htrans := integral_reveal_output_transport mu (fun _ ↦ (0 : ℝ)) B measurable_const hB r hr
    (fun u y ↦ F u y.1) (fun u ↦ (hF u).comp measurable_fst) (fun u y ↦ hFC u y.1)
  simp_rw [combinedPosteriorKernel_zero_left mu B hB] at htrans
  have hmap (u : U) : (∫ y : D × ℝ, F u y.1
      ∂pairObservationLaw (condition mu r u) (fun _ ↦ (0 : ℝ)) B) =
      ∫ y, F u y ∂mixtureLaw (condition mu r u) B := by
    rw [← pairObservationLaw_zero_left_map_fst (condition mu r u) B hB]
    exact (integral_map measurable_fst.aemeasurable (hF u).aestronglyMeasurable).symm
  simp_rw [hmap] at htrans
  rw [← pairObservationLaw_zero_left_map_fst mu B hB]
  exact htrans.trans (integral_map measurable_fst.aemeasurable hR.aestronglyMeasurable).symm

section Configuration
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N : ℕ}

theorem measurable_replicaVariance {Y : Type*} [MeasurableSpace Y]
    (kappa : Kernel Y (Fin N → S)) [IsMarkovKernel kappa] (a : S → ℝ) :
    Measurable (fun y ↦ replicaVariance (kappa y) a) := by
  simp_rw [replicaVariance_eq_pair_sum]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  have hpair : Measurable (fun y ↦ pairMoment (kappa y) a i j) :=
    (measurable_of_finite (fun x : Fin N → S ↦ a (x i)*a (x j))).stronglyMeasurable.integral_kernel.measurable
  have hcoord (l : Fin N) : Measurable (fun y ↦ coordinateMean (kappa y) a l) :=
    (measurable_of_finite (fun x : Fin N → S ↦ a (x l))).stronglyMeasurable.integral_kernel.measurable
  exact (hpair.pow_const 2).sub ((hcoord i).pow_const 2 |>.mul ((hcoord j).pow_const 2))

theorem replicaVariance_bounds (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) :
    0 ≤ replicaVariance q a ∧ replicaVariance q a ≤ 4*K^4 := by
  refine ⟨integral_nonneg (fun z ↦ sq_nonneg _),?_⟩
  have hb (z : (Fin N → S) × (Fin N → S)) :
      (overlap a z-meanOverlap q a)^2 ≤ 4*K^4 := by
    have hr := overlap_abs_le a hN hK ha z
    have hq := meanOverlap_le q a hN ha
    have hq0 := meanOverlap_nonneg q a
    have hd : |overlap a z-meanOverlap q a| ≤ 2*K^2 := by
      have hh := abs_sub (overlap a z) (meanOverlap q a)
      rw [abs_of_nonneg hq0] at hh
      linarith
    calc
      _ = |overlap a z-meanOverlap q a|^2 := (sq_abs _).symm
      _ ≤ (2*K^2)^2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
      _ = _ := by ring
  have h := integral_mono (μ := q.prod q) Integrable.of_finite (integrable_const (4*K^4)) hb
  simpa only [replicaVariance, integral_const, probReal_univ, one_smul] using h

theorem integral_reveal_variance_transport (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (B : (Fin N → S) → D) (hB : Measurable B) (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) (mask : Finset (Fin N)) :
    (∫ x, ∫ y, replicaVariance (posteriorKernel (posterior q mask x) B y) a
      ∂mixtureLaw (posterior q mask x) B ∂q) =
      ∫ y, ∫ x, replicaVariance (posterior (posteriorKernel q B y) mask x) a
        ∂posteriorKernel q B y ∂mixtureLaw q B := by
  have hk (u : Fin N → Unit ⊕ S) : IsMarkovKernel
      (posteriorKernel (condition q (observation mask) u) B) :=
    posteriorKernel_isMarkov _ B hB
  have h := integral_reveal_output_transport_single q B hB (observation mask) (measurable_of_finite _)
    (fun u y ↦ replicaVariance (posteriorKernel (condition q (observation mask) u) B y) a)
    (fun u ↦ measurable_replicaVariance _ a) (fun u y ↦ by
      have H := replicaVariance_bounds (posteriorKernel (condition q (observation mask) u) B y) a hN hK ha
      simpa only [abs_of_nonneg H.1] using H.2)
  simpa only [posterior, posteriorKernel_condition q B hB (observation mask) (measurable_of_finite _)] using h

theorem integrable_revealedVariance (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (B : (Fin N → S) → D) (hB : Measurable B) (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) (mask : Finset (Fin N)) :
    Integrable (fun y ↦ ∫ x, replicaVariance (posterior (posteriorKernel q B y) mask x) a
      ∂posteriorKernel q B y) (mixtureLaw q B) := by
  have : IsMarkovKernel (posteriorKernel q B) := posteriorKernel_isMarkov q B hB
  have : IsProbabilityMeasure (mixtureLaw q B) := mixtureLaw_probability q B hB
  have hk (x : Fin N → S) : IsMarkovKernel
      (posteriorKernel (condition q (observation mask) (observation mask x)) B) :=
    posteriorKernel_isMarkov _ B hB
  have hm : Measurable (fun y ↦ ∫ x, replicaVariance (posterior (posteriorKernel q B y) mask x) a
      ∂posteriorKernel q B y) := by
    simp_rw [posterior, ← posteriorKernel_condition q B hB (observation mask) (measurable_of_finite _),
      integral_fintype Integrable.of_finite, smul_eq_mul]
    apply Finset.measurable_sum
    intro x _
    exact ((Kernel.measurable_coe _ (measurableSet_singleton x)).ennreal_toReal).mul
      (measurable_replicaVariance _ a)
  apply Integrable.of_bound hm.aestronglyMeasurable (4*K^4)
  exact .of_forall fun y ↦ by
    have hb : ∀ᵐ x ∂posteriorKernel q B y,
        ‖replicaVariance (posterior (posteriorKernel q B y) mask x) a‖ ≤ 4*K^4 := .of_forall fun x ↦ by
      have H := replicaVariance_bounds (posterior (posteriorKernel q B y) mask x) a hN hK ha
      simpa only [Real.norm_eq_abs, abs_of_nonneg H.1] using H.2
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- Actual Gaussian observations of a revealed prior retain the finite pinning
bound. No concentration of the random posterior overlap center is assumed. -/
theorem actual_gaussian_pinning_variance_bound (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (B : (Fin N → S) → D) (hB : Measurable B) (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ y,
      replicaVariance (posteriorKernel (posterior q mask x) B y) a
      ∂mixtureLaw (posterior q mask x) B ∂q) ≤
      4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)) := by
  have : IsMarkovKernel (posteriorKernel q B) := posteriorKernel_isMarkov q B hB
  have : IsProbabilityMeasure (mixtureLaw q B) := mixtureLaw_probability q B hB
  simp_rw [integral_reveal_variance_transport q B hB a hN hK ha]
  rw [uniformAverage_integral_comm Finset.univ hd0 (mixtureLaw q B) _
    (fun mask ↦ integrable_revealedVariance q B hB a hN hK ha mask)]
  have hi : Integrable (fun y ↦ uniformAverage Finset.univ delta
      (fun mask ↦ ∫ x, replicaVariance (posterior (posteriorKernel q B y) mask x) a
        ∂posteriorKernel q B y)) (mixtureLaw q B) := by
    simp_rw [uniformAverage_eq_sum Finset.univ hd0]
    exact integrable_finsetSum _ (fun mask _ ↦
      (integrable_revealedVariance q B hB a hN hK ha mask).const_mul _)
  have h := integral_mono_ae hi
    (integrable_const (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta))))
    (.of_forall fun y ↦ finite_pinning_replica_variance_bound (posteriorKernel q B y) a hN hK ha hd0 hd1)
  simpa only [integral_const, probReal_univ, one_smul] using h


end Configuration
end
end TensorPCA.GaussianRevealVarianceProofs
