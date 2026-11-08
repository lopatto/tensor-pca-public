-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.KLBoundProofs
public import Mathlib.MeasureTheory.Integral.Prod

/-! Finite posterior marginals and their product-replica overlaps.
The posterior law is arbitrary; its coordinates need not be independent. -/
@[expose] public section
namespace TensorPCA.PosteriorPairProofs
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Configuration (S : Type*) (N : ℕ) := Fin N → S

theorem average_sqrt_le_sqrt_average {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hm : 0 < Fintype.card ι) :
    (∑ i, Real.sqrt (r i))/(Fintype.card ι : ℝ) ≤
      Real.sqrt ((∑ i, r i)/(Fintype.card ι : ℝ)) := by
  have hc : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ Real.sqrt (r i)) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
  have hs : (∑ i, (Real.sqrt (r i))^2) = ∑ i, r i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (hr i)
  rw [hs] at hcs
  have hstep : ((∑ i, Real.sqrt (r i))/(Fintype.card ι : ℝ))^2 ≤
      (∑ i, r i)/(Fintype.card ι : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    have heq : (∑ i, r i)/(Fintype.card ι : ℝ)*(Fintype.card ι : ℝ)^2 =
        (∑ i, r i)*(Fintype.card ι : ℝ) := by
      field_simp [hc.ne']
    rw [heq]
    exact hcs
  have ha : 0 ≤ (∑ i, r i)/(Fintype.card ι : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ ↦ hr i) hc.le
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg ((∑ i, r i)/(Fintype.card ι : ℝ))]

section Finite
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (Configuration S N)) [IsProbabilityMeasure q]

def coordinateLaw (i : Fin N) : Measure S := q.map (fun x ↦ x i)

def pairLaw (i j : Fin N) : Measure (S × S) := q.map (fun x ↦ (x i,x j))

def pairInformation (i j : Fin N) : ℝ≥0∞ :=
  klDiv (pairLaw q i j) ((coordinateLaw q i).prod (coordinateLaw q j))

def averagePairInformation : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, (pairInformation q i j).toReal)/(N : ℝ)^2

def coordinateMean (a : S → ℝ) (i : Fin N) : ℝ := ∫ x, a (x i) ∂q

def pairMoment (a : S → ℝ) (i j : Fin N) : ℝ := ∫ x, a (x i)*a (x j) ∂q

def meanOverlap (a : S → ℝ) : ℝ :=
  (∑ i : Fin N, (coordinateMean q a i)^2)/(N : ℝ)

def overlap (a : S → ℝ) (z : Configuration S N × Configuration S N) : ℝ :=
  (∑ i : Fin N, a (z.1 i)*a (z.2 i))/(N : ℝ)

def replicaVariance (a : S → ℝ) : ℝ :=
  ∫ z, (overlap a z-meanOverlap q a)^2 ∂q.prod q

instance coordinateLaw_probability (i : Fin N) : IsProbabilityMeasure (coordinateLaw q i) := by
  unfold coordinateLaw
  infer_instance

instance pairLaw_probability (i j : Fin N) : IsProbabilityMeasure (pairLaw q i j) := by
  unfold pairLaw
  infer_instance

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem pairLaw_map_fst (i j : Fin N) : (pairLaw q i j).map Prod.fst = coordinateLaw q i := by
  rw [pairLaw, coordinateLaw, Measure.map_map measurable_fst
    (show Measurable (fun x : Configuration S N ↦ (x i,x j)) by fun_prop)]
  rfl

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem pairLaw_map_snd (i j : Fin N) : (pairLaw q i j).map Prod.snd = coordinateLaw q j := by
  rw [pairLaw, coordinateLaw, Measure.map_map measurable_snd
    (show Measurable (fun x : Configuration S N ↦ (x i,x j)) by fun_prop)]
  rfl

/-- On a finite space, null singletons determine absolute continuity. -/
theorem finite_absolutelyContinuous_of_singleton {T : Type*} [Fintype T] [MeasurableSpace T]
    (μ ν : Measure T) (hs : ∀ x, ν {x} = 0 → μ {x} = 0) : μ ≪ ν := by
  intro A hA
  have hcover : A = ⋃ x : A, ({x.1} : Set T) := by
    ext x
    simp
  rw [hcover]
  apply measure_iUnion_null
  intro x
  exact hs x.1 (measure_mono_null (singleton_subset_iff.mpr x.2) hA)

omit [IsProbabilityMeasure q] in
/-- A positive joint atom has positive marginals, so actual pair information
is finite even when some alphabet atoms have posterior probability zero. -/
theorem pairLaw_absolutelyContinuous_product (i j : Fin N) :
    pairLaw q i j ≪ (coordinateLaw q i).prod (coordinateLaw q j) := by
  apply finite_absolutelyContinuous_of_singleton
  intro p hp
  have hset : ({p} : Set (S × S)) = {p.1} ×ˢ {p.2} := by
    rcases p with ⟨s,t⟩
    exact singleton_prod_singleton.symm
  have hprod : coordinateLaw q i {p.1}*coordinateLaw q j {p.2} = 0 := by
    rwa [hset, Measure.prod_prod] at hp
  rcases mul_eq_zero.mp hprod with hi | hj
  · apply measure_mono_null (show {p} ⊆ Prod.fst ⁻¹' {p.1} from fun x hx ↦ by
      simpa only [mem_preimage, mem_singleton_iff] using congrArg Prod.fst (mem_singleton_iff.mp hx))
    rw [← Measure.map_apply measurable_fst (measurableSet_singleton _), pairLaw_map_fst]
    exact hi
  · apply measure_mono_null (show {p} ⊆ Prod.snd ⁻¹' {p.2} from fun x hx ↦ by
      simpa only [mem_preimage, mem_singleton_iff] using congrArg Prod.snd (mem_singleton_iff.mp hx))
    rw [← Measure.map_apply measurable_snd (measurableSet_singleton _), pairLaw_map_snd]
    exact hj

theorem pairInformation_ne_top (i j : Fin N) : pairInformation q i j ≠ ∞ :=
  klDiv_ne_top (pairLaw_absolutelyContinuous_product q i j) Integrable.of_finite

theorem pairInformation_le_ofReal_toReal (i j : Fin N) :
    pairInformation q i j ≤ ENNReal.ofReal (pairInformation q i j).toReal := by
  rw [ENNReal.ofReal_toReal (pairInformation_ne_top q i j)]

theorem integral_coordinateLaw (a : S → ℝ) (i : Fin N) :
    (∫ x, a x ∂coordinateLaw q i) = coordinateMean q a i := by
  exact integral_map (measurable_pi_apply i).aemeasurable Integrable.of_finite.aestronglyMeasurable

theorem integral_pairLaw (a : S → ℝ) (i j : Fin N) :
    (∫ p, a p.1*a p.2 ∂pairLaw q i j) = pairMoment q a i j := by
  exact integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    Integrable.of_finite.aestronglyMeasurable

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem meanOverlap_nonneg (a : S → ℝ) : 0 ≤ meanOverlap q a :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg N)

/-- A genuine finite-posterior covariance bound, without any assumed coordinate
independence. Its KL quantity is the actual pair-marginal/product divergence. -/
theorem covariance_abs_le (a : S → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ s, |a s| ≤ K) (i j : Fin N) :
    |pairMoment q a i j-coordinateMean q a i*coordinateMean q a j| ≤
      K^2*Real.sqrt (2*(pairInformation q i j).toReal) := by
  have hbound (p : S × S) : |a p.1*a p.2| ≤ K^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hK
  have h := KLBoundProofs.abs_integral_sub_integral_le_of_klDiv_le
    (μ := pairLaw q i j) (ν := (coordinateLaw q i).prod (coordinateLaw q j))
    (fun p : S × S ↦ a p.1*a p.2) (measurable_of_finite _)
    (sq_nonneg K) hbound ENNReal.toReal_nonneg (pairInformation_le_ofReal_toReal q i j)
  rw [integral_pairLaw, integral_prod_mul, integral_coordinateLaw, integral_coordinateLaw] at h
  exact h

theorem integral_overlap (a : S → ℝ) : (∫ z, overlap a z ∂q.prod q) = meanOverlap q a := by
  unfold overlap meanOverlap coordinateMean
  rw [integral_div, integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simpa only [pow_two] using integral_prod_mul (μ := q) (ν := q)
    (fun x : Configuration S N ↦ a (x i)) (fun x : Configuration S N ↦ a (x i))

theorem integral_overlap_sq (a : S → ℝ) :
    (∫ z, (overlap a z)^2 ∂q.prod q) =
      (∑ i : Fin N, ∑ j : Fin N, (pairMoment q a i j)^2)/(N : ℝ)^2 := by
  have hpoly : (fun z : Configuration S N × Configuration S N ↦ (overlap a z)^2) =
      (fun z ↦ (∑ i : Fin N, ∑ j : Fin N,
        (a (z.1 i)*a (z.1 j))*(a (z.2 i)*a (z.2 j)))/(N : ℝ)^2) := by
    funext z
    unfold overlap
    rw [div_pow, pow_two, Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpoly, integral_div, integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [pairMoment, pow_two] using integral_prod_mul (μ := q) (ν := q)
    (fun x : Configuration S N ↦ a (x i)*a (x j))
    (fun x : Configuration S N ↦ a (x i)*a (x j))

theorem replicaVariance_eq_pair_sum (a : S → ℝ) :
    replicaVariance q a =
      (∑ i : Fin N, ∑ j : Fin N,
        ((pairMoment q a i j)^2-(coordinateMean q a i)^2*(coordinateMean q a j)^2))/(N : ℝ)^2 := by
  have hc : replicaVariance q a = (∫ z, (overlap a z)^2 ∂q.prod q)-(meanOverlap q a)^2 := by
    unfold replicaVariance
    have hp : (fun z : Configuration S N × Configuration S N ↦
        (overlap a z-meanOverlap q a)^2) =
        (fun z ↦ (overlap a z)^2-2*meanOverlap q a*overlap a z+(meanOverlap q a)^2) := by
      funext z
      ring
    rw [hp, integral_add Integrable.of_finite (integrable_const _),
      integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
      integral_overlap, integral_const, probReal_univ, one_smul]
    ring
  rw [hc, integral_overlap_sq]
  have hmean : (meanOverlap q a)^2 =
      (∑ i : Fin N, ∑ j : Fin N, (coordinateMean q a i)^2*(coordinateMean q a j)^2)/(N : ℝ)^2 := by
    unfold meanOverlap
    rw [div_pow, pow_two, Finset.sum_mul_sum]
  rw [hmean, ← sub_div]
  congr 1
  simp only [Finset.sum_sub_distrib]

omit [Fintype S] [MeasurableSingletonClass S] in
theorem coordinateMean_abs_le (a : S → ℝ) {K : ℝ} (hb : ∀ s, |a s| ≤ K) (i : Fin N) :
    |coordinateMean q a i| ≤ K := by
  have h := norm_integral_le_of_norm_le_const (μ := q)
    (f := fun x ↦ a (x i)) (Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using hb (x i))
  simpa only [coordinateMean, Real.norm_eq_abs, probReal_univ, mul_one] using h

omit [Fintype S] [MeasurableSingletonClass S] in
theorem pairMoment_abs_le (a : S → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ s, |a s| ≤ K) (i j : Fin N) : |pairMoment q a i j| ≤ K^2 := by
  have h := norm_integral_le_of_norm_le_const (μ := q) (C := K^2)
    (f := fun x ↦ a (x i)*a (x j)) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, pow_two]
      exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hK)
  simpa only [pairMoment, Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem pair_square_difference_le (a : S → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ s, |a s| ≤ K) (i j : Fin N) :
    (pairMoment q a i j)^2-(coordinateMean q a i)^2*(coordinateMean q a j)^2 ≤
      2*K^4*Real.sqrt (2*(pairInformation q i j).toReal) := by
  let b := coordinateMean q a i*coordinateMean q a j
  have hba : |b| ≤ K^2 := by
    change |coordinateMean q a i*coordinateMean q a j| ≤ K^2
    rw [abs_mul, pow_two]
    exact mul_le_mul (coordinateMean_abs_le q a hb i) (coordinateMean_abs_le q a hb j)
      (abs_nonneg _) hK
  have hsum : |pairMoment q a i j+b| ≤ 2*K^2 :=
    (abs_add_le _ _).trans (by linarith [pairMoment_abs_le q a hK hb i j])
  calc
    _ = (pairMoment q a i j-b)*(pairMoment q a i j+b) := by dsimp [b]; ring
    _ ≤ |pairMoment q a i j-b| * |pairMoment q a i j+b| := by
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ |pairMoment q a i j-b| * (2*K^2) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ (K^2*Real.sqrt (2*(pairInformation q i j).toReal))*(2*K^2) :=
      mul_le_mul_of_nonneg_right (covariance_abs_le q a hK hb i j) (by positivity)
    _ = _ := by ring

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem average_pair_sqrt_le (hN : 0 < N) :
    (∑ i : Fin N, ∑ j : Fin N, Real.sqrt (2*(pairInformation q i j).toReal))/(N : ℝ)^2 ≤
      Real.sqrt (2*averagePairInformation q) := by
  let r : Fin N × Fin N → ℝ := fun p ↦ 2*(pairInformation q p.1 p.2).toReal
  have h := average_sqrt_le_sqrt_average r (fun _ ↦ by positivity)
    (by simpa only [Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos hN hN)
  have hcard : (Fintype.card (Fin N × Fin N) : ℝ) = (N : ℝ)^2 := by simp [pow_two]
  rw [hcard] at h
  have hsum : (∑ p : Fin N × Fin N, r p) =
      2*(∑ i : Fin N, ∑ j : Fin N, (pairInformation q i j).toReal) := by
    simp only [r, Fintype.sum_prod_type, ← Finset.mul_sum]
  rw [hsum] at h
  simpa only [r, Fintype.sum_prod_type, averagePairInformation, mul_div_assoc] using h

/-- Thermal posterior-replica concentration is controlled by the actual mean
pair information. The center Q is the random posterior sum of squared means. -/
theorem replicaVariance_le_pairInformation (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    replicaVariance q a ≤ 2*K^4*Real.sqrt (2*averagePairInformation q) := by
  rw [replicaVariance_eq_pair_sum]
  calc
    _ ≤ (∑ i : Fin N, ∑ j : Fin N,
        2*K^4*Real.sqrt (2*(pairInformation q i j).toReal))/(N : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pair_square_difference_le q a hK hb i j
    _ = 2*K^4*((∑ i : Fin N, ∑ j : Fin N,
        Real.sqrt (2*(pairInformation q i j).toReal))/(N : ℝ)^2) := by
      simp_rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (average_pair_sqrt_le q hN) (by positivity)

end Finite
end
end TensorPCA.PosteriorPairProofs
