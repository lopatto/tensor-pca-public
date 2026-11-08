-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarSeparationProofs
public import TensorPCA.MaximumProofs
public import TensorPCA.Statistical

/-! An explicit Borel nearest-limit classifier and its finite mean-square bound. -/
@[expose] public section
namespace TensorPCA.ClassifierProofs
open Set Filter MeasureTheory ScalarStaticRatioProofs ScalarSeparationProofs
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def cost {r : ℕ} (centers : Fin (r+1) → ℝ) (z : ℝ) (i : Fin (r+1)) : ℝ := |z-centers i|

def nearestSet {r : ℕ} (centers : Fin (r+1) → ℝ) (z : ℝ) : Finset (Fin (r+1)) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, cost centers z i ≤ cost centers z j)

theorem nearestSet_nonempty {r : ℕ} (centers : Fin (r+1) → ℝ) (z : ℝ) :
    (nearestSet centers z).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := Finite.exists_min (cost centers z)
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- Ties select the least index among all exact distance minimizers. -/
def nearest {r : ℕ} (centers : Fin (r+1) → ℝ) (z : ℝ) : Fin (r+1) :=
  (nearestSet centers z).min' (nearestSet_nonempty centers z)

theorem nearest_min {r : ℕ} (centers : Fin (r+1) → ℝ) (z : ℝ) (i : Fin (r+1)) :
    cost centers z (nearest centers z) ≤ cost centers z i := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ (nearestSet_nonempty centers z))).2 i

theorem nearest_eq_iff {r : ℕ} (centers : Fin (r+1) → ℝ) (z : ℝ) (i : Fin (r+1)) :
    nearest centers z = i ↔
      (∀ j, cost centers z i ≤ cost centers z j) ∧
        ∀ j, j < i → cost centers z i < cost centers z j := by
  classical
  constructor
  · intro heq
    refine ⟨fun j => by simpa only [heq] using nearest_min centers z j, ?_⟩
    intro j hji
    by_contra hn
    have hcost : cost centers z j ≤ cost centers z i := le_of_not_gt hn
    have hj : j ∈ nearestSet centers z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun l => hcost.trans (by simpa only [heq] using nearest_min centers z l)⟩
    have hmin := Finset.min'_le (nearestSet centers z) j hj
    change nearest centers z ≤ j at hmin
    rw [heq] at hmin
    exact (not_le_of_gt hji) hmin
  · rintro ⟨hmin, hstrict⟩
    have hi : i ∈ nearestSet centers z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmin⟩
    have hle := Finset.min'_le (nearestSet centers z) i hi
    change nearest centers z ≤ i at hle
    apply le_antisymm hle
    by_contra hn
    have hlt : nearest centers z < i := lt_of_not_ge hn
    exact not_lt_of_ge (nearest_min centers z i) (hstrict _ hlt)

theorem nearest_measurable {r : ℕ} (centers : Fin (r+1) → ℝ) : Measurable (nearest centers) := by
  apply measurable_to_countable'
  intro i
  have hset : (nearest centers) ⁻¹' {i} =
      {z : ℝ | (∀ j, cost centers z i ≤ cost centers z j) ∧
        ∀ j, j < i → cost centers z i < cost centers z j} := by
    ext z
    exact nearest_eq_iff centers z i
  have hm (j : Fin (r+1)) : Measurable (fun z : ℝ => |z-centers j|) :=
    (continuous_id.sub continuous_const).abs.measurable
  rw [hset, ofPred_and]
  apply MeasurableSet.inter
  · simp only [cost, ofPred_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (hm i) (hm j))
  · simp only [cost, ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _hj
    exact measurableSet_lt (hm i) (hm j)

def classifierConstant {r : ℕ} (centers : Fin (r+1) → ℝ) : ℝ :=
  ∑ i, ∑ j, 4/(centers i-centers j)^2

theorem classifierConstant_nonneg {r : ℕ} (centers : Fin (r+1) → ℝ) : 0 ≤ classifierConstant centers := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))

theorem pair_coefficient_le {r : ℕ} (centers : Fin (r+1) → ℝ) (i j : Fin (r+1)) :
    4/(centers i-centers j)^2 ≤ classifierConstant centers := by
  unfold classifierConstant
  calc
    _ ≤ ∑ j', 4/(centers i-centers j')^2 := Finset.single_le_sum (fun j' _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum
      (f := fun i' : Fin (r+1) => ∑ j' : Fin (r+1), 4/(centers i'-centers j')^2)
      (fun i' _ => Finset.sum_nonneg (fun j' _ => by positivity)) (Finset.mem_univ i)

/-- A classification error costs at least the squared half-gap between centers. -/
theorem classifier_pointwise {r : ℕ} {centers : Fin (r+1) → ℝ}
    (hinj : Function.Injective centers) (z : ℝ) (i : Fin (r+1)) :
    (if nearest centers z ≠ i then (1 : ℝ) else 0) ≤ classifierConstant centers*(z-centers i)^2 := by
  by_cases heq : nearest centers z = i
  · rw [ite_eq_right (not_not.mpr heq)]
    exact mul_nonneg (classifierConstant_nonneg centers) (sq_nonneg _)
  · rw [ite_eq_left heq]
    let j := nearest centers z
    have hji : j ≠ i := heq
    have hdist : centers i-centers j ≠ 0 := sub_ne_zero.mpr (fun hc => hji (hinj hc).symm)
    have hmin := nearest_min centers z i
    have htriangle : |centers i-centers j| ≤ 2*|z-centers i| := by
      have ht := abs_sub_le (centers i) z (centers j)
      rw [abs_sub_comm (centers i) z] at ht
      dsimp [cost] at hmin
      change |z-centers j| ≤ |z-centers i| at hmin
      linarith
    have hsq : (centers i-centers j)^2 ≤ 4*(z-centers i)^2 := by
      nlinarith [sq_abs (centers i-centers j), sq_abs (z-centers i),
        abs_nonneg (centers i-centers j), abs_nonneg (z-centers i)]
    have hone : 1 ≤ (4/(centers i-centers j)^2)*(z-centers i)^2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_ne_zero hdist)).mpr
      simpa only [one_mul] using hsq
    exact hone.trans (mul_le_mul_of_nonneg_right (pair_coefficient_le centers i j) (sq_nonneg _))

theorem classification_error_le_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} {centers : Fin (r+1) → ℝ}
    (hinj : Function.Injective centers) {stat : Ω → ℝ} (hstat : Measurable stat)
    (i : Fin (r+1)) (hint : Integrable (fun w => (stat w-centers i)^2) μ) :
    μ.real {w | nearest centers (stat w) ≠ i} ≤
      classifierConstant centers * ∫ w, (stat w-centers i)^2 ∂μ := by
  classical
  have htest : Measurable (fun w => nearest centers (stat w)) := (nearest_measurable centers).comp hstat
  have hs : MeasurableSet {w | nearest centers (stat w) ≠ i} :=
    (measurableSet_eq_fun htest measurable_const).compl
  have hi := integral_mono ((integrable_const (1 : ℝ)).indicator hs) (hint.const_mul (classifierConstant centers))
    (fun w => by
      simpa only [indicator_apply, mem_ofPred_eq, Pi.one_apply] using classifier_pointwise hinj (stat w) i)
  rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, integral_const_mul] at hi
  exact hi

theorem maximum_observation_memLp_two {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    MemLp (Model.normalizedMaximum (N := N) (k := k)) 2 (Model.observationLaw N k lam) := by
  have hM := (Geometry.normalizedMaximum_lipschitz (k := k) hN).continuous.measurable
  unfold Model.observationLaw
  apply (memLp_map_measure_iff hM.aestronglyMeasurable
    (Model.measurable_observation N k lam).aemeasurable).mpr
  exact MaximumProofs.plantedMaximum_memLp_two hN lam

/-- The requested finite quantitative classifier, using the actual normalized
maximum statistic and actual observation laws. No asymptotic consistency input. -/
theorem finite_classifier (k : ℕ) (hk : 3 ≤ k) (r : ℕ) (strengths : Fin (r+1) → ℝ)
    (hinj : Function.Injective strengths) (hsuper : ∀ i, Scalar.lambdaC k < strengths i) :
    ∃ (tests : ∀ n : ℕ, Model.Tensor (n+1) k → Fin (r+1)) (C : ℝ),
      (∀ n, Measurable (tests n)) ∧ ∀ i n,
      (Model.observationLaw (n+1) k (strengths i)).real {y | tests n y ≠ i} ≤
        C*Statistical.maximumMeanSquare (n+1) k (strengths i) := by
  let centers : Fin (r+1) → ℝ := fun i => Scalar.mleValue k (strengths i)
  have hc : Function.Injective centers := by
    intro i j hij
    exact hinj ((strictMonoOn_mleValue k hk).injOn (hsuper i).le (hsuper j).le hij)
  let tests : ∀ n : ℕ, Model.Tensor (n+1) k → Fin (r+1) :=
    fun n y => nearest centers (Model.normalizedMaximum y)
  have hmeas (n : ℕ) : Measurable (tests n) :=
    (nearest_measurable centers).comp (Geometry.normalizedMaximum_lipschitz (k := k) (Nat.succ_pos n)).continuous.measurable
  refine ⟨tests, classifierConstant centers, hmeas, ?_⟩
  intro i n
  have hint : Integrable (fun y : Model.Tensor (n+1) k =>
      (Model.normalizedMaximum y-centers i)^2) (Model.observationLaw (n+1) k (strengths i)) :=
    ((maximum_observation_memLp_two (Nat.succ_pos n) (strengths i)).sub (memLp_const (centers i))).integrable_sq
  exact classification_error_le_mse (Model.observationLaw (n+1) k (strengths i)) hc
    (Geometry.normalizedMaximum_lipschitz (k := k) (Nat.succ_pos n)).continuous.measurable i hint

/-- The singleton family uses its sole label and has zero finite error constant. -/
theorem nearest_singleton (centers : Fin 1 → ℝ) (z : ℝ) : nearest centers z = 0 :=
  Fin.eq_zero _

theorem classifierConstant_singleton (centers : Fin 1 → ℝ) : classifierConstant centers = 0 := by
  simp [classifierConstant]

end
end TensorPCA.ClassifierProofs
