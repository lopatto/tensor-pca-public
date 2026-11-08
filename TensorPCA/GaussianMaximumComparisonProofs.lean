-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed ports of GaussianFiniteMaximum.lean,
GaussianCompactMaximum.lean, GaussianCompactFeatureComparison.lean and
GaussianNormMean.lean from
https://github.com/pmaronow/slowequilibration-palomar/tree/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration
Original Apache-2.0 SPDX notices and proofs are preserved except the finite
uniform-law API adaptation required by the pinned Mathlib revision. Namespaces are
changed to TensorPCA; local imports use the checked generic comparison port. -/
module
public import TensorPCA.GaussianSpinComparisonProofs
public import TensorPCA.GaussianConcentrationBridge
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Probability.ProductMeasure

/- Source block: GaussianFiniteMaximum.lean. -/
-- SPDX-License-Identifier: Apache-2.0

/-! Finite Gaussian maximum comparison obtained from the proved ordinary
Gaussian log-partition interpolation. The zero-temperature limit is controlled
by the deterministic log-cardinality error. -/

@[expose] public section
namespace TensorPCA.GaussianFiniteMaximum
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open GaussianSpinComparison GaussianSpinInterpolation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type*} [Fintype V] [Nonempty V]

def maximum (f : V → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

lemma le_maximum (f : V → ℝ) (v : V) : f v ≤ maximum f :=
  Finset.le_sup' f (Finset.mem_univ v)

lemma maximum_le (f : V → ℝ) {c : ℝ} (h : ∀ v, f v ≤ c) : maximum f ≤ c :=
  Finset.sup'_le _ _ (fun v _ => h v)

lemma maximum_attained (f : V → ℝ) : ∃ v, maximum f = f v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  exact ⟨v, hv⟩

lemma log_mean_exp_bounds (f : V → ℝ) {β : ℝ} (hβ : 0 < β) :
    β * maximum f - Real.log (Fintype.card V) ≤
      Real.log ((∑ v, Real.exp (β * f v)) / Fintype.card V) ∧
    Real.log ((∑ v, Real.exp (β * f v)) / Fintype.card V) ≤ β * maximum f := by
  have hc : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨v, hv⟩ := maximum_attained f
  have hs : Real.exp (β * maximum f) ≤ ∑ v, Real.exp (β * f v) := by
    rw [hv]
    exact Finset.single_le_sum (f := fun i => Real.exp (β * f i)) (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ v)
  have hu : (∑ v, Real.exp (β * f v)) ≤ Fintype.card V * Real.exp (β * maximum f) := by
    calc
      _ ≤ ∑ _v : V, Real.exp (β * maximum f) :=
        Finset.sum_le_sum (fun v _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_maximum f v) hβ.le))
      _ = _ := by simp
  have hsp : 0 < (∑ v, Real.exp (β * f v)) / (Fintype.card V : ℝ) :=
    div_pos ((Real.exp_pos _).trans_le hs) hc
  constructor
  · have h := Real.log_le_log (div_pos (Real.exp_pos _) hc) (div_le_div_of_nonneg_right hs hc.le)
    rw [Real.log_div (Real.exp_pos _).ne' hc.ne', Real.log_exp] at h
    exact h
  · have hu' : (∑ v, Real.exp (β * f v)) / (Fintype.card V : ℝ) ≤ Real.exp (β * maximum f) :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hu)
    have h := Real.log_le_log hsp hu'
    simpa only [Real.log_exp] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma maximum_rotated_integrable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v, ‖L v‖ ≤ K) (label : ι → Bool) (θ : ℝ) :
    Integrable (fun w => maximum (fun v => L v (rotation label θ w)))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc : Continuous (fun w => maximum (fun v => L v (rotation label θ w))) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun v _ => (L v).continuous.comp (rotation label θ).continuous)
  apply (gaussian_norm_integrable.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    obtain ⟨v, hv⟩ := maximum_attained (fun v => L v (rotation label θ w))
    rw [hv]
    exact (L v).le_opNorm _ |>.trans ((mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) hK))

lemma signedKernel_smul (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (β : ℝ) (v u : V) :
    signedKernel (fun v => β • L v) label v u = β ^ 2 * signedKernel L label v u := by
  simp only [signedKernel, coordinateObservable, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring


variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Mathlib now represents the uniform finite law directly as a measure. -/
lemma uniform_univ_probability :
    IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset V)) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp
  exact ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero (α := V))
    (ENNReal.natCast_ne_top (Fintype.card V))

lemma finite_logPartition_eq (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (β : ℝ) (w : EuclideanSpace ℝ ι) :
    logPartition (Measure.uniformOfFinset (Finset.univ : Finset V)) (fun v => β • L v) w =
      Real.log ((∑ v, Real.exp (β * L v w)) / Fintype.card V) := by
  unfold logPartition GaussianSpinInterpolation.moment Measure.uniformOfFinset
  rw [integral_finsetSum_measure (by
    intro v hv
    exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero (α := V))))]
  congr 1
  simp only [integral_smul_measure, integral_dirac, weight, one_mul, Finset.card_univ,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, smul_apply]
  rw [← Finset.mul_sum, div_eq_inv_mul]

/-- Sudakov–Fernique comparison for the actual finite Gaussian fields. No
pointwise variance equality is assumed: the hypothesis compares increments. -/
theorem expected_maximum_comparison (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool)
    (hinc : ∀ v u, 0 ≤ signedKernel L label v v + signedKernel L label u u -
      2 * signedKernel L label v u) :
    (∫ w, maximum (fun v => L v (rotation label 0 w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    ∫ w, maximum (fun v => L v (rotation label (Real.pi / 2) w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let ν := (Measure.uniformOfFinset (Finset.univ : Finset V))
  haveI : IsProbabilityMeasure ν := uniform_univ_probability
  let K : ℝ := ∑ v, ‖L v‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ v, ‖L v‖ ≤ K := fun v =>
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
  have hi (θ : ℝ) := maximum_rotated_integrable L hK hb label θ
  have hc : (0 : ℝ) ≤ Real.log (Fintype.card V) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := V))
  apply le_of_forall_pos_le_add
  intro ε hε
  let β : ℝ := (Real.log (Fintype.card V) + 1) / ε
  have hβ : 0 < β := div_pos (by linarith) hε
  have hβeq : β * ε = Real.log (Fintype.card V) + 1 := by
    dsimp [β]
    exact div_mul_cancel₀ _ hε.ne'
  have hbβ : ∀ᵐ v ∂ν, ‖β • L v‖ ≤ β * K := .of_forall fun v => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hb v) hβ.le
  have hilp (θ : ℝ) := logPartition_rotated_gaussian_integrable ν
    (fun v => β • L v) (measurable_of_finite _) (mul_nonneg hβ.le hK) hbβ label θ
  have hcomp := gaussian_increment_comparison ν (fun v => β • L v)
    (measurable_of_finite _) (mul_nonneg hβ.le hK) hbβ label (Filter.Eventually.of_forall fun z => by
      rw [signedKernel_smul, signedKernel_smul, signedKernel_smul]
      nlinarith [mul_nonneg (sq_nonneg β) (hinc z.1 z.2)])
  have hilow : Integrable (fun w => β * maximum (fun v => L v (rotation label 0 w)) -
      Real.log (Fintype.card V)) (SYK.standardGaussianMeasureOnEuclidean ι) := by
    exact ((hi 0).const_mul β).sub (integrable_const _)
  have hlo := integral_mono hilow (hilp 0) (fun w => by
      change _ ≤ logPartition (Measure.uniformOfFinset (Finset.univ : Finset V)) _ _
      rw [finite_logPartition_eq]
      exact (log_mean_exp_bounds (fun v => L v (rotation label 0 w)) hβ).1)
  have hup := integral_mono (hilp (Real.pi / 2)) ((hi (Real.pi / 2)).const_mul β)
    (fun w => by
      change logPartition (Measure.uniformOfFinset (Finset.univ : Finset V)) _ _ ≤ _
      rw [finite_logPartition_eq]
      exact (log_mean_exp_bounds (fun v => L v (rotation label (Real.pi / 2) w)) hβ).2)
  rw [integral_sub ((hi 0).const_mul β) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hlo
  rw [integral_const_mul] at hup
  unfold averagedRotatedLogPartition at hcomp
  have h := hlo.trans (hcomp.trans hup)
  nlinarith

end
end TensorPCA.GaussianFiniteMaximum

/- Source block: GaussianCompactMaximum.lean. -/
-- SPDX-License-Identifier: Apache-2.0

/-!
# Compact-index Gaussian supremum comparison

The compact feature image has deterministic finite operator-norm nets. Gaussian suprema are Lipschitz functions of the Gaussian input and have an
integrable Gaussian norm envelope. The finite Sudakov--Fernique comparison
therefore passes to the compact supremum with a proved net error.
-/

@[expose] public section

namespace TensorPCA.GaussianCompactMaximum

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinComparison GaussianSpinInterpolation GaussianFiniteMaximum
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Nonempty V]

theorem field_bddAbove (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    BddAbove (range (fun v => L v w)) := by
  refine ⟨K * ‖w‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (le_abs_self _).trans ((L v).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg w)))

/-- Every actual field value lies below the genuine compact supremum. -/
theorem le_field_supremum (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) (v : V) :
    L v w ≤ ⨆ u, L u w := le_ciSup (field_bddAbove L hb w) v

/-- The true supremum has the actual uniform Gaussian norm envelope. -/
theorem norm_field_supremum_le (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    ‖⨆ v, L v w‖ ≤ K * ‖w‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · let v : V := Classical.choice inferInstance
    have h := (L v).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg w))
    exact (neg_le_of_abs_le h).trans (le_field_supremum L hb w v)
  · exact ciSup_le fun v => (le_abs_self _).trans ((L v).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg w)))

/-- The actual supremum is Lipschitz in all original Gaussian coordinates. -/
theorem field_supremum_lipschitz (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) :
    LipschitzWith (Real.toNNReal K) (fun w => ⨆ v, L v w) := by
  apply LipschitzWith.of_le_add_mul' K
  intro w z
  apply ciSup_le
  intro v
  have hdiff : L v w - L v z ≤ K * dist w z := by
    rw [← map_sub, dist_eq_norm]
    exact (le_abs_self _).trans ((L v).le_opNorm (w - z) |>.trans
      (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _)))
  have hz := le_field_supremum L hb z v
  linarith

/-- Integrability of the genuine rotated supremum, with no countability
restriction on the index type. -/
theorem supremum_rotated_integrable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v, ‖L v‖ ≤ K) (label : ι → Bool) (θ : ℝ) :
    Integrable (fun w => ⨆ v, L v (rotation label θ w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc := (field_supremum_lipschitz L hb).continuous.comp (rotation label θ).continuous
  apply (gaussian_norm_integrable.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => (norm_field_supremum_le L hb _).trans
    (mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) hK)

/-- A deterministic finite feature net approximates every actual field
supremum with its exact operator-norm error bound. -/
theorem finite_net_supremum_bounds (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (s : Finset V) [Nonempty s]
    {ε : ℝ} (hnet : ∀ v, ∃ u ∈ s, ‖L v - L u‖ ≤ ε) (w : EuclideanSpace ℝ ι) :
    maximum (fun u : s => L u w) ≤ (⨆ v, L v w) ∧
      (⨆ v, L v w) ≤ maximum (fun u : s => L u w) + ε * ‖w‖ := by
  constructor
  · exact maximum_le _ fun u => le_field_supremum L hb w u
  · apply ciSup_le
    intro v
    obtain ⟨u, hu, hdist⟩ := hnet v
    have hdiff : L v w - L u w ≤ ε * ‖w‖ := by
      change (L v - L u) w ≤ _
      exact (le_abs_self _).trans ((L v - L u).le_opNorm w |>.trans
        (mul_le_mul_of_nonneg_right hdist (norm_nonneg w)))
    have hmax := le_maximum (fun a : s => L a w) ⟨u, hu⟩
    linarith

variable [TopologicalSpace V] [CompactSpace V]

/-- Compact continuity supplies the uniform operator bound used by the
actual Gaussian envelope. -/
theorem exists_feature_bound (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖L v‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_range hL.norm).bddAbove
  have hb : ∀ v, ‖L v‖ ≤ K := fun v => hK (mem_range_self v)
  exact ⟨K, (norm_nonneg (L (Classical.choice inferInstance))).trans
    (hb (Classical.choice inferInstance)), hb⟩

/-- A finite set of actual indices approximates the entire feature map in
operator norm. This net is deterministic, independent of the disorder. -/
theorem exists_finite_feature_net (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Continuous L) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v, ∃ u ∈ s, ‖L v - L u‖ < ε := by
  classical
  let U : V → Set V := fun u => {v | ‖L v - L u‖ < ε}
  have hU : ∀ u, IsOpen (U u) := fun u =>
    isOpen_lt (hL.sub continuous_const).norm continuous_const
  have hcover : univ ⊆ ⋃ u, U u := by
    intro v _
    exact mem_iUnion.mpr ⟨v, by simpa [U] using hε⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hnet : ∀ v, ∃ u ∈ s, ‖L v - L u‖ < ε := by
    intro v
    simpa only [mem_iUnion, U, mem_setOf_eq, exists_prop] using hs (mem_univ v)
  refine ⟨s, ?_, hnet⟩
  obtain ⟨u, hu, _⟩ := hnet (Classical.choice inferInstance)
  exact ⟨u, hu⟩

/-- Continuity on a compact index space gives an integrable actual Gaussian
supremum at every rotation. -/
theorem supremum_rotated_integrable_of_continuous
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L)
    (label : ι → Bool) (θ : ℝ) :
    Integrable (fun w => ⨆ v, L v (rotation label θ w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨K, hK, hb⟩ := exists_feature_bound L hL
  exact supremum_rotated_integrable L hK hb label θ

/-- Compact-index Sudakov--Fernique for the actual Gaussian fields. The
covariance hypothesis compares actual increments and does not impose constant
pointwise variance or assume the desired supremum comparison. -/
theorem expected_supremum_comparison
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L)
    (label : ι → Bool)
    (hinc : ∀ v u, 0 ≤ signedKernel L label v v + signedKernel L label u u -
      2 * signedKernel L label v u) :
    (∫ w, (⨆ v, L v (rotation label 0 w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    ∫ w, (⨆ v, L v (rotation label (Real.pi / 2) w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  classical
  obtain ⟨K, hK, hb⟩ := exists_feature_bound L hL
  have hi (θ : ℝ) := supremum_rotated_integrable L hK hb label θ
  let M : ℝ := ∫ w : EuclideanSpace ℝ ι, ‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / (M + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hεeq : ε * (M + 1) = δ := by
    exact div_mul_cancel₀ _ (by linarith)
  obtain ⟨s, hs, hnet⟩ := exists_finite_feature_net L hL hε
  obtain ⟨v₀, hv₀⟩ := hs
  letI : Nonempty s := ⟨⟨v₀, hv₀⟩⟩
  letI : MeasurableSpace s := ⊤
  letI : MeasurableSingletonClass s := ⟨fun _ => trivial⟩
  have hnet' : ∀ v, ∃ u ∈ s, ‖L v - L u‖ ≤ ε := by
    intro v
    obtain ⟨u, hu, hdist⟩ := hnet v
    exact ⟨u, hu, hdist.le⟩
  have hiF (θ : ℝ) := maximum_rotated_integrable (fun u : s => L u)
    hK (fun u => hb u) label θ
  have hcomp := expected_maximum_comparison (fun u : s => L u) label
    (fun v u => hinc v u)
  have hup := integral_mono (hi 0)
    ((hiF 0).fun_add (gaussian_norm_integrable.const_mul ε)) (fun w => by
      have h := (finite_net_supremum_bounds L hb s hnet' (rotation label 0 w)).2
      exact h.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (rotation_norm_le label 0 w) hε.le)))
  rw [integral_add (hiF 0) (gaussian_norm_integrable.const_mul ε), integral_const_mul] at hup
  have hlo := integral_mono (hiF (Real.pi / 2)) (hi (Real.pi / 2))
    (fun w => (finite_net_supremum_bounds L hb s hnet' (rotation label (Real.pi / 2) w)).1)
  change _ ≤ _ + ε * M at hup
  nlinarith

end
end TensorPCA.GaussianCompactMaximum

/- Source block: GaussianCompactFeatureComparison.lean. -/
-- SPDX-License-Identifier: Apache-2.0

/-!
# Compact Gaussian comparison on independent coefficient spaces

The two coefficient spaces are joined by their product Gaussian law. Their increment norm comparison is exactly the signed covariance
comparison required by compact Sudakov--Fernique.
-/

@[expose] public section

namespace TensorPCA.GaussianCompactFeatureComparison

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open GaussianSpinComparison GaussianSpinInterpolation GaussianCompactMaximum
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Actual split into the two disjoint original Gaussian coefficient blocks. -/
def sumSplit : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ]
    EuclideanSpace ℝ ι × EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (WithLp.toLp 2 (fun i => w (.inl i)),
        WithLp.toLp 2 (fun j => w (.inr j)))
      map_add' := by intro w z; ext i <;> rfl
      map_smul' := by intro a w; ext i <;> rfl }

/-- Actual coordinate joining map used by the comparison features. -/
def sumJoin : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →L[ℝ]
    EuclideanSpace ℝ (ι ⊕ κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (Sum.elim p.1 p.2)
      map_add' := by intro p q; ext (i | j) <;> rfl
      map_smul' := by intro a p; ext (i | j) <;> rfl }

/-- The true joined standard Gaussian splits into independent standard
Gaussians on the original coefficient spaces. -/
theorem sumSplit_gaussian_map :
    (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)).map (sumSplit (ι := ι) (κ := κ)) =
      (SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean κ) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  have he := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => gaussianReal 0 1)
  have hs : sumSplit ∘ (WithLp.toLp 2 : (ι ⊕ κ → ℝ) → EuclideanSpace ℝ (ι ⊕ κ)) =
      (Prod.map (WithLp.toLp 2) (WithLp.toLp 2)) ∘ e := rfl
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map sumSplit.continuous.measurable (by fun_prop), hs,
    ← Measure.map_map (by fun_prop) e.measurable, he.map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

def blockLabel : ι ⊕ κ → Bool := Sum.elim (fun _ => true) (fun _ => false)

def combinedLinear (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] ℝ :=
  innerSL ℝ (sumJoin (a v, b v))

theorem combinedLinear_apply (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) (w : EuclideanSpace ℝ (ι ⊕ κ)) :
    combinedLinear a b v w = inner ℝ (a v) (sumSplit w).1 + inner ℝ (b v) (sumSplit w).2 := by
  simp only [combinedLinear, innerSL_apply_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  rfl

@[simp] theorem combinedLinear_coordinate (a : V → EuclideanSpace ℝ ι)
    (b : V → EuclideanSpace ℝ κ) (v : V) (i : ι ⊕ κ) :
    coordinateObservable (combinedLinear a b) i v = Sum.elim (a v) (b v) i := by
  simp only [coordinateObservable, combinedLinear, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rfl

theorem combined_signedKernel (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v u : V) :
    signedKernel (combinedLinear a b) blockLabel v u =
      inner ℝ (b v) (b u) - inner ℝ (a v) (a u) := by
  simp only [signedKernel, combinedLinear_coordinate, Fintype.sum_sum_type,
    covarianceSign, blockLabel, Sum.elim_inl, Sum.elim_inr, Bool.true_eq_false,
    Bool.false_eq_true, ite_true, ite_false, neg_one_mul, one_mul, Finset.sum_neg_distrib,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [mul_comm, sub_eq_add_neg, add_comm]

theorem combined_increment_nonnegative (a : V → EuclideanSpace ℝ ι)
    (b : V → EuclideanSpace ℝ κ)
    (hinc : ∀ v u, ‖a v - a u‖ ≤ ‖b v - b u‖) (v u : V) :
    0 ≤ signedKernel (combinedLinear a b) blockLabel v v +
      signedKernel (combinedLinear a b) blockLabel u u -
        2 * signedKernel (combinedLinear a b) blockLabel v u := by
  rw [combined_signedKernel, combined_signedKernel, combined_signedKernel,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hinc v u)
  rw [norm_sub_sq_real, norm_sub_sq_real] at hs
  linarith

theorem combined_rotation_zero (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) (w : EuclideanSpace ℝ (ι ⊕ κ)) :
    combinedLinear a b v (rotation blockLabel 0 w) = inner ℝ (a v) (sumSplit w).1 := by
  rw [combinedLinear_apply]
  have h1 : (sumSplit (rotation blockLabel 0 w)).1 = (sumSplit w).1 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  have h2 : (sumSplit (rotation blockLabel 0 w)).2 = 0 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  rw [h1, h2, inner_zero_right, add_zero]

theorem combined_rotation_pi_div_two (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) (w : EuclideanSpace ℝ (ι ⊕ κ)) :
    combinedLinear a b v (rotation blockLabel (Real.pi / 2) w) = inner ℝ (b v) (sumSplit w).2 := by
  rw [combinedLinear_apply]
  have h1 : (sumSplit (rotation blockLabel (Real.pi / 2) w)).1 = 0 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  have h2 : (sumSplit (rotation blockLabel (Real.pi / 2) w)).2 = (sumSplit w).2 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  rw [h1, h2, inner_zero_right, zero_add]

variable [TopologicalSpace V] [CompactSpace V] [Nonempty V]

/-- Sudakov--Fernique for two genuine Gaussian feature fields on independent
coefficient spaces, stated solely through the true feature increment norms. -/
theorem expected_supremum_comparison_of_increment_norm
    (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (ha : Continuous a) (hb : Continuous b)
    (hinc : ∀ v u, ‖a v - a u‖ ≤ ‖b v - b u‖) :
    (∫ g, (⨆ v, inner ℝ (a v) g) ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      ∫ g, (⨆ v, inner ℝ (b v) g) ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  have hL : Continuous (combinedLinear a b) :=
    (innerSL ℝ).continuous.comp (sumJoin.continuous.comp (ha.prodMk hb))
  have hc := expected_supremum_comparison (combinedLinear a b) hL blockLabel
    (combined_increment_nonnegative a b hinc)
  simp only [combined_rotation_zero, combined_rotation_pi_div_two] at hc
  have hsplit : MeasurePreserving (sumSplit (ι := ι) (κ := κ))
      (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ))
      ((SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean κ)) :=
    ⟨sumSplit.continuous.measurable, sumSplit_gaussian_map⟩
  have hfst := measurePreserving_fst.comp hsplit
  have hsnd := measurePreserving_snd.comp hsplit
  have hAf := (innerSL ℝ).continuous.comp ha
  have hBf := (innerSL ℝ).continuous.comp hb
  obtain ⟨Ka, _, hba⟩ := exists_feature_bound (fun v => innerSL ℝ (a v)) hAf
  obtain ⟨Kb, _, hbb⟩ := exists_feature_bound (fun v => innerSL ℝ (b v)) hBf
  have hAc := (field_supremum_lipschitz (fun v => innerSL ℝ (a v)) hba).continuous
  have hBc := (field_supremum_lipschitz (fun v => innerSL ℝ (b v)) hbb).continuous
  have hla : HasLaw (fun w => (sumSplit (ι := ι) (κ := κ) w).1)
      (SYK.standardGaussianMeasureOnEuclidean ι) (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)) :=
    ⟨hfst.measurable.aemeasurable, hfst.map_eq⟩
  have hlb : HasLaw (fun w => (sumSplit (ι := ι) (κ := κ) w).2)
      (SYK.standardGaussianMeasureOnEuclidean κ) (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)) :=
    ⟨hsnd.measurable.aemeasurable, hsnd.map_eq⟩
  have hea := hla.integral_comp hAc.aestronglyMeasurable
  have heb := hlb.integral_comp hBc.aestronglyMeasurable
  simp only [Function.comp_def, innerSL_apply_apply] at hea heb
  rwa [hea, heb] at hc

end
end TensorPCA.GaussianCompactFeatureComparison


/- Source block: GaussianNormMean.lean, same Apache-2.0 pin above. -/
-- SPDX-License-Identifier: Apache-2.0

/-!
# Gaussian norm second moment and expected norm bound
-/

@[expose] public section

namespace TensorPCA.GaussianNormMean

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The true squared norm of an ordinary standard Gaussian has expectation
equal to the actual Euclidean dimension. -/
theorem integral_norm_sq_stdGaussian :
    (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  let e := stdOrthonormalBasis ℝ E
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x : E => (inner ℝ (e i) x) ^ 2) (stdGaussian E) := by
    exact ((IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp
      (innerSL ℝ (e i))).integrable_sq
  have he (i : Fin (Module.finrank ℝ E)) :
      (∫ x : E, (inner ℝ (e i) x) ^ 2 ∂stdGaussian E) = 1 := by
    change (∫ x : E, (innerSL ℝ (e i) x) ^ 2 ∂stdGaussian E) = 1
    rw [← variance_of_integral_eq_zero (innerSL ℝ (e i)).continuous.measurable.aemeasurable
      (integral_strongDual_stdGaussian (innerSL ℝ (e i))),
      variance_dual_stdGaussian, innerSL_apply_norm, e.norm_eq_one, one_pow]
  simp_rw [← e.sum_sq_inner_right]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp [he]

/-- Cauchy--Schwarz for the genuine standard Gaussian norm, obtained from
its exact second moment and nonnegative variance. -/
theorem integral_norm_stdGaussian_le_sqrt_finrank :
    (∫ x : E, ‖x‖ ∂stdGaussian E) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := by
  have hv := variance_nonneg (fun x : E => ‖x‖) (stdGaussian E)
  have hLp : MemLp (fun x : E => ‖x‖) 2 (stdGaussian E) := IsGaussian.memLp_two_id.norm
  rw [variance_eq_sub hLp] at hv
  change 0 ≤ (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) - (∫ x : E, ‖x‖ ∂stdGaussian E) ^ 2 at hv
  rw [integral_norm_sq_stdGaussian] at hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity)
  have hsp := Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)
  nlinarith

variable (ι : Type*) [Fintype ι]

/-- Coordinate form for the actual Gaussian law used in the interpolation. -/
theorem standardGaussian_integral_norm_sq :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖ ^ 2 ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      (Fintype.card ι : ℝ) := by
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian,
    integral_norm_sq_stdGaussian, finrank_euclideanSpace]

/-- The expected norm of the actual coefficient Gaussian is at most the
square root of its actual number of coordinates. -/
theorem standardGaussian_integral_norm_le_sqrt_card :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      Real.sqrt (Fintype.card ι : ℝ) := by
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  simpa only [finrank_euclideanSpace] using
    (integral_norm_stdGaussian_le_sqrt_finrank (E := EuclideanSpace ℝ ι))

end
end TensorPCA.GaussianNormMean

@[expose] public section
namespace TensorPCA.GaussianMaximumComparisonProofs
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [TopologicalSpace V] [CompactSpace V] [Nonempty V]

/-- Compact Gaussian comparison under the canonical Mathlib Gaussian law. -/
theorem expected_supremum_comparison
    (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (ha : Continuous a) (hb : Continuous b)
    (hinc : ∀ v u, ‖a v-a u‖ ≤ ‖b v-b u‖) :
    (∫ g, (⨆ v, inner ℝ (a v) g) ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      ∫ g, (⨆ v, inner ℝ (b v) g) ∂stdGaussian (EuclideanSpace ℝ κ) := by
  simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using
    GaussianCompactFeatureComparison.expected_supremum_comparison_of_increment_norm a b ha hb hinc

/-- Every compact continuous Gaussian feature supremum is integrable. -/
theorem supremum_integrable (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Integrable (fun g ↦ ⨆ v, inner ℝ (a v) g) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hL := (innerSL ℝ).continuous.comp ha
  obtain ⟨K, hK, hb⟩ := GaussianCompactMaximum.exists_feature_bound (fun v ↦ innerSL ℝ (a v)) hL
  have H : Integrable (fun g ↦ ⨆ v, (innerSL ℝ (a v)) g)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    apply (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K).mono'
      (GaussianCompactMaximum.field_supremum_lipschitz (fun v ↦ innerSL ℝ (a v)) hb).continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall (GaussianCompactMaximum.norm_field_supremum_le _ hb)
  simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge, innerSL_apply_apply] using H

/-- A compact field whose increment norm is dominated by a linear field has
an actual expected maximum bounded by the linear coefficient norm scale. -/
theorem expected_supremum_le_linear_bound
    (a : V → EuclideanSpace ℝ ι) (z : V → EuclideanSpace ℝ κ)
    (ha : Continuous a) (hz : Continuous z) {L : ℝ} (hL : 0 ≤ L)
    (hz1 : ∀ v, ‖z v‖ = 1)
    (hinc : ∀ v u, ‖a v-a u‖ ≤ L*‖z v-z u‖) :
    (∫ g, (⨆ v, inner ℝ (a v) g) ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      L*Real.sqrt (Fintype.card κ : ℝ) := by
  let b : V → EuclideanSpace ℝ κ := fun v ↦ L • z v
  have hb : Continuous b := hz.const_smul L
  have H := expected_supremum_comparison a b ha hb (fun v u ↦ by
    simpa only [b, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL] using hinc v u)
  have hpoint (g : EuclideanSpace ℝ κ) : (⨆ v, inner ℝ (b v) g) ≤ L*‖g‖ := by
    apply ciSup_le
    intro v
    exact (real_inner_le_norm _ _).trans (by simp [b, norm_smul, abs_of_nonneg hL, hz1])
  have hnorm : Integrable (fun g : EuclideanSpace ℝ κ ↦ L*‖g‖)
      (stdGaussian (EuclideanSpace ℝ κ)) := (IsGaussian.integrable_id.norm).const_mul L
  have Hupper := integral_mono (supremum_integrable b hb) hnorm hpoint
  rw [integral_const_mul] at Hupper
  exact H.trans (Hupper.trans (mul_le_mul_of_nonneg_left
    (by simpa only [finrank_euclideanSpace] using
      (GaussianNormMean.integral_norm_stdGaussian_le_sqrt_finrank (E := EuclideanSpace ℝ κ))) hL))

end
end TensorPCA.GaussianMaximumComparisonProofs
