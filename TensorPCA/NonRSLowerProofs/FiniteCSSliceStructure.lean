-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSContactGeometry
public import TensorPCA.JTProfileBoundsProofs

/-! The finite-temperature slice minimizer is concentrated on at most two interior
overlaps. Generic support calculus is applied to the full slice covariance,
including its positive linear term. Existence is bound separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open RetainedCountProofs.CrisantiSommers

private theorem curvature_zero_iff_comparator_zero {beta v p : ℝ}
    (hb : 0 < beta) (hv : 0 < v) (hp : 0 < p) :
    beta ^ 2 * v - 1 / p ^ 2 = 0 ↔ (Real.sqrt v)⁻¹ - beta * p = 0 := by
  have hspos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsne : Real.sqrt v ≠ 0 := hspos.ne'
  have hsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  have hprodpos : 0 < beta * Real.sqrt v * p := mul_pos (mul_pos hb hspos) hp
  constructor
  · intro hzero
    have hvalue : beta ^ 2 * v = 1 / p ^ 2 := sub_eq_zero.mp hzero
    have hprodsq : (beta * Real.sqrt v * p) ^ 2 = 1 := by
      calc
        _ = beta ^ 2 * (Real.sqrt v) ^ 2 * p ^ 2 := by ring
        _ = beta ^ 2 * v * p ^ 2 := by rw [hsq]
        _ = (1 / p ^ 2) * p ^ 2 := by rw [hvalue]
        _ = 1 := by field_simp
    have hprod : beta * Real.sqrt v * p = 1 := by nlinarith
    field_simp [hsne]
    nlinarith
  · intro hzero
    have hprod : beta * Real.sqrt v * p = 1 := by
      field_simp [hsne] at hzero
      nlinarith
    have hnum : beta ^ 2 * v * p ^ 2 = 1 := by
      calc
        _ = beta ^ 2 * (Real.sqrt v) ^ 2 * p ^ 2 := congrArg (fun w => beta ^ 2 * w * p ^ 2) hsq.symm
        _ = (beta * Real.sqrt v * p) ^ 2 := by ring
        _ = 1 := by rw [hprod]; norm_num
    field_simp [hp.ne']
    nlinarith

theorem xiSlice_firstVariation_maxima_encard_le_two (k : ℕ) (hk : 3 ≤ k)
    {beta m : ℝ} (hbeta : 0 < beta) (hm : |m| < 1) (zeta : Admissible)
    (M : ℝ) (hmax : ∀ r ∈ Ico (0 : ℝ) 1,
      firstVariation beta (Scalar.xiSlice k m) zeta.law r ≤ M) :
    {r | r ∈ Ioo (0 : ℝ) 1 ∧
      firstVariation beta (Scalar.xiSlice k m) zeta.law r = M}.encard ≤ 2 := by
  let xi := Scalar.xiSlice k m
  have hxi : DifferentiableOn ℝ xi (Iio 1) := by
    intro t _
    exact (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt.differentiableWithinAt
  have hd (t : ℝ) : HasDerivAt xi (deriv xi t) t :=
    (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt.hasDerivAt
  have hd' (t : ℝ) : HasDerivAt (deriv xi) (deriv (deriv xi) t) t :=
    (VariationalProofs.hasDerivAt_deriv_xiSlice (by omega : 1 ≤ k) m t).differentiableAt.hasDerivAt
  have hhat : ConcaveOn ℝ (Ioo (0 : ℝ) 1) (xHat zeta.law) :=
    (xHat_concave zeta.law zeta.hasCutoff).subset (subset_univ _) (convex_Ioo 0 1)
  apply maxima_encard_le_two
    (fun t ht => (firstVariation_hasDerivAt beta xi zeta.law zeta.hasCutoff ht.2 (hd t)).differentiableAt)
    (fun t ht => (firstVariation_deriv_hasDerivAt beta xi zeta.law zeta.hasCutoff ht.2 hxi (hd' t)).differentiableAt)
    hmax
    ((JTModelCurvatureProofs.xiSlice_comparator_strictConvex k hk hm).sub_concaveOn
      (ConcaveOn.smul hbeta.le hhat))
  intro t ht
  rw [(firstVariation_deriv_hasDerivAt beta xi zeta.law zeta.hasCutoff ht.2 hxi (hd' t)).deriv]
  exact curvature_zero_iff_comparator_zero hbeta
    (JTProfileBoundsProofs.xiSlice_secondDeriv_pos k (by omega) hm ht)
    (xHat_pos zeta.law zeta.hasCutoff ht.2)

theorem xiSlice_firstVariation_origin_lt_maximum (k : ℕ) (hk : 3 ≤ k)
    {beta m : ℝ} (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1)
    (zeta : Admissible) (M : ℝ)
    (hmax : ∀ r ∈ Ico (0 : ℝ) 1, firstVariation beta (Scalar.xiSlice k m) zeta.law r ≤ M) :
    firstVariation beta (Scalar.xiSlice k m) zeta.law 0 < M := by
  have hB : 0 < 1 - m ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm1)
  have hmne : m ≠ 0 := abs_pos.mp hm0
  have hder : 0 < deriv (Scalar.xiSlice k m) 0 := by
    rw [VariationalProofs.deriv_xiSlice]
    simp only [mul_zero, add_zero]
    exact mul_pos (mul_pos (Nat.cast_pos.mpr (by omega)) hB)
      (pow_pos (sq_pos_of_ne_zero hmne) _)
  let f := firstVariation beta (Scalar.xiSlice k m) zeta.law
  have hd : HasDerivAt f (beta ^ 2 * deriv (Scalar.xiSlice k m) 0) 0 := by
    simpa using firstVariation_hasDerivAt beta (Scalar.xiSlice k m) zeta.law zeta.hasCutoff
      (by norm_num : (0 : ℝ) < 1)
      (VariationalProofs.hasDerivAt_xiSlice k m 0).differentiableAt.hasDerivAt
  have hle : f 0 ≤ M := hmax 0 (by norm_num)
  apply lt_of_le_of_ne hle
  intro heq
  have hlocal : IsLocalMaxOn f (Icc (0 : ℝ) (1 / 2)) 0 := by
    apply IsMaxOn.isLocalMaxOn
    intro t ht
    rw [heq]
    exact hmax t ⟨ht.1, by linarith [ht.2]⟩
  have hcone : (1 / 2 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) (1 / 2)) 0 := by
    have hh := sub_mem_posTangentConeAt_of_segment_subset
      (x := (0 : ℝ)) (y := (1 / 2 : ℝ))
      (by rw [segment_eq_Icc (by norm_num)])
    simpa using hh
  have hn := hlocal.hasFDerivWithinAt_nonpos hd.hasDerivWithinAt.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hn
  have hpos := mul_pos (sq_pos_of_pos hbeta) hder
  nlinarith

/-- Every cutoff-class minimizer for the full slice is a probability law concentrated on
at most two points strictly between zero and one. Equal points are allowed, so the
replica-symmetric degeneration is kept.
-/
theorem xiSlice_minimizer_ae_two_points (k : ℕ) (hk : 3 ≤ k)
    {beta m : ℝ} (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1)
    (zeta : Admissible) (hmin : zeta.IsMinimizer beta (Scalar.xiSlice k m)) :
    ∃ a b : ℝ, a ∈ Ioo (0 : ℝ) 1 ∧ b ∈ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ r ∂zeta.law, r = a ∨ r = b := by
  have hxi : ContinuousOn (Scalar.xiSlice k m) (Ico (0 : ℝ) 1) := by
    intro t _
    exact (VariationalProofs.hasDerivAt_xiSlice k m t).continuousAt.continuousWithinAt
  obtain ⟨M, hmax, heq⟩ := (zeta.minimizer_iff_support_on_maximum beta (Scalar.xiSlice k m) hxi).mp hmin
  have horigin := xiSlice_firstVariation_origin_lt_maximum k hk hbeta hm0 hm1 zeta M hmax
  let Z : Set ℝ := {r | r ∈ Ioo (0 : ℝ) 1 ∧
    firstVariation beta (Scalar.xiSlice k m) zeta.law r = M}
  have hae : ∀ᵐ r ∂zeta.law, r ∈ Z := by
    filter_upwards [zeta.hasCutoff.2.2, heq] with r hr hrM
    refine ⟨⟨?_, hr.2.trans_lt zeta.hasCutoff.2.1⟩, hrM⟩
    by_contra hpos
    have hr0 : r = 0 := le_antisymm (le_of_not_gt hpos) hr.1
    rw [hr0] at hrM
    exact horigin.ne hrM
  have hcount : Z.encard ≤ 2 := xiSlice_firstVariation_maxima_encard_le_two k hk hbeta hm1 zeta M hmax
  by_cases hsmall : Z.encard ≤ 1
  · obtain ⟨a, ha⟩ := hae.exists
    refine ⟨a, a, ha.1, ha.1, ?_⟩
    filter_upwards [hae] with r hr
    exact Or.inl ((Set.encard_le_one_iff.mp hsmall) r a hr ha)
  · have hge : 2 ≤ Z.encard := by
      simpa only [one_add_one_eq_two] using
        (ENat.add_one_le_iff ENat.one_ne_top).mpr (lt_of_not_ge hsmall)
    obtain ⟨a, b, _hab, hZ⟩ := Set.encard_eq_two.mp (le_antisymm hcount hge)
    have ha : a ∈ Z := by rw [hZ]; simp
    have hb : b ∈ Z := by rw [hZ]; simp
    refine ⟨a, b, ha.1, hb.1, ?_⟩
    filter_upwards [hae] with r hr
    simpa only [hZ, mem_insert_iff, mem_singleton_iff] using hr

end
end TensorPCA.NonRSLowerProofs.FiniteCS
