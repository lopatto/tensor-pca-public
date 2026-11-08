-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.RetainedCountProofs.CrisantiSommers

/-! The integrated-CDF kernel on the closed finite-temperature overlap interval. These
lemmas use ordinary probability measures and do not depend on a compactness theorem
for the space of probability measures.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set MeasureTheory
open scoped Topology
noncomputable section

abbrev Overlap := Icc (0 : ℝ) 1

def kernel (t : ℝ) : C(Overlap, ℝ) :=
  ⟨fun q => 1 - max t (q : ℝ), by fun_prop⟩

def hatCDF (nu : Measure Overlap) (t : ℝ) : ℝ := ∫ q, kernel t q ∂nu

theorem kernel_integrable (nu : Measure Overlap) [IsProbabilityMeasure nu] (t : ℝ) :
    Integrable (kernel t) nu := by
  apply (integrable_const (2 + |t|)).mono' (by fun_prop)
  exact .of_forall fun q => by
    change |1 - max t (q : ℝ)| ≤ 2 + |t|
    apply abs_le.mpr
    have hmax : max t (q : ℝ) ≤ |t| + 1 :=
      max_le (by linarith [le_abs_self t]) (by linarith [q.property.2, abs_nonneg t])
    constructor
    · linarith
    · linarith [le_max_left t (q : ℝ), neg_abs_le t]

theorem hatCDF_lipschitz (nu : Measure Overlap) [IsProbabilityMeasure nu] :
    LipschitzWith 1 (hatCDF nu) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  change |hatCDF nu t - hatCDF nu u| ≤ (1 : ℝ) * |t - u|
  rw [one_mul]
  unfold hatCDF
  rw [← integral_sub (kernel_integrable nu t) (kernel_integrable nu u)]
  have hb : ∀ᵐ q ∂nu, ‖kernel t q - kernel u q‖ ≤ |t - u| :=
    .of_forall fun q => by
      change |(1 - max t (q : ℝ)) - (1 - max u (q : ℝ))| ≤ |t - u|
      have heq : (1 - max t (q : ℝ)) - (1 - max u (q : ℝ)) =
          -(max t (q : ℝ) - max u (q : ℝ)) := by ring
      rw [heq, abs_neg]
      exact abs_max_sub_max_le_abs t u (q : ℝ)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := nu) hb

theorem hatCDF_continuous (nu : Measure Overlap) [IsProbabilityMeasure nu] :
    Continuous (hatCDF nu) := (hatCDF_lipschitz nu).continuous

theorem hatCDF_antitone (nu : Measure Overlap) [IsProbabilityMeasure nu] :
    Antitone (hatCDF nu) := by
  intro t u htu
  apply integral_mono (kernel_integrable nu u) (kernel_integrable nu t)
  intro q
  exact sub_le_sub_left (max_le_max htu le_rfl) 1

theorem hatCDF_nonneg (nu : Measure Overlap) [IsProbabilityMeasure nu]
    {t : ℝ} (ht : t ≤ 1) : 0 ≤ hatCDF nu t := by
  apply integral_nonneg
  intro q
  exact sub_nonneg.mpr (max_le ht q.property.2)

theorem hatCDF_le_one_sub (nu : Measure Overlap) [IsProbabilityMeasure nu] (t : ℝ) :
    hatCDF nu t ≤ 1 - t := by
  have H := integral_mono (kernel_integrable nu t) (integrable_const (1 - t))
    (fun q : Overlap => sub_le_sub_left (le_max_left t (q : ℝ)) 1)
  simpa only [hatCDF, integral_const, probReal_univ, one_smul] using H

theorem hatCDF_one (nu : Measure Overlap) [IsProbabilityMeasure nu] : hatCDF nu 1 = 0 := by
  have heq : kernel (1 : ℝ) = (0 : C(Overlap, ℝ)) := by
    ext q
    simp only [kernel, ContinuousMap.coe_mk, ContinuousMap.coe_zero, Pi.zero_apply,
      max_eq_left q.property.2, sub_self]
  simp only [hatCDF, heq, ContinuousMap.coe_zero, Pi.zero_apply, integral_zero]

theorem hatCDF_dirac (q : Overlap) (t : ℝ) :
    hatCDF (Measure.dirac q) t = 1 - max t (q : ℝ) := by
  simp [hatCDF, kernel]

theorem hatCDF_concave (nu : Measure Overlap) [IsProbabilityMeasure nu] :
    ConcaveOn ℝ univ (hatCDF nu) := by
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  have hi := integral_mono
    (((kernel_integrable nu t).const_mul a).add ((kernel_integrable nu u).const_mul b))
    (kernel_integrable nu (a * t + b * u)) (fun q : Overlap => by
      have hmax : max (a * t + b * u) (q : ℝ) ≤ a * max t (q : ℝ) + b * max u (q : ℝ) := by
        apply max_le
        · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left t (q : ℝ)) ha)
            (mul_le_mul_of_nonneg_left (le_max_left u (q : ℝ)) hb)
        · have hh := add_le_add (mul_le_mul_of_nonneg_left (le_max_right t (q : ℝ)) ha)
            (mul_le_mul_of_nonneg_left (le_max_right u (q : ℝ)) hb)
          have hss : a * (q : ℝ) + b * (q : ℝ) = (q : ℝ) := by rw [← add_mul, hab, one_mul]
          rw [hss] at hh
          exact hh
      change a * (1 - max t (q : ℝ)) + b * (1 - max u (q : ℝ)) ≤
        1 - max (a * t + b * u) (q : ℝ)
      nlinarith)
  change (∫ q, a * kernel t q + b * kernel u q ∂nu) ≤ _ at hi
  rw [integral_add ((kernel_integrable nu t).const_mul a)
    ((kernel_integrable nu u).const_mul b), integral_const_mul, integral_const_mul] at hi
  simpa only [smul_eq_mul, hatCDF] using hi

theorem scaled_hatCDF_lipschitz (nu : Measure Overlap) [IsProbabilityMeasure nu]
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    LipschitzWith ⟨beta, hbeta⟩ (fun t => beta * hatCDF nu t) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  change |beta * hatCDF nu t - beta * hatCDF nu u| ≤ beta * |t - u|
  rw [← mul_sub, abs_mul, abs_of_nonneg hbeta]
  have H := (hatCDF_lipschitz nu).dist_le_mul t u
  change |hatCDF nu t - hatCDF nu u| ≤ (1 : ℝ) * |t - u| at H
  rw [one_mul] at H
  exact mul_le_mul_of_nonneg_left H hbeta

theorem scaled_hatCDF_bounds (nu : Measure Overlap) [IsProbabilityMeasure nu]
    {beta t : ℝ} (hbeta : 0 ≤ beta) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ beta * hatCDF nu t ∧ beta * hatCDF nu t ≤ beta * (1 - t) :=
  ⟨mul_nonneg hbeta (hatCDF_nonneg nu ht.2),
    mul_le_mul_of_nonneg_left (hatCDF_le_one_sub nu t) hbeta⟩

theorem scaled_hatCDF_antitone (nu : Measure Overlap) [IsProbabilityMeasure nu]
    {beta : ℝ} (hbeta : 0 ≤ beta) : Antitone (fun t => beta * hatCDF nu t) := by
  intro t u htu
  exact mul_le_mul_of_nonneg_left (hatCDF_antitone nu htu) hbeta

theorem scaled_hatCDF_concave (nu : Measure Overlap) [IsProbabilityMeasure nu]
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    ConcaveOn ℝ univ (fun t => beta * hatCDF nu t) := by
  simpa only [smul_eq_mul] using ConcaveOn.smul hbeta (hatCDF_concave nu)


end
end TensorPCA.NonRSLowerProofs.FiniteCS
