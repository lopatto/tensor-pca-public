-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GroundState
public import TensorPCA.Geometry
public import TensorPCA.VariationalProofs
public import TensorPCA.GaussianMaximumComparisonProofs
public import Mathlib.Algebra.Ring.GeomSum

/-! The slice feature covariance and Gaussian maximum upper bounds.
The physical lower/equality limits are separate obligations. -/
@[expose] public section
namespace TensorPCA.GroundUpperProofs
open Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section

def sliceAmplitude (N k : ℕ) (m : ℝ) (p : Fin k) : ℝ :=
  Real.sqrt N*Real.sqrt (Nat.choose k (p.val+1))*m^(k-(p.val+1))*
    (Real.sqrt (1-m^2))^(p.val+1)

theorem sliceAmplitude_sq (N k : ℕ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (p : Fin k) :
    (sliceAmplitude N k m p)^2 = (N : ℝ)*VariationalProofs.sliceCoefficient k m p := by
  have hmp : (m^(k-(p.val+1)))^2 = (m^2)^(k-(p.val+1)) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hsp : ((Real.sqrt (1-m^2))^(p.val+1))^2 = (1-m^2)^(p.val+1) := by
    rw [← pow_mul, Nat.mul_comm (p.val+1) 2, pow_mul,
      Real.sq_sqrt (VariationalProofs.one_sub_sq_nonneg hm)]
  unfold sliceAmplitude VariationalProofs.sliceCoefficient
  simp only [mul_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt (Nat.cast_nonneg (Nat.choose k (p.val+1))), hmp, hsp]
  ring

theorem continuous_sliceFeature (N k : ℕ) (m : ℝ) :
    Continuous (GroundState.sliceFeature (N := N) k m) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fun_prop

/-- Exact covariance of the genuine ordered Gaussian slice feature. -/
theorem sliceFeature_inner {N k : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (x y : Model.Vector N) :
    inner ℝ (GroundState.sliceFeature k m x) (GroundState.sliceFeature k m y) =
      (N : ℝ)*Scalar.xiSlice k m (inner ℝ x y) := by
  have hblock (p : Fin k) :
      (∑ i : Fin (p.val+1) → Fin N,
        (sliceAmplitude N k m p*∏ j, y (i j))*(sliceAmplitude N k m p*∏ j, x (i j))) =
      (sliceAmplitude N k m p)^2*(inner ℝ x y)^(p.val+1) := by
    have H := Geometry.feature_inner (k := p.val+1) x y
    change (∑ i : Fin (p.val+1) → Fin N, (∏ j, y (i j))*(∏ j, x (i j))) =
      (inner ℝ x y)^(p.val+1) at H
    rw [← H, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i : GroundState.Coordinate N k,
    (sliceAmplitude N k m i.1*∏ j, y (i.2 j))*(sliceAmplitude N k m i.1*∏ j, x (i.2 j))) = _
  rw [Fintype.sum_sigma]
  simp_rw [hblock, sliceAmplitude_sq N k hm]
  rw [VariationalProofs.xiSlice_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  ring


/-- The elementary increment estimate is valid for negative overlaps too. -/
theorem one_sub_pow_le_mul (k : ℕ) {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    1-r^k ≤ (k : ℝ)*(1-r) := by
  have hpow (i : ℕ) : r^i ≤ 1 := by
    apply (le_abs_self (r^i)).trans
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg r) (abs_le.mpr hr)
  have H : (∑ i ∈ Finset.range k, r^i) ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum (fun i hi ↦ hpow i)
      _ = _ := by simp
  rw [← geom_sum_mul_neg]
  exact mul_le_mul_of_nonneg_right H (sub_nonneg.mpr hr.2)

theorem sliceFeature_norm_sq {N k : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    {x : Model.Vector N} (hx : x ∈ Model.unitSphere N) :
    ‖GroundState.sliceFeature k m x‖^2 = (N : ℝ)*(1-m^(2*k)) := by
  rw [← real_inner_self_eq_norm_sq, sliceFeature_inner hm, real_inner_self_eq_norm_sq]
  change ‖x‖ = 1 at hx
  rw [hx, one_pow]
  unfold Scalar.xiSlice
  have h : m^2+(1-m^2)*(1 : ℝ) = 1 := by ring
  rw [h, one_pow]

/-- The actual slice process has the increment metric dominated by a linear
Gaussian field with scale sqrt(N*k*(1-m²)). -/
theorem sliceFeature_increment_le {N k : ℕ} {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) {x y : Model.Vector N}
    (hx : x ∈ Model.unitSphere N) (hy : y ∈ Model.unitSphere N) :
    ‖GroundState.sliceFeature k m x-GroundState.sliceFeature k m y‖ ≤
      (Real.sqrt N*Real.sqrt ((k : ℝ)*(1-m^2)))*‖x-y‖ := by
  have hxn : ‖x‖ = 1 := hx
  have hyn : ‖y‖ = 1 := hy
  have hs : 0 ≤ 1-m^2 := VariationalProofs.one_sub_sq_nonneg hm
  have hr : inner ℝ x y ∈ Icc (-1 : ℝ) 1 := by
    have H := abs_real_inner_le_norm x y
    rw [hxn, hyn, one_mul] at H
    exact abs_le.mp H
  have hu : m^2+(1-m^2)*inner ℝ x y ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hs (by linarith [hr.1] : 0 ≤ inner ℝ x y+1), sq_nonneg m]
    · nlinarith [mul_nonneg hs (sub_nonneg.mpr hr.2)]
  have H := one_sub_pow_le_mul k hu
  have Hscaled := mul_le_mul_of_nonneg_left H (show 0 ≤ 2*(N : ℝ) by positivity)
  have hfeature : ‖GroundState.sliceFeature k m x-GroundState.sliceFeature k m y‖^2 =
      2*(N : ℝ)*(1-(m^2+(1-m^2)*inner ℝ x y)^k) := by
    rw [norm_sub_sq_real, sliceFeature_norm_sq hm hx, sliceFeature_norm_sq hm hy,
      sliceFeature_inner hm]
    unfold Scalar.xiSlice
    ring
  have hxy : ‖x-y‖^2 = 2*(1-inner ℝ x y) := by
    rw [norm_sub_sq_real, hxn, hyn]
    ring
  have Hsq : ‖GroundState.sliceFeature k m x-GroundState.sliceFeature k m y‖^2 ≤
      (N : ℝ)*((k : ℝ)*(1-m^2))*‖x-y‖^2 := by
    rw [hfeature, hxy]
    nlinarith [Hscaled]
  have hscale : (Real.sqrt N*Real.sqrt ((k : ℝ)*(1-m^2))*‖x-y‖)^2 =
      (N : ℝ)*((k : ℝ)*(1-m^2))*‖x-y‖^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N),
      Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg k) hs)]
  have hnonneg : 0 ≤ Real.sqrt N*Real.sqrt ((k : ℝ)*(1-m^2))*‖x-y‖ := by positivity
  nlinarith [sq_nonneg ‖GroundState.sliceFeature k m x-GroundState.sliceFeature k m y‖]


/-- The literal finite Gaussian slice maximum has the sharp constant-profile
upper bound. This is a physical expectation bound, without a limit premise. -/
theorem expectedSliceGround_le {N k : ℕ} (hN : 0 < N)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.expectedSliceGround N k m ≤ Real.sqrt ((k : ℝ)*(1-m^2)) := by
  letI : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  letI : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  let a : Model.unitSphere N → GroundState.Disorder N k :=
    fun x ↦ GroundState.sliceFeature k m x
  let z : Model.unitSphere N → Model.Vector N := fun x ↦ x
  have ha : Continuous a := (continuous_sliceFeature N k m).comp continuous_subtype_val
  have hz : Continuous z := continuous_subtype_val
  have H := GaussianMaximumComparisonProofs.expected_supremum_le_linear_bound a z ha hz
    (L := Real.sqrt N*Real.sqrt ((k : ℝ)*(1-m^2))) (by positivity)
    (fun x ↦ x.property)
    (fun x y ↦ sliceFeature_increment_le hm x.property y.property)
  have hscale : (Real.sqrt N*Real.sqrt ((k : ℝ)*(1-m^2)))*Real.sqrt N =
      (N : ℝ)*Real.sqrt ((k : ℝ)*(1-m^2)) := by
    calc
      _ = (Real.sqrt N)^2*Real.sqrt ((k : ℝ)*(1-m^2)) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  simp only [a, Fintype.card_fin, hscale] at H
  have hsup (g : GroundState.Disorder N k) :
      sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) =
        ⨆ x : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k m x) g := by
    rw [iSup, Set.image_eq_range]
  unfold GroundState.expectedSliceGround
  simp_rw [hsup]
  rw [integral_div]
  apply (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mpr
  simpa only [mul_comm] using H


end
end TensorPCA.GroundUpperProofs
