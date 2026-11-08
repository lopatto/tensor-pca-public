-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- The explicit pure critical-point complexity is the amplitude-one, Q=1
specialization of SphericalMarkedComplexity.pureMarkedComplexity, from
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e.
The geometric semicircle calculation is adapted from the same source's
SphericalOnePointContactSaddle. No physical ground formula is assumed. -/
module
public import TensorPCA.PureVariationalProofs
public import TensorPCA.RetainedCountProofs.SemicirclePotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
namespace TensorPCA.PureComplexityProofs
noncomputable section
open Set Filter
open RetainedCountProofs.SemicirclePotential
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Explicit amplitude-one pure critical-point complexity. -/
def pureComplexity (k : ℕ) (e : ℝ) : ℝ :=
  1/2 + Real.log ((k : ℝ)-1)/2 - e^2/2 +
    potential ((k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))

private theorem geometric_shift_facts {r : ℝ} (hr : 1 < r) :
    2 < r+1/r ∧ 0 ≤ r-1/r ∧ (r+1/r)^2-4=(r-1/r)^2 := by
  have hpos : 0 < r := by linarith
  have hsmall : 1/r < 1 := (div_lt_one hpos).mpr hr
  have hg : 0 < (r-1)^2/r := div_pos (sq_pos_of_pos (sub_pos.mpr hr)) hpos
  have he : (r-1)^2/r=r+1/r-2 := by field_simp [hpos.ne'];ring
  rw [he] at hg
  refine ⟨by linarith,by linarith,?_⟩
  field_simp [hpos.ne']
  ring

lemma potential_geometric {r : ℝ} (hr : 1 < r) :
    potential (r+1/r)=Real.log r+1/(2*r^2) := by
  obtain ⟨hedge,hsub,hdisc⟩ := geometric_shift_facts hr
  have hpos : 0 < r := by linarith
  rw [potential_explicit hedge,hdisc,Real.sqrt_sq_eq_abs,abs_of_nonneg hsub]
  have hl : (r+1/r+(r-1/r))/2=r := by ring
  rw [hl]
  field_simp [hpos.ne']
  ring

/-- The true root places the critical complexity contact outside the spectral edge. -/
lemma scaled_gs_geometric (k : ℕ) (hk : 3 ≤ k) :
    let r := Real.sqrt (1+Scalar.zK k)/Real.sqrt ((k : ℝ)-1)
    1 < r ∧
      (k : ℝ)*Scalar.gs k/Real.sqrt ((k : ℝ)*((k : ℝ)-1))=r+1/r := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hk1 : 0 < (k : ℝ)-1 := by
    have h : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  have hz2 := ScalarThresholdProofs.zK_gt_sub_two k hk
  have ha : 0 < Real.sqrt (1+Scalar.zK k) := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < Real.sqrt ((k : ℝ)-1) := Real.sqrt_pos.mpr hk1
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  dsimp only
  constructor
  · apply (lt_div_iff₀ hb).mpr
    simpa only [one_mul] using Real.sqrt_lt_sqrt hk1.le (show (k : ℝ)-1<1+Scalar.zK k by linarith)
  · rw [PureVariationalProofs.gs_eq_normalized k hk,
      Real.sqrt_mul hk0.le, Real.sqrt_mul hk0.le]
    field_simp [ha.ne',hb.ne',hs.ne']
    nlinarith [Real.sq_sqrt hk0.le,Real.sq_sqrt hk1.le,
      Real.sq_sqrt (show 0≤1+Scalar.zK k by linarith)]

lemma scaled_gs_gt_two (k : ℕ) (hk : 3 ≤ k) :
    2 < (k : ℝ)*Scalar.gs k/Real.sqrt ((k : ℝ)*((k : ℝ)-1)) := by
  obtain ⟨hr,he⟩ := scaled_gs_geometric k hk
  rw [he]
  exact (geometric_shift_facts hr).1


/-- At the reviewed scalar ground constant the literal pure complexity is zero. -/
theorem pureComplexity_gs (k : ℕ) (hk : 3 ≤ k) :
    pureComplexity k (Scalar.gs k)=0 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hk1 : 0 < (k : ℝ)-1 := by
    have h : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  have hz1 : 0 < 1+Scalar.zK k := by linarith
  have ha : 0 < Real.sqrt (1+Scalar.zK k) := Real.sqrt_pos.mpr hz1
  have hb : 0 < Real.sqrt ((k : ℝ)-1) := Real.sqrt_pos.mpr hk1
  obtain ⟨hr,he⟩ := scaled_gs_geometric k hk
  have hg2 : (Scalar.gs k)^2=((k : ℝ)+Scalar.zK k)^2/((k : ℝ)*(1+Scalar.zK k)) := by
    rw [PureVariationalProofs.gs_eq_normalized k hk,div_pow,Real.sq_sqrt (mul_pos hk0 hz1).le]
  have hr2 : (Real.sqrt (1+Scalar.zK k)/Real.sqrt ((k : ℝ)-1))^2=
      (1+Scalar.zK k)/((k : ℝ)-1) := by
    rw [div_pow,Real.sq_sqrt hz1.le,Real.sq_sqrt hk1.le]
  unfold pureComplexity
  rw [he,potential_geometric hr,hg2,hr2,Real.log_div ha.ne' hb.ne',
    Real.log_sqrt hz1.le,Real.log_sqrt hk1.le,ScalarThresholdProofs.log_one_add_zK k hk]
  field_simp [hk0.ne',hk1.ne',hz1.ne']
  ring


lemma pureComplexity_continuous (k : ℕ) : Continuous (pureComplexity k) := by
  unfold pureComplexity
  exact ((continuous_const.add continuous_const).sub ((continuous_id.pow 2).div_const 2)).add
    (potential_continuous.comp ((continuous_const.mul continuous_id).div_const _))

lemma pureComplexity_hasDerivAt (k : ℕ) {e : ℝ}
    (he : 2 < (k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1))) :
    HasDerivAt (pureComplexity k)
      (-e+(((k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1))-
        Real.sqrt (((k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))^2-4))/2)*
          ((k : ℝ)/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))) e := by
  have h := ((hasDerivAt_const e (1/2+Real.log ((k : ℝ)-1)/2)).sub
    (((hasDerivAt_id e).pow 2).div_const 2)).add
      ((potential_hasDerivAt_explicit he).comp e
        (((hasDerivAt_id e).const_mul (k : ℝ)).div_const _))
  convert h using 1
  · rfl
  · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

lemma potential_slope_le_one {u : ℝ} (hu : 2 < u) :
    (u-Real.sqrt (u^2-4))/2 ≤ 1 := by
  have hs : 0 ≤ Real.sqrt (u^2-4) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ u^2-4 by nlinarith)
  have hlo : u-2 ≤ Real.sqrt (u^2-4) := by nlinarith
  linarith


/-- A fixed positive upper-tail complexity slope. -/
def pureComplexitySlope (k : ℕ) : ℝ :=
  Scalar.gs k-(k : ℝ)/Real.sqrt ((k : ℝ)*((k : ℝ)-1))

lemma pureComplexitySlope_pos (k : ℕ) (hk : 3 ≤ k) : 0 < pureComplexitySlope k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ)-1 := by linarith
  have hs : 0 < Real.sqrt ((k : ℝ)*((k : ℝ)-1)) := Real.sqrt_pos.mpr (mul_pos hk0 hk1)
  have H := (lt_div_iff₀ hs).mp (scaled_gs_gt_two k hk)
  have H' := mul_lt_mul_of_pos_right H hs
  have hg : (k : ℝ) < Scalar.gs k*Real.sqrt ((k : ℝ)*((k : ℝ)-1)) := by
    apply (mul_lt_mul_iff_right₀ hk0).mp
    nlinarith [Real.sq_sqrt (mul_pos hk0 hk1).le]
  exact sub_pos.mpr ((div_lt_iff₀ hs).mpr hg)

lemma scaled_energy_gt_two (k : ℕ) (hk : 3 ≤ k) {e : ℝ} (he : Scalar.gs k ≤ e) :
    2 < (k : ℝ)*e/Real.sqrt ((k : ℝ)*((k : ℝ)-1)) := by
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg k))
    (Real.sqrt_nonneg ((k : ℝ)*((k : ℝ)-1)))
  exact (scaled_gs_gt_two k hk).trans_le h

lemma pureComplexity_deriv_upper (k : ℕ) (hk : 3 ≤ k) {e : ℝ}
    (he : Scalar.gs k ≤ e) : deriv (pureComplexity k) e ≤ -pureComplexitySlope k := by
  have hx := scaled_energy_gt_two k hk he
  rw [(pureComplexity_hasDerivAt k hx).deriv]
  have H := mul_le_mul_of_nonneg_right (potential_slope_le_one hx)
    (div_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg ((k : ℝ)*((k : ℝ)-1))))
  unfold pureComplexitySlope
  linarith

/-- The true pure complexity is uniformly negative above the ground constant. -/
theorem pureComplexity_upper_linear (k : ℕ) (hk : 3 ≤ k) {e : ℝ}
    (he : Scalar.gs k ≤ e) :
    pureComplexity k e ≤ -pureComplexitySlope k*(e-Scalar.gs k) := by
  have hd : DifferentiableOn ℝ (pureComplexity k) (interior (Ici (Scalar.gs k))) := by
    intro x hx
    have hx' : Scalar.gs k ≤ x := interior_subset hx
    exact (pureComplexity_hasDerivAt k (scaled_energy_gt_two k hk hx')).differentiableAt.differentiableWithinAt
  have H := (convex_Ici (Scalar.gs k)).image_sub_le_mul_sub_of_deriv_le
    (pureComplexity_continuous k).continuousOn hd
    (fun x hx => pureComplexity_deriv_upper k hk (interior_subset hx))
    (Scalar.gs k) le_rfl e he he
  simpa only [pureComplexity_gs k hk,sub_zero] using H

theorem pureComplexity_neg (k : ℕ) (hk : 3 ≤ k) {e : ℝ} (he : Scalar.gs k < e) :
    pureComplexity k e < 0 :=
  (pureComplexity_upper_linear k hk he.le).trans_lt
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (pureComplexitySlope_pos k hk)) (sub_pos.mpr he))



end
end TensorPCA.PureComplexityProofs
