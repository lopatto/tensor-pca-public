-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Fixed-cavity compatibility of sublinear perturbation variances. The dimension is the
natural N; no shifted-dimension convention or perturbation-amplitude definition is
introduced here.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FinitePerturbationScaleAsymptotics
open Filter Set Real
open scoped Topology
noncomputable section

theorem rpow_increment_abs_le {x y alpha : ℝ} (hx : 0<x) (hy : 0≤y)
    (ha0 : 0≤alpha) (ha1 : alpha≤1) :
    |(x+y)^alpha-x^alpha|≤alpha*y*x^(alpha-1) := by
  have hs : -1≤y/x := by linarith [div_nonneg hy hx.le]
  have H := mul_le_mul_of_nonneg_left
    (rpow_one_add_le_one_add_mul_self hs ha0 ha1) (Real.rpow_nonneg hx.le alpha)
  have hfactor : x*(1+y/x)=x+y := by field_simp
  have hpow : (x+y)^alpha=x^alpha*(1+y/x)^alpha := by
    rw [← hfactor,Real.mul_rpow hx.le (by positivity : 0≤1+y/x)]
  have hmono : x^alpha≤(x+y)^alpha := Real.rpow_le_rpow hx.le (by linarith) ha0
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  calc
    _ ≤ x^alpha*(1+alpha*(y/x))-x^alpha := by rw [hpow]; exact sub_le_sub_right H _
    _ = _ := by rw [Real.rpow_sub_one hx.ne']; ring

private theorem nat_rpow_sub_one_tendsto_zero {alpha : ℝ} (ha1 : alpha<1) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)^(alpha-1)) atTop (𝓝 0) := by
  simpa only [neg_sub,Function.comp_def] using
    (tendsto_rpow_neg_atTop (sub_pos.mpr ha1)).comp tendsto_natCast_atTop_atTop

theorem rpow_increment_abs_tendsto_zero (M : ℕ) {alpha : ℝ}
    (ha0 : 0<alpha) (ha1 : alpha<1) :
    Tendsto (fun N : ℕ ↦ |((N+M : ℕ) : ℝ)^alpha-(N : ℝ)^alpha|) atTop (𝓝 0) := by
  have hbound : Tendsto (fun N : ℕ ↦ alpha*(M : ℝ)*(N : ℝ)^(alpha-1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (nat_rpow_sub_one_tendsto_zero ha1).const_mul (alpha*(M : ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ abs_nonneg _)) _ hbound
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ)<(N : ℝ) := by exact_mod_cast hN
  simpa only [Nat.cast_add] using rpow_increment_abs_le hNr (Nat.cast_nonneg M) ha0.le ha1.le

theorem rpow_shift_div_dimension_tendsto_zero (M : ℕ) {alpha : ℝ}
    (ha0 : 0<alpha) (ha1 : alpha<1) :
    Tendsto (fun N : ℕ ↦ ((N+M : ℕ) : ℝ)^alpha/(N : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun N : ℕ ↦ (N : ℝ)^alpha/(N : ℝ)) atTop (𝓝 0) := by
    apply (nat_rpow_sub_one_tendsto_zero ha1).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact Real.rpow_sub_one (by exact_mod_cast (Nat.ne_of_gt hN)) alpha
  have hinc : Tendsto (fun N : ℕ ↦ ((N+M : ℕ) : ℝ)^alpha-(N : ℝ)^alpha) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr (by
      simpa only [Real.norm_eq_abs] using rpow_increment_abs_tendsto_zero M ha0 ha1)
  have hquot := hinc.div_atTop tendsto_natCast_atTop_atTop
  have H := hbase.add hquot
  apply Tendsto.congr' (Eventually.of_forall (fun N ↦ by ring))
    (show Tendsto (fun N : ℕ ↦ (N : ℝ)^alpha/(N : ℝ)+
      (((N+M : ℕ) : ℝ)^alpha-(N : ℝ)^alpha)/(N : ℝ)) atTop (𝓝 0) from by simpa only [add_zero] using H)

end
end TensorPCA.NonRSLowerProofs.FinitePerturbationScaleAsymptotics
