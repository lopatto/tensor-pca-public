-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSTrialTransport
public import Mathlib.MeasureTheory.Integral.Prod

/-! The covariance energy identity for the true integrated CDF. The
 derivative-at-zero term is essential, including for linear covariances. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem integral_secondDeriv_kernel (xi : ℝ → ℝ)
    (hxi : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt xi (deriv xi t) t)
    (hxi' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (deriv xi) (deriv (deriv xi) t) t)
    (hcont : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, deriv (deriv xi) t * (1 - max t q)) +
      deriv xi 0 * (1 - q) = xi 1 - xi q := by
  have hInt : IntervalIntegrable (fun t => deriv (deriv xi) t * (1 - max t q))
      volume 0 1 :=
    (hcont.mul (continuous_const.sub (continuous_id.max continuous_const)).continuousOn).intervalIntegrable_of_Icc zero_le_one
  have hHeadSet : uIcc (0 : ℝ) q ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hq.1]
    exact Icc_subset_Icc le_rfl hq.2
  have hTailSet : uIcc q (1 : ℝ) ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hq.2]
    exact Icc_subset_Icc hq.1 le_rfl
  have hHeadInt := hInt.mono_set (by simpa [uIcc_of_le zero_le_one] using hHeadSet)
  have hTailInt := hInt.mono_set (by simpa [uIcc_of_le zero_le_one] using hTailSet)
  have hHead : (∫ t in (0 : ℝ)..q, deriv (deriv xi) t * (1 - max t q)) =
      deriv xi q * (1 - q) - deriv xi 0 * (1 - q) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => deriv xi t * (1 - q)) _ hHeadInt
    intro t ht
    rw [max_eq_right ((uIcc_of_le hq.1 ▸ ht).2)]
    exact (hxi' t (hHeadSet ht)).mul_const (1 - q)
  have hTail : (∫ t in q..(1 : ℝ), deriv (deriv xi) t * (1 - max t q)) =
      xi 1 - (deriv xi q * (1 - q) + xi q) := by
    have hd : ∀ t ∈ uIcc q (1 : ℝ),
        HasDerivAt (fun t => deriv xi t * (1 - t) + xi t)
          (deriv (deriv xi) t * (1 - max t q)) t := by
      intro t ht
      rw [max_eq_left ((uIcc_of_le hq.2 ▸ ht).1)]
      convert (((hxi' t (hTailSet ht)).mul ((hasDerivAt_id t).const_sub 1)).add
        (hxi t (hTailSet ht))) using 1 <;> (try funext u) <;> simp only [id_eq, Pi.add_apply, Pi.mul_apply] <;> ring
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hTailInt
    simpa using hh
  rw [← intervalIntegral.integral_add_adjacent_intervals hHeadInt hTailInt, hHead, hTail]
  ring

theorem energy_real_integral_eq (k : ℕ) (hk : 1 ≤ k) (beta m : ℝ) (nu : Trial) :
    (∫ t in (0 : ℝ)..1, deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t) +
      deriv (Scalar.xiSlice k m) 0 * profile beta nu 0 =
      beta * (Scalar.xiSlice k m 1 -
        ∫ q : Overlap, Scalar.xiSlice k m (q : ℝ) ∂(nu : Measure Overlap)) := by
  let xi := Scalar.xiSlice k m
  let w := deriv (deriv xi)
  let f : ℝ × Overlap → ℝ := fun z => w z.1 * (1 - max z.1 (z.2 : ℝ))
  have hw : Continuous w := continuous_secondDeriv_slice k m
  have hc : Continuous f := by
    exact (hw.comp continuous_fst).mul
      (continuous_const.sub (continuous_fst.max (continuous_subtype_val.comp continuous_snd)))
  have hprod : Integrable f ((volume.restrict (Icc (0 : ℝ) 1)).prod (nu : Measure Overlap)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_univ)
  have hswap := integral_integral_swap (f := fun t q => f (t, q)) hprod
  have hxiInt : Integrable (fun q : Overlap => xi (q : ℝ)) (nu : Measure Overlap) := by
    have hcx : Continuous (fun q : Overlap => xi (q : ℝ)) := by
      dsimp [xi, Scalar.xiSlice]
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hcx.continuousOn.integrableOn_compact (isCompact_univ : IsCompact (univ : Set Overlap))
  have hkInt : Integrable (fun q : Overlap => 1 - (q : ℝ)) (nu : Measure Overlap) := by
    have hh := kernel_integrable (nu : Measure Overlap) 0
    apply hh.congr
    exact .of_forall fun q => by simp [kernel, max_eq_right q.property.1]
  have hpoint (q : Overlap) :
      (∫ t in Icc (0 : ℝ) 1, f (t, q)) + deriv xi 0 * (1 - (q : ℝ)) = xi 1 - xi q := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_secondDeriv_kernel xi
      (fun t _ => (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt.hasDerivAt)
      (fun t _ => (VariationalProofs.hasDerivAt_deriv_xiSlice hk m t).differentiableAt.hasDerivAt)
      hw.continuousOn q.property
  have hidentity := integral_congr_ae (μ := (nu : Measure Overlap)) (Eventually.of_forall hpoint)
  rw [integral_add hprod.integral_prod_right (hkInt.const_mul (deriv xi 0)),
    integral_const_mul, integral_sub (integrable_const (xi 1)) hxiInt] at hidentity
  simp only [integral_const, probReal_univ, one_smul] at hidentity
  change (∫ t in Icc (0 : ℝ) 1, ∫ q : Overlap, f (t, q) ∂(nu : Measure Overlap)) = _ at hswap
  rw [← hswap] at hidentity
  have hkernel0 : (∫ q : Overlap, kernel 0 q ∂(nu : Measure Overlap)) =
      ∫ q : Overlap, (1 - (q : ℝ)) ∂(nu : Measure Overlap) := by
    apply integral_congr_ae
    exact .of_forall fun q => by simp [kernel, max_eq_right q.property.1]
  change (∫ t in (0 : ℝ)..1, w t * (beta * hatCDF (nu : Measure Overlap) t)) +
      deriv xi 0 * (beta * hatCDF (nu : Measure Overlap) 0) = _
  have hleft : (∫ t in (0 : ℝ)..1, w t * (beta * hatCDF (nu : Measure Overlap) t)) =
      beta * ∫ t in Icc (0 : ℝ) 1, ∫ q : Overlap, f (t, q) ∂(nu : Measure Overlap) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f, hatCDF, kernel]
    rw [integral_const_mul]
    ring
  rw [hleft]
  unfold hatCDF
  rw [hkernel0]
  calc
    _ = beta * ((∫ t in Icc (0 : ℝ) 1,
        ∫ q : Overlap, f (t, q) ∂(nu : Measure Overlap)) +
        deriv xi 0 * ∫ q : Overlap, (1 - (q : ℝ)) ∂(nu : Measure Overlap)) := by ring
    _ = _ := congrArg (beta * ·) hidentity

/-- The extended energy is exactly the ordinary covariance energy on the
manuscript domain. In particular the linear term has not been suppressed. -/
theorem energy_eq_ofReal (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 ≤ beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) :
    energy k beta m nu = ENNReal.ofReal (beta * (Scalar.xiSlice k m 1 -
      ∫ q : Overlap, Scalar.xiSlice k m (q : ℝ) ∂(nu : Measure Overlap))) := by
  have hm2 := VariationalProofs.one_sub_sq_nonneg hm
  have hder0 : 0 ≤ deriv (Scalar.xiSlice k m) 0 := by
    rw [VariationalProofs.deriv_xiSlice]
    positivity
  have hder2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ deriv (deriv (Scalar.xiSlice k m)) t := by
    rw [(VariationalProofs.hasDerivAt_deriv_xiSlice hk m t).deriv]
    have hkreal : 0 ≤ (k : ℝ) - 1 := by
      have hkk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hb : 0 ≤ m ^ 2 + (1 - m ^ 2) * t := add_nonneg (sq_nonneg m) (mul_nonneg hm2 ht.1)
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hkreal) (sq_nonneg _))
      (pow_nonneg hb _)
  have hi : IntegrableOn (fun t => deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t)
      (Ico (0 : ℝ) 1) :=
    ((continuous_secondDeriv_slice k m).mul (profile_continuous beta nu)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      fun t => deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact mul_nonneg (hder2 t ⟨ht.1, ht.2.le⟩) (profile_bounds hbeta nu ⟨ht.1, ht.2.le⟩).1
  have hnb : 0 ≤ deriv (Scalar.xiSlice k m) 0 * profile beta nu 0 :=
    mul_nonneg hder0 (profile_bounds hbeta nu (by norm_num)).1
  rw [energy, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← ENNReal.ofReal_add (integral_nonneg_of_ae hn) hnb]
  congr 1
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact energy_real_integral_eq k hk beta m nu

end
end TensorPCA.NonRSLowerProofs.FiniteCS
