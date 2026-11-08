-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedMass
public import TensorPCA.ChiSquareTailProofs

/-! The Gaussian cavity-annulus logarithmic cost is sublinear in the cavity dimension.
This does not assert that its unnormalized log vanishes at fixed dimension. Finite
positivity is supplied by the separate open-set proof.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityAnnulusMassAsymptotics
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCavityRetainedMass FiniteCavityShellLinearPartition
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem log_add_one_div_dimension_tendsto_zero :
    Tendsto (fun M : ℕ => Real.log ((M : ℝ)+1)/(M : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun M : ℕ => (M : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa only [Function.comp_def,pow_one,one_mul,add_neg_cancel_right] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hN

theorem tail_at_mean_polynomial_lower {M : ℕ} (hM : 0<M) :
    Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))≤
      (stdGaussian (Model.Vector M)).real {x | (M : ℝ)≤‖x‖^2} := by
  have hMr : (0 : ℝ)<M := Nat.cast_pos.mpr hM
  have H := ChiSquareTailProofs.chiSquare_tail_lower (b := 1) hM le_rfl
  simp only [mul_one,sub_self,Real.log_one,mul_zero,zero_div,sub_zero,zero_sub] at H
  have hdiv : (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))/(M : ℝ)≤
      Real.log ((stdGaussian (Model.Vector M)).real {x | (M : ℝ)≤‖x‖^2})/(M : ℝ) := by
    simpa only [one_div_mul_eq_div,neg_mul,neg_div] using H.2
  have hlog := (div_le_div_iff_of_pos_right hMr).1 hdiv
  exact (Real.exp_le_exp.2 hlog).trans_eq (Real.exp_log H.1)

theorem annulus_lower_via_tails {M : ℕ} (hM : 0<M) {delta : ℝ} (hdelta : 0<delta) :
    Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))-
      Real.exp (-(M : ℝ)*RetainedCountProofs.GaussianShell.rate (1+delta))≤annulusMass M delta := by
  have hsub : {x : Model.Vector M | (M : ℝ)≤‖x‖^2}⊆
      gaussianAnnulus M delta∪{x | (1+delta)*(M : ℝ)≤‖x‖^2} := by
    intro x hx
    by_cases hxu : ‖x‖^2≤(M : ℝ)*(1+delta)
    · exact Or.inl ⟨hx,hxu⟩
    · apply Or.inr
      change (1+delta)*(M : ℝ)≤‖x‖^2
      nlinarith only [lt_of_not_ge hxu]
  have hUnion := (measureReal_mono (μ := stdGaussian (Model.Vector M)) hsub).trans (measureReal_union_le _ _)
  have hUpper := RetainedCountProofs.GaussianShell.upper_tail (E := Model.Vector M)
    (a := 1+delta) (by linarith only [hdelta])
  simp only [finrank_euclideanSpace,Fintype.card_fin] at hUpper
  have hLower := tail_at_mean_polynomial_lower hM
  change _≤(stdGaussian (Model.Vector M)).real (gaussianAnnulus M delta)
  linarith only [hUnion,hUpper,hLower]

theorem eventually_annulus_polynomial_lower {delta : ℝ} (hdelta : 0<delta) :
    ∀ᶠ M : ℕ in atTop,
      Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))/2≤annulusMass M delta := by
  let c := RetainedCountProofs.GaussianShell.rate (1+delta)
  have hc : 0<c := RetainedCountProofs.GaussianShell.rate_pos (by linarith only [hdelta]) (by linarith only [hdelta])
  have hRatio : Tendsto (fun M : ℕ => RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1)/(M : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using
      log_add_one_div_dimension_tendsto_zero.const_mul RadialTailBounds.tailLogConstant
  have hLog := hRatio.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<c/2))
  have hExp := (exponential_dimension_decay (by positivity : 0<c/2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [eventually_ge_atTop 1,hLog,hExp] with M hM hlog hexp
  have hMpos : 0<M := by omega
  have hMr : (0 : ℝ)<M := Nat.cast_pos.mpr hMpos
  have hClog : RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1)≤(c/2)*(M : ℝ) :=
    (div_le_iff₀ hMr).1 hlog.le
  have hUpper : Real.exp (-(M : ℝ)*c)≤
      (1/2 : ℝ)*Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1)) := by
    calc
      _ = Real.exp (-(M : ℝ)*c+RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))*
          Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(M : ℝ)*(c/2))*Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith only [hClog])) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp.le (Real.exp_pos _).le
  have hA := annulus_lower_via_tails hMpos hdelta
  change Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))-Real.exp (-(M : ℝ)*c)≤_ at hA
  linarith only [hA,hUpper]

theorem eventually_annulus_log_lower {delta : ℝ} (hdelta : 0<delta) :
    ∀ᶠ M : ℕ in atTop,
      (-Real.log 2-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))/(M : ℝ)≤
        Real.log (annulusMass M delta)/(M : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,eventually_annulus_polynomial_lower hdelta] with M hM hLower
  have hMr : (0 : ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hlog := Real.log_le_log (by positivity : 0<Real.exp (-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))/2) hLower
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ)≠0),Real.log_exp] at hlog
  have H := div_le_div_of_nonneg_right hlog hMr.le
  convert H using 1 <;> ring

theorem annulus_log_nonpos (M : ℕ) (delta : ℝ) : Real.log (annulusMass M delta)≤0 :=
  Real.log_nonpos (annulusMass_nonneg M delta) (annulusMass_le_one M delta)

theorem annulus_log_div_dimension_tendsto_zero {delta : ℝ} (hdelta : 0<delta) :
    Tendsto (fun M : ℕ => Real.log (annulusMass M delta)/(M : ℝ)) atTop (𝓝 0) := by
  have hConst : Tendsto (fun M : ℕ => (-Real.log 2)/(M : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (-Real.log 2)
  have hLog : Tendsto (fun M : ℕ => RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1)/(M : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using
      log_add_one_div_dimension_tendsto_zero.const_mul RadialTailBounds.tailLogConstant
  have hLower : Tendsto (fun M : ℕ => (-Real.log 2-RadialTailBounds.tailLogConstant*Real.log ((M : ℝ)+1))/(M : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_div,sub_zero] using hConst.sub hLog
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower tendsto_const_nhds
    (eventually_annulus_log_lower hdelta) (.of_forall fun M =>
      div_nonpos_of_nonpos_of_nonneg (annulus_log_nonpos M delta) (Nat.cast_nonneg M))


end
end TensorPCA.NonRSLowerProofs.FiniteCavityAnnulusMassAsymptotics
