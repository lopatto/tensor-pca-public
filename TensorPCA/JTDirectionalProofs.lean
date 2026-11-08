-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTStationarityProofs

/-! Directional first variations of the zero-temperature functional. -/
@[expose] public section
namespace TensorPCA.JTDirectionalProofs
open Set Filter MeasureTheory JTFirstVariationProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem continuous_directionExtend {r : ℝ → ℝ} (hr : ContinuousOn r (Icc (0 : ℝ) 1)) :
    Continuous (profileExtend r) := by
  change Continuous (r ∘ clamp)
  exact hr.comp_continuous (by unfold clamp; fun_prop) clamp_mem

theorem exists_direction_bound {r : ℝ → ℝ} (hr : ContinuousOn r (Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc (0 : ℝ) 1, |r t| ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image hr.norm
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro t ht
  have hb : |r t| ≤ M := by simpa only [Real.norm_eq_abs] using hM ⟨t,ht,rfl⟩
  exact hb.trans (le_max_left _ _)

def directionKernel (p r : ℝ → ℝ) (c t : ℝ) : ℝ :=
  profileExtend r t/(profileExtend p t*max (profileExtend p t+c*profileExtend r t) (p 1/2))

theorem continuous_directionKernel {p r : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hr : ContinuousOn r (Icc (0 : ℝ) 1)) : Continuous (directionKernel p r).uncurry := by
  have hP : Continuous (fun z : ℝ × ℝ => profileExtend p z.2) :=
    (continuous_profileExtend hp).comp continuous_snd
  have hR : Continuous (fun z : ℝ × ℝ => profileExtend r z.2) :=
    (continuous_directionExtend hr).comp continuous_snd
  have hden : Continuous (fun z : ℝ × ℝ => profileExtend p z.2*
      max (profileExtend p z.2+z.1*profileExtend r z.2) (p 1/2)) :=
    hP.mul ((hP.add (continuous_fst.mul hR)).max continuous_const)
  apply hR.div hden
  intro z
  have hp1 := profile_one_pos hp
  have hlow := profileExtend_lower hp z.2
  exact mul_ne_zero (by linarith)
    (ne_of_gt ((by linarith : 0 < p 1/2).trans_le (le_max_right _ _)))

theorem directionKernel_eq {p r : ℝ → ℝ} {c t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hpos : p 1/2 ≤ p t+c*r t) :
    directionKernel p r c t = r t/(p t*(p t+c*r t)) := by
  simp only [directionKernel,profileExtend,clamp_eq ht,max_eq_left hpos]

theorem directionKernel_zero {p r : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    directionKernel p r 0 t = r t/(p t)^2 := by
  have hp1 := profile_one_pos hp
  rw [directionKernel_eq ht (by linarith [profile_lower hp ht])]
  rw [zero_mul,add_zero,pow_two]

def directionKernelIntegral (p r : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, directionKernel p r c t

theorem continuous_directionKernelIntegral {p r : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hr : ContinuousOn r (Icc (0 : ℝ) 1)) : Continuous (directionKernelIntegral p r) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (continuous_directionKernel hp hr) (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  convert hc using 1
  funext c
  unfold directionKernelIntegral
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]

theorem directionKernelIntegral_zero {p r : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    directionKernelIntegral p r 0 = ∫ t in (0 : ℝ)..1, r t/(p t)^2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact directionKernel_zero hp (by simpa using ht)

theorem exists_positive_direction_radius {p r : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hr : ContinuousOn r (Icc (0 : ℝ) 1)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ c : ℝ, |c| < delta →
      ∀ t ∈ Icc (0 : ℝ) 1, p 1/2 < p t+c*r t := by
  obtain ⟨M,hM,hbound⟩ := exists_direction_bound hr
  have hp1 := profile_one_pos hp
  refine ⟨p 1/(2*M),by positivity,?_⟩
  intro c hc t ht
  have hsmall : |c| * M < p 1/2 := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*M)).mp hc
    nlinarith
  have hprod : |c*r t| ≤ |c| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg c)
  nlinarith [neg_abs_le (c*r t),profile_lower hp ht]

theorem parisiFunctional_direction_difference {xi p r : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hr : ContinuousOn r (Icc (0 : ℝ) 1)) (h c : ℝ)
    (hqpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < p t+c*r t) :
    Scalar.parisiFunctional xi h (fun t => p t+c*r t)-Scalar.parisiFunctional xi h p =
      c*((h^2+deriv xi 0)*r 0+∫ t in (0 : ℝ)..1,
        deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t))) := by
  have hq : ContinuousOn (fun t => p t+c*r t) (Icc (0 : ℝ) 1) := hp.1.add (hr.const_mul c)
  have hInvP : ContinuousOn (fun t => 1/p t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp.1 (fun t ht => (hp.2.2.2 t ht).ne')
  have hInvQ : ContinuousOn (fun t => 1/(p t+c*r t)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hq (fun t ht => (hqpos t ht).ne')
  have hP : IntervalIntegrable (fun t => deriv (deriv xi) t*p t+1/p t) volume 0 1 :=
    ((hxi.mul hp.1).add hInvP).intervalIntegrable_of_Icc zero_le_one
  have hQ : IntervalIntegrable (fun t => deriv (deriv xi) t*(p t+c*r t)+1/(p t+c*r t)) volume 0 1 :=
    ((hxi.mul hq).add hInvQ).intervalIntegrable_of_Icc zero_le_one
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (deriv (deriv xi) t*(p t+c*r t)+1/(p t+c*r t))-(deriv (deriv xi) t*p t+1/p t) =
        c*(deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t))) := by
    have hpn : p t ≠ 0 := (hp.2.2.2 t ht).ne'
    have hqn : p t+c*r t ≠ 0 := (hqpos t ht).ne'
    field_simp [hpn,hqn]
    ring
  have hi : (∫ t in (0 : ℝ)..1, deriv (deriv xi) t*(p t+c*r t)+1/(p t+c*r t))-
      (∫ t in (0 : ℝ)..1, deriv (deriv xi) t*p t+1/p t) =
      c*(∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t))) := by
    rw [← intervalIntegral.integral_sub hQ hP,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact he t (by simpa using ht)
  unfold Scalar.parisiFunctional
  nlinarith [hi]

theorem hasDerivAt_parisiFunctional_direction {xi p r : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hr : ContinuousOn r (Icc (0 : ℝ) 1)) (h : ℝ) :
    HasDerivAt (fun c : ℝ => Scalar.parisiFunctional xi h (fun t => p t+c*r t))
      ((h^2+deriv xi 0)*r 0+∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t)^2) 0 := by
  let A := (h^2+deriv xi 0)*r 0
  let G := fun c : ℝ => A+(∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t)-directionKernelIntegral p r c
  have hLin : IntervalIntegrable (fun t => deriv (deriv xi) t*r t) volume 0 1 :=
    (hxi.mul hr).intervalIntegrable_of_Icc zero_le_one
  have hInv : IntervalIntegrable (fun t => r t/(p t)^2) volume 0 1 :=
    (hr.div (hp.1.pow 2) (fun t ht => pow_ne_zero 2 (hp.2.2.2 t ht).ne')).intervalIntegrable_of_Icc zero_le_one
  have hG : Continuous G := continuous_const.sub (continuous_directionKernelIntegral hp hr)
  have hG0 : G 0 = A+∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t)^2 := by
    dsimp only [G]
    rw [directionKernelIntegral_zero hp,intervalIntegral.integral_sub hLin hInv]
    ring
  have hF0 : Scalar.parisiFunctional xi h (fun t => p t+(0 : ℝ)*r t) = Scalar.parisiFunctional xi h p := by
    congr 1
    funext t
    ring
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simp only [zero_add,smul_eq_mul,hF0]
  have hlim : Tendsto G (𝓝[≠] (0 : ℝ))
      (𝓝 ((h^2+deriv xi 0)*r 0+∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t)^2)) := by
    rw [← hG0]
    exact hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨delta,hdelta,hgood⟩ := exists_positive_direction_radius hp hr
  have hnear0 : ∀ᶠ c : ℝ in 𝓝 0, c ∈ Ioo (-delta) delta :=
    Ioo_mem_nhds (by linarith : -delta < 0) hdelta
  have hnear : ∀ᶠ c : ℝ in 𝓝[≠] 0, |c| < delta :=
    (hnear0.filter_mono nhdsWithin_le_nhds).mono (fun _ hc => abs_lt.mpr hc)
  have hne : ∀ᶠ c : ℝ in 𝓝[≠] 0, c ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    simpa using hc
  have heq : (fun c : ℝ => c⁻¹*(Scalar.parisiFunctional xi h (fun t => p t+c*r t)-
      Scalar.parisiFunctional xi h p)) =ᶠ[𝓝[≠] 0] G := by
    filter_upwards [hnear,hne] with c hc hcn
    have hgood' := hgood c hc
    have hp1 := profile_one_pos hp
    have hQpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < p t+c*r t := by
      intro t ht
      linarith [hgood' t ht]
    have hKcont : Continuous (directionKernel p r c) :=
      (continuous_directionKernel hp hr).comp (continuous_const.prodMk continuous_id)
    have hInt : (∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t))) =
        (∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-directionKernel p r c t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t)) =
        deriv (deriv xi) t*r t-directionKernel p r c t
      rw [directionKernel_eq (by simpa using ht) (hgood' t (by simpa using ht)).le]
    have hInner : A+(∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t))) = G c := by
      rw [hInt,intervalIntegral.integral_sub hLin (hKcont.intervalIntegrable 0 1)]
      dsimp [G,directionKernelIntegral]
      ring
    rw [parisiFunctional_direction_difference hp hxi hr h c hQpos]
    change c⁻¹*(c*(A+∫ t in (0 : ℝ)..1, deriv (deriv xi) t*r t-r t/(p t*(p t+c*r t)))) = G c
    rw [hInner,← mul_assoc,inv_mul_cancel₀ hcn,one_mul]
  exact (tendsto_congr' heq).mpr hlim


end
end TensorPCA.JTDirectionalProofs
