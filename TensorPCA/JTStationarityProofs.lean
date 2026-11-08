-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTFirstVariationProofs

/-! Constant-profile variations and their necessary Euler equation. -/
@[expose] public section
namespace TensorPCA.JTStationarityProofs
open Set Filter MeasureTheory JTFirstVariationProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem hasDerivAt_parisiFunctional_constShift {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ) :
    HasDerivAt (fun c : ℝ => Scalar.parisiFunctional xi h (fun t => p t+c))
      ((h^2+deriv xi 0)+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2) 0 := by
  let A := h^2+deriv xi 0
  let G := fun c : ℝ => A+(∫ t in (0 : ℝ)..1, deriv (deriv xi) t)-reciprocalKernelIntegral p c
  have hxiInt : IntervalIntegrable (deriv (deriv xi)) volume 0 1 :=
    hxi.intervalIntegrable_of_Icc zero_le_one
  have hInv2 : IntervalIntegrable (fun t => 1/(p t)^2) volume 0 1 :=
    (continuousOn_const.div (hp.1.pow 2)
      (fun t ht => pow_ne_zero 2 (hp.2.2.2 t ht).ne')).intervalIntegrable_of_Icc zero_le_one
  have hG : Continuous G := continuous_const.sub (continuous_reciprocalKernelIntegral hp)
  have hG0 : G 0 = A+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2 := by
    dsimp only [G]
    rw [reciprocalKernelIntegral_zero hp,intervalIntegral.integral_sub hxiInt hInv2]
    ring
  have hF0 : Scalar.parisiFunctional xi h (fun t => p t+(0 : ℝ)) = Scalar.parisiFunctional xi h p := by
    congr 1
    funext t
    ring
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simp only [zero_add,smul_eq_mul,hF0]
  have hlim : Tendsto G (𝓝[≠] (0 : ℝ))
      (𝓝 ((h^2+deriv xi 0)+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2)) := by
    rw [← hG0]
    exact hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp1 := profile_one_pos hp
  have hnear0 : ∀ᶠ c : ℝ in 𝓝 0, -p 1/2 < c := Ioi_mem_nhds (by linarith : -p 1/2 < 0)
  have hnear : ∀ᶠ c : ℝ in 𝓝[≠] 0, -p 1/2 < c := hnear0.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ c : ℝ in 𝓝[≠] 0, c ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    simpa using hc
  have heq : (fun c : ℝ => c⁻¹*(Scalar.parisiFunctional xi h (fun t => p t+c)-
      Scalar.parisiFunctional xi h p)) =ᶠ[𝓝[≠] 0] G := by
    filter_upwards [hnear,hne] with c hc hcn
    have hshift : -p 1 < c := by linarith
    have hKcont : Continuous (reciprocalKernel p c) :=
      (continuous_reciprocalKernel hp).comp (continuous_const.prodMk continuous_id)
    have hInt : (∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t*(p t+c))) =
        (∫ t in (0 : ℝ)..1, deriv (deriv xi) t-reciprocalKernel p c t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change deriv (deriv xi) t-1/(p t*(p t+c)) = deriv (deriv xi) t-reciprocalKernel p c t
      rw [reciprocalKernel_eq hc.le (by simpa using ht)]
    have hInner : A+(∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t*(p t+c))) = G c := by
      rw [hInt,intervalIntegral.integral_sub hxiInt (hKcont.intervalIntegrable 0 1)]
      dsimp [G,reciprocalKernelIntegral]
      ring
    rw [parisiFunctional_constShift_difference hp hxi h hshift]
    change c⁻¹*(c*(A+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t*(p t+c)))) = G c
    rw [hInner,← mul_assoc,inv_mul_cancel₀ hcn,one_mul]
  exact (tendsto_congr' heq).mpr hlim

theorem minimizer_constant_euler {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hmin : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q) :
    (h^2+deriv xi 0)+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2 = 0 := by
  have hp1 := profile_one_pos hp
  have hlocal : IsLocalMin (fun c : ℝ => Scalar.parisiFunctional xi h (fun t => p t+c)) 0 := by
    filter_upwards [Ioi_mem_nhds (by linarith : -p 1 < 0)] with c hc
    have hh := hmin (fun t => p t+c) (admissibleProfile_constShift hp hc)
    simpa only [add_zero] using hh
  exact hlocal.hasDerivAt_eq_zero (hasDerivAt_parisiFunctional_constShift hp hxi h)


end
end TensorPCA.JTStationarityProofs
