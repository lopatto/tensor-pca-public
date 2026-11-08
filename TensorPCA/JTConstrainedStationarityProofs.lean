-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTConstrainedContactProofs

/-! Constrained Euler conditions for a candidate minimizer above a
positive constant floor. Existence of such a candidate is not assumed as a
theorem; these are necessary conditions used in the later compactness argument. -/
@[expose] public section
namespace TensorPCA.JTConstrainedStationarityProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem hasDerivAt_nonneg_of_right_min {F : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt F d 0)
    (hmin : ∀ c : ℝ, 0 ≤ c → F 0 ≤ F c) : 0 ≤ d := by
  by_contra hnot
  have hneg := lt_of_not_ge hnot
  have hslope : ∀ᶠ c : ℝ in 𝓝[>] 0, c⁻¹*(F c-F 0) < 0 := by
    simpa only [smul_eq_mul,zero_add] using hd.tendsto_slope_zero_right.eventually (Iio_mem_nhds hneg)
  have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  obtain ⟨c,hc,hcslope⟩ := (hpos.and hslope).exists
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hc.le)
    (sub_nonneg.mpr (hmin c hc.le))) hcslope

theorem floor_scale_lower {p : ℝ → ℝ} {eps c : ℝ}
    (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t) (hc : -1 < c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : eps ≤ p t+c*(p t-eps) := by
  have H := mul_nonneg (show 0 ≤ 1+c by linarith) (sub_nonneg.mpr (hfloor t ht))
  nlinarith

theorem floor_scale_admissible {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {eps c : ℝ} (heps : 0 < eps) (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hc : -1 < c) : Scalar.AdmissibleProfile (fun t => p t+c*(p t-eps)) := by
  have hC : 0 < 1+c := by linarith
  refine ⟨hp.1.add ((hp.1.sub continuousOn_const).const_mul c),?_,?_,?_⟩
  · intro x hx y hy hxy
    have H := mul_le_mul_of_nonneg_left (hp.2.1 hx hy hxy) hC.le
    nlinarith
  · have H := (ConcaveOn.smul hC.le hp.2.2.1).add
      (concaveOn_const (-c*eps) (convex_Icc (0 : ℝ) 1))
    exact H.congr (fun t ht => by change (1+c)*p t+(-c*eps) = p t+c*(p t-eps); ring)
  · intro t ht
    exact heps.trans_le (floor_scale_lower hfloor hc t ht)

theorem floor_minimizer_constant_euler_nonneg {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h eps : ℝ)
    (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ r t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r) :
    0 ≤ (h^2+deriv xi 0)+∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2 := by
  apply hasDerivAt_nonneg_of_right_min (JTStationarityProofs.hasDerivAt_parisiFunctional_constShift hp hxi h)
  intro c hc
  have hAd := JTFirstVariationProofs.admissibleProfile_constShift hp
    (show -p 1 < c by linarith [hp.2.2.2 1 (by norm_num)])
  have H := hmin _ hAd (fun t ht => (hfloor t ht).trans (le_add_of_nonneg_right hc))
  simpa only [add_zero] using H

theorem floor_minimizer_scaling_euler {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    {eps : ℝ} (heps : 0 < eps) (hfloor : ∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ r t) →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r) :
    JTOptimalityProofs.firstVariation xi h p (fun t => p t-eps) = 0 := by
  let F := fun c : ℝ => Scalar.parisiFunctional xi h (fun t => p t+c*(p t-eps))
  have hd : HasDerivAt F (JTOptimalityProofs.firstVariation xi h p (fun t => p t-eps)) 0 :=
    JTOptimalityProofs.hasDerivAt_firstVariation hp hxi (hp.1.sub continuousOn_const) h
  have hF0 : F 0 = Scalar.parisiFunctional xi h p := by
    change Scalar.parisiFunctional xi h (fun t => p t+0*(p t-eps)) = _
    simp only [zero_mul,add_zero]
  have hlocal : IsLocalMin F 0 := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with c hc
    change F 0 ≤ F c
    rw [hF0]
    exact hmin _ (floor_scale_admissible hp heps hfloor hc) (floor_scale_lower hfloor hc)
  exact hlocal.hasDerivAt_eq_zero hd


end
end TensorPCA.JTConstrainedStationarityProofs
