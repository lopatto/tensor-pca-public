-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTDirectionalProofs
public import TensorPCA.PureVariationalProofs

/-! The variational inequality characterizing an admissible minimizer. -/
@[expose] public section
namespace TensorPCA.JTOptimalityProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def firstVariation (xi : ℝ → ℝ) (h : ℝ) (p r : ℝ → ℝ) : ℝ :=
  (h^2+deriv xi 0)*r 0+∫ t in (0 : ℝ)..1, (deriv (deriv xi) t-1/(p t)^2)*r t

theorem hasDerivAt_firstVariation {xi p r : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (hr : ContinuousOn r (Icc (0 : ℝ) 1)) (h : ℝ) :
    HasDerivAt (fun c : ℝ => Scalar.parisiFunctional xi h (fun t => p t+c*r t))
      (firstVariation xi h p r) 0 := by
  apply (JTDirectionalProofs.hasDerivAt_parisiFunctional_direction hp hxi hr h).congr_deriv
  unfold firstVariation
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem admissibleProfile_combination {p q : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p) (hq : Scalar.AdmissibleProfile q)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    Scalar.AdmissibleProfile (fun t => (1-c)*p t+c*q t) := by
  have hc1 : 0 ≤ 1-c := sub_nonneg.mpr hc.2
  refine ⟨(hp.1.const_mul (1-c)).add (hq.1.const_mul c),?_,?_,?_⟩
  · intro x hx y hy hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hp.2.1 hx hy hxy) hc1)
      (mul_le_mul_of_nonneg_left (hq.2.1 hx hy hxy) hc.1)
  · exact (ConcaveOn.smul hc1 hp.2.2.1).add (ConcaveOn.smul hc.1 hq.2.2.1)
  · intro t ht
    by_cases hlt : c < 1
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) (hp.2.2.2 t ht))
        (mul_nonneg hc.1 (hq.2.2.2 t ht).le)
    · have he : c = 1 := le_antisymm hc.2 (le_of_not_gt hlt)
      subst c
      simpa only [sub_self,zero_mul,one_mul,zero_add] using hq.2.2.2 t ht

theorem minimizer_firstVariation_nonneg {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hmin : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q)
    (q : ℝ → ℝ) (hq : Scalar.AdmissibleProfile q) :
    0 ≤ firstVariation xi h p (fun t => q t-p t) := by
  let F := fun c : ℝ => Scalar.parisiFunctional xi h (fun t => p t+c*(q t-p t))
  have hd : HasDerivAt F (firstVariation xi h p (fun t => q t-p t)) 0 :=
    hasDerivAt_firstVariation hp hxi (hq.1.sub hp.1) h
  have hF0 : F 0 = Scalar.parisiFunctional xi h p := by
    change Scalar.parisiFunctional xi h (fun t => p t+0*(q t-p t)) = _
    simp only [zero_mul,add_zero]
  by_contra hnot
  have hneg : firstVariation xi h p (fun t => q t-p t) < 0 := lt_of_not_ge hnot
  have hslope : ∀ᶠ c : ℝ in 𝓝[>] 0, c⁻¹*(F c-F 0) < 0 := by
    simpa only [smul_eq_mul,zero_add] using hd.tendsto_slope_zero_right.eventually (Iio_mem_nhds hneg)
  have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  have hsmall0 : ∀ᶠ c : ℝ in 𝓝 0, c < 1 := Iio_mem_nhds zero_lt_one
  have hsmall : ∀ᶠ c : ℝ in 𝓝[>] 0, c < 1 := hsmall0.filter_mono nhdsWithin_le_nhds
  obtain ⟨c,hcpos,hcsmall,hcslope⟩ := (hpos.and (hsmall.and hslope)).exists
  have hAd : Scalar.AdmissibleProfile (fun t => p t+c*(q t-p t)) := by
    have he : (fun t => p t+c*(q t-p t)) = (fun t => (1-c)*p t+c*q t) := by
      funext t
      ring
    rw [he]
    exact admissibleProfile_combination hp hq ⟨hcpos.le,hcsmall.le⟩
  have hF : F 0 ≤ F c := by rw [hF0]; exact hmin _ hAd
  have hn := mul_nonneg (inv_nonneg.mpr hcpos.le) (sub_nonneg.mpr hF)
  exact not_lt_of_ge hn hcslope

theorem minimal_of_firstVariation_nonneg {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hvar : ∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      0 ≤ firstVariation xi h p (fun t => q t-p t))
    (q : ℝ → ℝ) (hq : Scalar.AdmissibleProfile q) :
    Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q := by
  have hpinv : ContinuousOn (fun t => 1/p t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp.1 (fun t ht => (hp.2.2.2 t ht).ne')
  have hqinv : ContinuousOn (fun t => 1/q t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hq.1 (fun t ht => (hq.2.2.2 t ht).ne')
  have hv : ContinuousOn (fun t => deriv (deriv xi) t-1/(p t)^2) (Icc (0 : ℝ) 1) :=
    hxi.sub (continuousOn_const.div (hp.1.pow 2)
      (fun t ht => pow_ne_zero _ (hp.2.2.2 t ht).ne'))
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv xi) t*p t+1/p t+
        (deriv (deriv xi) t-1/(p t)^2)*(q t-p t) ≤
        deriv (deriv xi) t*q t+1/q t := by
    intro t ht
    have H := PureVariationalProofs.reciprocal_tangent
      (hp.2.2.2 t ht) (hq.2.2.2 t ht)
    have hid : deriv (deriv xi) t*p t+1/p t+
        (deriv (deriv xi) t-1/(p t)^2)*(q t-p t) =
        deriv (deriv xi) t*q t+(2/p t-q t/(p t)^2) := by
      field_simp [(hp.2.2.2 t ht).ne']
      ring
    rw [hid]
    linarith
  have H := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (f := fun t => deriv (deriv xi) t*p t+1/p t+
      (deriv (deriv xi) t-1/(p t)^2)*(q t-p t))
    (g := fun t => deriv (deriv xi) t*q t+1/q t)
    ((((hxi.mul hp.1).add hpinv).add (hv.mul (hq.1.sub hp.1))).intervalIntegrable_of_Icc zero_le_one)
    (((hxi.mul hq.1).add hqinv).intervalIntegrable_of_Icc zero_le_one) hpoint
  rw [intervalIntegral.integral_add
    (f := fun t => deriv (deriv xi) t*p t+1/p t)
    (g := fun t => (deriv (deriv xi) t-1/(p t)^2)*(q t-p t))
    (((hxi.mul hp.1).add hpinv).intervalIntegrable_of_Icc zero_le_one)
    ((hv.mul (hq.1.sub hp.1)).intervalIntegrable_of_Icc zero_le_one)] at H
  have hvq := hvar q hq
  unfold firstVariation at hvq
  unfold Scalar.parisiFunctional
  linarith

theorem minimizer_iff_firstVariation_nonneg {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ) :
    (∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h q) ↔
    (∀ q : ℝ → ℝ, Scalar.AdmissibleProfile q →
      0 ≤ firstVariation xi h p (fun t => q t-p t)) :=
  ⟨minimizer_firstVariation_nonneg hp hxi h,
    minimal_of_firstVariation_nonneg hp hxi h⟩


end
end TensorPCA.JTOptimalityProofs
