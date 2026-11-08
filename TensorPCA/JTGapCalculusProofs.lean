-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTObstacleProofs

/-! Twice differentiable extension of the hinge gap. The clamp affects
only values outside the variational interval. -/
@[expose] public section
namespace TensorPCA.JTGapCalculusProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def extendedWeight (xi p : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv xi) (JTFirstVariationProofs.clamp t)-
    1/(JTFirstVariationProofs.profileExtend p t)^2

theorem extendedWeight_eq {xi p : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extendedWeight xi p t = deriv (deriv xi) t-1/(p t)^2 := by
  simp only [extendedWeight,JTFirstVariationProofs.profileExtend,
    JTFirstVariationProofs.clamp_eq ht]

theorem continuous_extendedWeight {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) :
    Continuous (extendedWeight xi p) := by
  have hc : Continuous (JTFirstVariationProofs.clamp) := by
    unfold JTFirstVariationProofs.clamp
    fun_prop
  have hw : Continuous (fun t => deriv (deriv xi) (JTFirstVariationProofs.clamp t)) :=
    hxi.comp_continuous hc JTFirstVariationProofs.clamp_mem
  have hpcont := JTFirstVariationProofs.continuous_profileExtend hp
  exact hw.sub (continuous_const.div (hpcont.pow 2) (fun t =>
    pow_ne_zero _ (hp.2.2.2 _ (JTFirstVariationProofs.clamp_mem t)).ne'))

def gapPrimitive (w : ℝ → ℝ) (A q : ℝ) : ℝ :=
  (1-q)*(A+∫ t in (0 : ℝ)..q, w t)+∫ t in q..1, (1-t)*w t

theorem gapPrimitive_eq_hinge {w : ℝ → ℝ} (hw : Continuous w) (A : ℝ)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    gapPrimitive w A q = A*(1-q)+
      ∫ t in (0 : ℝ)..1, w t*JTObstacleProofs.hinge q t := by
  have hc : Continuous (fun t => w t*JTObstacleProofs.hinge q t) :=
    hw.mul (JTObstacleProofs.hinge_continuous q)
  have hleft : (∫ t in (0 : ℝ)..q, w t*JTObstacleProofs.hinge q t) =
      (1-q)*∫ t in (0 : ℝ)..q, w t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have htq : t ≤ q := (uIcc_of_le hq.1 ▸ ht).2
    simp only [JTObstacleProofs.hinge,max_eq_right htq]
    ring
  have hright : (∫ t in q..1, w t*JTObstacleProofs.hinge q t) =
      ∫ t in q..1, (1-t)*w t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htq : q ≤ t := (uIcc_of_le hq.2 ▸ ht).1
    simp only [JTObstacleProofs.hinge,max_eq_left htq]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 q)
    (hc.intervalIntegrable q 1),hleft,hright]
  unfold gapPrimitive
  ring

theorem hasDerivAt_gapPrimitive {w : ℝ → ℝ} (hw : Continuous w) (A q : ℝ) :
    HasDerivAt (gapPrimitive w A) (-A-∫ t in (0 : ℝ)..q, w t) q := by
  have hI := intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 q)
    (hw.stronglyMeasurableAtFilter volume (𝓝 q)) hw.continuousAt
  have hc : Continuous (fun t : ℝ => (1-t)*w t) := by fun_prop
  have hJ := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable q 1)
    (hc.stronglyMeasurableAtFilter volume (𝓝 q)) hc.continuousAt
  have hlin : HasDerivAt (fun t : ℝ => 1-t) (-1) q :=
    (hasDerivAt_id q).const_sub 1
  convert ((hlin.mul (hI.const_add A)).add hJ) using 1
  · funext t
    rfl
  · ring

theorem deriv_gapPrimitive {w : ℝ → ℝ} (hw : Continuous w) (A q : ℝ) :
    deriv (gapPrimitive w A) q = -A-∫ t in (0 : ℝ)..q, w t :=
  (hasDerivAt_gapPrimitive hw A q).deriv

theorem hasDerivAt_deriv_gapPrimitive {w : ℝ → ℝ} (hw : Continuous w) (A q : ℝ) :
    HasDerivAt (deriv (gapPrimitive w A)) (-w q) q := by
  have he : deriv (gapPrimitive w A) = (fun q => -A-∫ t in (0 : ℝ)..q, w t) :=
    funext (deriv_gapPrimitive hw A)
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 q)
    (hw.stronglyMeasurableAtFilter volume (𝓝 q)) hw.continuousAt).const_sub (-A)

def gap (xi : ℝ → ℝ) (h : ℝ) (p : ℝ → ℝ) : ℝ → ℝ :=
  gapPrimitive (extendedWeight xi p) (h^2+deriv xi 0)

theorem gap_eq_obstacleGap {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    gap xi h p q = JTObstacleProofs.obstacleGap xi h p q := by
  rw [gap,gapPrimitive_eq_hinge (continuous_extendedWeight hp hxi) _ hq]
  unfold JTObstacleProofs.obstacleGap JTOptimalityProofs.firstVariation
  have hq0 : JTObstacleProofs.hinge q 0 = 1-q := by
    simp only [JTObstacleProofs.hinge,max_eq_right hq.1]
  rw [hq0]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change extendedWeight xi p t*JTObstacleProofs.hinge q t =
    (deriv (deriv xi) t-1/(p t)^2)*JTObstacleProofs.hinge q t
  rw [extendedWeight_eq (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)]

theorem minimizer_gap_nonneg {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ gap xi h p q := by
  rw [gap_eq_obstacleGap hp hxi h hq]
  exact JTObstacleProofs.minimizer_obstacleGap_nonneg hp hxi h hmin hq

theorem gap_one (xi p : ℝ → ℝ) (h : ℝ) : gap xi h p 1 = 0 := by
  simp only [gap,gapPrimitive,sub_self,zero_mul,intervalIntegral.integral_same,add_zero]

theorem hasDerivAt_gap {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h q : ℝ) :
    HasDerivAt (gap xi h p)
      (-(h^2+deriv xi 0)-∫ t in (0 : ℝ)..q, extendedWeight xi p t) q :=
  hasDerivAt_gapPrimitive (continuous_extendedWeight hp hxi) _ q

theorem hasDerivAt_deriv_gap {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h q : ℝ) :
    HasDerivAt (deriv (gap xi h p)) (-extendedWeight xi p q) q :=
  hasDerivAt_deriv_gapPrimitive (continuous_extendedWeight hp hxi) _ q

theorem minimizer_deriv_gap_one {xi p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r) :
    deriv (gap xi h p) 1 = 0 := by
  rw [(hasDerivAt_gap hp hxi h 1).deriv]
  have he : (∫ t in (0 : ℝ)..1, extendedWeight xi p t) =
      ∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact extendedWeight_eq (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)
  rw [he]
  have H := JTStationarityProofs.minimizer_constant_euler hp hxi h hmin
  linarith


end
end TensorPCA.JTGapCalculusProofs
