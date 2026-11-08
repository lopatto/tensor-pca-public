-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTOptimalityProofs

/-! The dual-gap inequality obtained from admissible hinge directions. -/
@[expose] public section
namespace TensorPCA.JTObstacleProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def hinge (q t : ℝ) : ℝ := 1-max t q

theorem hinge_continuous (q : ℝ) : Continuous (hinge q) := by
  unfold hinge
  fun_prop

theorem hinge_antitone (q : ℝ) : Antitone (hinge q) := by
  intro x y hxy
  exact sub_le_sub_left (max_le_max hxy le_rfl) 1

theorem hinge_concave (q : ℝ) : ConcaveOn ℝ (Icc (0 : ℝ) 1) (hinge q) := by
  refine ⟨convex_Icc 0 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hmax : max (a*x+b*y) q ≤ a*max x q+b*max y q := by
    apply max_le
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left x q) ha)
        (mul_le_mul_of_nonneg_left (le_max_left y q) hb)
    · calc
        q = a*q+b*q := by rw [← add_mul,hab,one_mul]
        _ ≤ a*max x q+b*max y q :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_right x q) ha)
            (mul_le_mul_of_nonneg_left (le_max_right y q) hb)
  change a*(1-max x q)+b*(1-max y q) ≤ 1-max (a*x+b*y) q
  nlinarith

theorem hinge_nonneg {q t : ℝ} (hq : q ≤ 1) (ht : t ≤ 1) : 0 ≤ hinge q t :=
  sub_nonneg.mpr (max_le ht hq)

theorem admissibleProfile_add_hinge {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {q c : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    Scalar.AdmissibleProfile (fun t => p t+c*hinge q t) := by
  refine ⟨hp.1.add ((hinge_continuous q).continuousOn.const_mul c),?_,?_,?_⟩
  · intro x hx y hy hxy
    exact add_le_add (hp.2.1 hx hy hxy)
      (mul_le_mul_of_nonneg_left (hinge_antitone q hxy) hc)
  · exact hp.2.2.1.add (ConcaveOn.smul hc (hinge_concave q))
  · intro t ht
    exact add_pos_of_pos_of_nonneg (hp.2.2.2 t ht)
      (mul_nonneg hc (hinge_nonneg hq.2 ht.2))

def obstacleGap (xi : ℝ → ℝ) (h : ℝ) (p : ℝ → ℝ) (q : ℝ) : ℝ :=
  JTOptimalityProofs.firstVariation xi h p (hinge q)

theorem minimizer_obstacleGap_nonneg {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hmin : ∀ r : ℝ → ℝ, Scalar.AdmissibleProfile r →
      Scalar.parisiFunctional xi h p ≤ Scalar.parisiFunctional xi h r)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    0 ≤ obstacleGap xi h p q := by
  have hAd : Scalar.AdmissibleProfile (fun t => p t+hinge q t) := by
    simpa only [one_mul] using admissibleProfile_add_hinge hp hq (c := 1) zero_le_one
  have H := JTOptimalityProofs.minimizer_firstVariation_nonneg hp hxi h hmin _ hAd
  have he : (fun t => p t+hinge q t-p t) = hinge q := by
    funext t
    ring
  simpa only [he,obstacleGap] using H

theorem obstacleGap_one (xi p : ℝ → ℝ) (h : ℝ) : obstacleGap xi h p 1 = 0 := by
  unfold obstacleGap JTOptimalityProofs.firstVariation
  have hint : (∫ t in (0 : ℝ)..1,
      (deriv (deriv xi) t-1/(p t)^2)*hinge 1 t) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht1 : t ≤ 1 := (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht).2
        simp only [hinge,max_eq_right ht1,sub_self,mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hint]
  norm_num [hinge]


end
end TensorPCA.JTObstacleProofs
