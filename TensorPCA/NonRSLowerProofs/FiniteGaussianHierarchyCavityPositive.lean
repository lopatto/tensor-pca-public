-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyPrefixGaussian
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthBridge

/-! Thermal covariance and full theta correction bind the uniform spherical endpoint to
the CS minimum for positive-height finite hierarchies.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyCavityPositive
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCS FiniteCSGaussianDepthPrecision FiniteCSGaussianDepthMoment
open FiniteCSGaussianDepthComparison FiniteCSGaussianDepthBridge
open FiniteCSGaussianThreeAtomBridge FiniteCSGaussianThreeAtomComparison
open FiniteGaussianQuadraticUniformEndpoint FiniteGaussianQuadraticSphericalStages
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem thermal_theta_monotone (k : ℕ) (beta : ℝ) {m : ℝ} (hm : m∈Icc (-1 : ℝ) 1) :
    MonotoneOn (fun t => t*(beta^2*deriv (Scalar.xiSlice k m) t)-beta^2*Scalar.xiSlice k m t) (Ici 0) := by
  intro a ha b hb hab
  have HB := convex_bregman_nonneg (thermal_xiSlice_convex_nonneg k beta hm) ha hb
    (thermal_xiSlice_hasDerivAt k beta m b)
  have HD : beta^2*deriv (Scalar.xiSlice k m) a≤beta^2*deriv (Scalar.xiSlice k m) b :=
    mul_le_mul_of_nonneg_left (xiSlice_deriv_mono_nonneg_overlap k hm ha hab) (sq_nonneg beta)
  have HP := mul_nonneg ha (sub_nonneg.mpr HD)
  nlinarith only [HB,HP]

theorem positive_height_cavity_lower (k : ℕ) (hk : 1≤k) {beta m delta error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1)
    (hdelta : 0<delta) (hdelta1 : delta≤1) (herror : 0<error) :
    ∀ᶠ M : ℕ in atTop,∀(d : ℕ) (x : Fin d→ℝ) (q : Fin (d+1)→ℝ),
      (∀j,delta≤x j)→Monotone x→(∀j,x j≤1)→
      0≤q 0→Monotone q→q (Fin.last d)=1→
      let y := fun i : Fin (d+1) => beta^2*deriv (Scalar.xiSlice k m) (q i)
      let z := fun i : Fin (d+1) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
      beta*(rawValue k beta m).toReal/2-error≤
        (∫g : Model.Vector M,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)/(M : ℝ)
          ∂stdGaussian (Model.Vector M))-(∑j : Fin d,x j*increments z j)/2 := by
  let ymin := beta^2*deriv (Scalar.xiSlice k m) 0
  let Y := beta^2*deriv (Scalar.xiSlice k m) 1
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  have hymin : 0<ymin := mul_pos (sq_pos_of_pos hbeta)
    (xiSlice_deriv_pos_nonneg_overlap k hk hm0 hm1 (le_refl (0 : ℝ)))
  have HT := uniform_spherical_endpoint (Y := Y) hymin hdelta hdelta1 herror
  filter_upwards [HT] with M HM
  intro d x q hxLower hxm hx1 hq0 hqm hqend
  let y := fun i : Fin (d+1) => beta^2*deriv (Scalar.xiSlice k m) (q i)
  let z := fun i : Fin (d+1) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
  change beta*(rawValue k beta m).toReal/2-error≤
    (∫g : Model.Vector M,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)/(M : ℝ)
      ∂stdGaussian (Model.Vector M))-(∑j : Fin d,x j*increments z j)/2
  have hx : ∀j,0<x j := fun j => hdelta.trans_le (hxLower j)
  have hq (i : Fin (d+1)) : 0≤q i := hq0.trans (hqm (Fin.zero_le i))
  have hym : Monotone y := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (xiSlice_deriv_mono_nonneg_overlap k hm (hq i) (hqm hij)) (sq_nonneg beta)
  have hDelta (j : Fin d) : 0≤ increments y j :=
    sub_nonneg.mpr (hym (show j.castSucc≤j.succ by change (j : ℕ)≤(j : ℕ)+1; omega))
  have hyFloor : ymin≤y 0 := mul_le_mul_of_nonneg_left
    (xiSlice_deriv_mono_nonneg_overlap k hm (le_refl (0 : ℝ)) hq0) (sq_nonneg beta)
  have hy : 0<y 0 := hymin.trans_le hyFloor
  have hTotal : y 0+(∑j : Fin d,increments y j)=Y := by
    have H := sum_adjacent_sub y
    have Hend : y (Fin.last d)=Y := by dsimp only [y,Y]; rw [hqend]
    rw [Hend] at H
    change (∑j : Fin d,increments y j)=Y-y 0 at H
    linarith only [H]
  obtain ⟨B,hB,hroot,hmin⟩ := exists_depth_minimizing_root x (increments y) hx hDelta hy
  have HS := HM d x (increments y) B (y 0) hxLower hxm hx1 hDelta hB hyFloor hTotal.le hroot
  have hBcs : tail (fun j : Fin d => x j*(beta^2*deriv (Scalar.xiSlice k m) (q j.succ)-
      beta^2*deriv (Scalar.xiSlice k m) (q j.castSucc))) 0<B := hB
  have HCS := rawValue_le_depthGaussianValue k hk hbeta hm0 hm1 x q hx hx1 hxm hq0 hqm hqend hBcs
  change beta*(rawValue k beta m).toReal≤
    depthCost x (increments y) (y 0) B-(∑j : Fin d,x j*increments z j) at HCS
  linarith only [HS,HCS]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyCavityPositive
