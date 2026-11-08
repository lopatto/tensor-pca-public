-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyCavityLower
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClippingUniform
public import TensorPCA.NonRSLowerProofs.FiniteGaussianCompensationClippingUniform

/-! Clipped Gaussian cavity lower bound, pointwise in the hierarchy. One cavity-size
threshold works uniformly over all hierarchy depths and heights. Applying the
estimate sectionwise permits integration of bounded clipped marked values without
requiring joint measurability of an unbounded random-height raw tower.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyClippedCavityLower
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCS FiniteCSGaussianDepthMoment FiniteCSGaussianDepthComparison
open FiniteGaussianHierarchyCavityLower FiniteGaussianHierarchyCavityPositive
open FiniteGaussianQuadraticSphericalStages FiniteGaussianQuadraticLogSteps
open FiniteGaussianLogStepsCompression FiniteGaussianLinearLogSteps
open FiniteGaussianSphericalNumeratorClippingUniform FiniteGaussianCompensationClippingUniform
open OneStepGaussianTiltEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem clipped_cavity_lower (k : ℕ) (hk : 1≤k) {beta m error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1) (herror : 0<error) :
    ∀ᶠ M : ℕ in atTop,0<M ∧ ∀(d : ℕ) (x : Fin d→ℝ) (q : Fin (d+1)→ℝ)
      (LN b cap : ℝ),
      (∀j,0<x j) → Monotone x → (∀j,x j≤1) →
      0≤q 0 → Monotone q → q (Fin.last d)=1 →
      1≤LN → 0<b → b≤1 → 1≤cap →
      let y := fun i : Fin (d+1) => beta^2*deriv (Scalar.xiSlice k m) (q i)
      let z := fun i : Fin (d+1) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
      let num := ∫g : Model.Vector M,gaussianLogSteps (quadraticSteps M x (increments y))
        (fun h => min (Real.log (sphericalLaplace M h)) (Real.log LN)) (Real.sqrt (y 0) •g)
        ∂stdGaussian (Model.Vector M)
      let comp := ∫g : Model.Vector 1,gaussianLogSteps (quadraticSteps 1 x (increments z))
        (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt (z 0) •g)
        ∂stdGaussian (Model.Vector 1)
      beta*(rawValue k beta m).toReal/2-error-
        (Real.exp (2*(M : ℝ)*(beta^2*deriv (Scalar.xiSlice k m) 1))/LN+
          (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*(beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1))))/(M : ℝ)≤
        num/(M : ℝ)-comp/(M : ℝ) := by
  have HT := cavity_lower k hk hbeta hm0 hm1 herror
  filter_upwards [HT,eventually_gt_atTop (0 : ℕ)] with M HM hM
  refine ⟨hM,?_⟩
  intro d x q LN b cap hx hxm hx1 hq0 hqm hqend hLN hb hb1 hcap
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  let y := fun i : Fin (d+1) => beta^2*deriv (Scalar.xiSlice k m) (q i)
  let z := fun i : Fin (d+1) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
  let YN := beta^2*deriv (Scalar.xiSlice k m) 1
  let YC := beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1)
  let theta := fun t => t*(beta^2*deriv (Scalar.xiSlice k m) t)-beta^2*Scalar.xiSlice k m t
  have hq (i : Fin (d+1)) : 0≤q i := hq0.trans (hqm (Fin.zero_le i))
  have hym : Monotone y := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (xiSlice_deriv_mono_nonneg_overlap k hm (hq i) (hqm hij)) (sq_nonneg beta)
  have htheta : MonotoneOn theta (Ici 0) := thermal_theta_monotone k beta hm
  have hzm : Monotone z := fun i j hij => htheta (hq i) (hq j) (hqm hij)
  have hy0 : 0≤y 0 := (mul_pos (sq_pos_of_pos hbeta)
    (xiSlice_deriv_pos_nonneg_overlap k hk hm0 hm1 hq0)).le
  have ht0 : theta 0=0 := by simp [theta,Scalar.xiSlice,pow_mul]
  have hz0 : 0≤z 0 := by
    have H := htheta (le_refl 0) hq0 hq0
    rw [ht0] at H
    exact H
  have hDy (j : Fin d) : 0 ≤ increments y j := sub_nonneg.mpr (hym (by change (j : ℕ)≤(j : ℕ)+1; omega))
  have hDz (j : Fin d) : 0 ≤ increments z j := sub_nonneg.mpr (hzm (by change (j : ℕ)≤(j : ℕ)+1; omega))
  have hTotalY : y 0+∑j : Fin d,increments y j=YN := by
    have H := sum_adjacent_sub y
    have HE : y (Fin.last d)=YN := by dsimp [y,YN]; rw [hqend]
    rw [HE] at H
    change (∑j : Fin d,increments y j)=YN-y 0 at H
    linarith
  have hTotalZ : z 0+∑j : Fin d,increments z j=YC := by
    have H := sum_adjacent_sub z
    have HE : z (Fin.last d)=YC := by dsimp [z,y,YC]; rw [hqend]; ring
    rw [HE] at H
    change (∑j : Fin d,increments z j)=YC-z 0 at H
    linarith
  let RN := ∫g : Model.Vector M,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g) ∂stdGaussian (Model.Vector M)
  let CN := ∫g : Model.Vector M,gaussianLogSteps (quadraticSteps M x (increments y))
    (fun h => min (Real.log (sphericalLaplace M h)) (Real.log LN)) (Real.sqrt (y 0) •g) ∂stdGaussian (Model.Vector M)
  let RC := ∫g : Model.Vector 1,gaussianLogSteps (quadraticSteps 1 x (increments z))
    (fun h => Real.sqrt (M : ℝ)*h 0) (Real.sqrt (z 0) •g) ∂stdGaussian (Model.Vector 1)
  let CC := ∫g : Model.Vector 1,gaussianLogSteps (quadraticSteps 1 x (increments z))
    (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt (z 0) •g) ∂stdGaussian (Model.Vector 1)
  let U := Real.exp (2*(M : ℝ)*YN)/LN
  let V := (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*YC)
  have HNum := sphericalStage_clipping_bound hM x (increments y) hx hx1 hxm hDy hy0 hLN
  have HN : RN-CN≤U := by simpa only [hTotalY] using HNum.2.2.2
  have HComp := finite_compensation_clipping_bound M x (increments z) (fun j => (hx j).le) hx1 hDz
    hz0 hb (zero_lt_one.trans_le hcap) (hb1.trans hcap) hTotalZ.le
  have HC : |RC-CC|≤V := HComp.2.2
  have hRC : RC/(M : ℝ)=(∑j : Fin d,x j*increments z j)/2 := by
    dsimp [RC]
    rw [expected_scalar_compensation M x (increments z) hDz (z 0)]
    field_simp
  have HR := HM d x q (fun j => (hx j).le) hxm hx1 hq0 hqm hqend
  dsimp only at HR
  rw [integral_div] at HR
  change beta*(rawValue k beta m).toReal/2-error≤RN/(M : ℝ)-(∑j : Fin d,x j*increments z j)/2 at HR
  rw [←hRC] at HR
  have HCost : RN-RC-(U+V)≤CN-CC := by
    have H := (abs_le.mp HC).1
    linarith
  have HD := div_le_div_of_nonneg_right HCost hMr.le
  change beta*(rawValue k beta m).toReal/2-error-(U+V)/(M : ℝ)≤CN/(M : ℝ)-CC/(M : ℝ)
  simp only [sub_div] at HD
  linarith only [HR,HD]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyClippedCavityLower
