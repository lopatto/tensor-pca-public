-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyCavityPositive

/-! The physical finite Gaussian hierarchy cavity functional dominates the CS minimum
uniformly over all finite nonnegative-height hierarchies. Small initial heights are
genuinely compressed into the quenched Gaussian root.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyCavityLower
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCS FiniteCSGaussianDepthMoment
open FiniteGaussianHierarchyPrefixTransport FiniteGaussianHierarchyPrefixGaussian
open FiniteGaussianHierarchyCavityPositive FiniteGaussianQuadraticSphericalStages
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cavity_lower (k : ℕ) (hk : 1≤k) {beta m error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1) (herror : 0<error) :
    ∀ᶠ M : ℕ in atTop,∀(d : ℕ) (x : Fin d→ℝ) (q : Fin (d+1)→ℝ),
      (∀j,0≤x j)→Monotone x→(∀j,x j≤1)→
      0≤q 0→Monotone q→q (Fin.last d)=1→
      let y := fun i : Fin (d+1) => beta^2*deriv (Scalar.xiSlice k m) (q i)
      let z := fun i : Fin (d+1) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
      beta*(rawValue k beta m).toReal/2-error≤
        (∫g : Model.Vector M,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)/(M : ℝ)
          ∂stdGaussian (Model.Vector M))-(∑j : Fin d,x j*increments z j)/2 := by
  let theta := fun t => t*(beta^2*deriv (Scalar.xiSlice k m) t)-beta^2*Scalar.xiSlice k m t
  let T := theta 1-theta 0
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  have hTheta : MonotoneOn theta (Ici 0) := thermal_theta_monotone k beta hm
  have hT : 0≤T := sub_nonneg.mpr (hTheta (by norm_num) (by norm_num) (by norm_num))
  let delta := min 1 (error/(T+1))
  have hT1 : 0<T+1 := by linarith only [hT]
  have hdelta : 0<delta := lt_min (by norm_num) (div_pos herror hT1)
  have hdelta1 : delta≤1 := min_le_left _ _
  have hdeltaT : delta*T≤error := by
    have H := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (error/(T+1))) hT1.le
    rw [div_mul_cancel₀ _ hT1.ne'] at H
    change delta*(T+1)≤error at H
    nlinarith only [H,hdelta]
  have HT := positive_height_cavity_lower k hk hbeta hm0 hm1 hdelta hdelta1 (half_pos herror)
  filter_upwards [HT,eventually_ge_atTop (1 : ℕ)] with M HM hM
  intro d x q hx0 hxm hx1 hq0 hqm hqend
  obtain ⟨r,s,e,hsmall,hlarge⟩ := exists_height_split x hxm delta
  subst d
  let y := fun i : Fin (r+s+1) => beta^2*deriv (Scalar.xiSlice k m) (q i)
  let z := fun i : Fin (r+s+1) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
  let xs := fun j : Fin s => x (j.natAdd r)
  let qs := suffixValues q
  change beta*(rawValue k beta m).toReal/2-error≤
    (∫g : Model.Vector M,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)/(M : ℝ)
      ∂stdGaussian (Model.Vector M))-(∑j : Fin (r+s),x j*increments z j)/2
  have hMpos : 0<M := Nat.lt_of_lt_of_le (by decide) hM
  have hMr : (0 : ℝ)<M := by exact_mod_cast hMpos
  have hq (i : Fin (r+s+1)) : 0≤q i := hq0.trans (hqm (Fin.zero_le i))
  have hym : Monotone y := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (xiSlice_deriv_mono_nonneg_overlap k hm (hq i) (hqm hij)) (sq_nonneg beta)
  have hzm : Monotone z := fun i j hij => hTheta (hq i) (hq j) (hqm hij)
  have hy0 : 0≤y 0 := (mul_pos (sq_pos_of_pos hbeta)
    (xiSlice_deriv_pos_nonneg_overlap k hk hm0 hm1 hq0)).le
  have hxLarge (j : Fin s) : delta<xs j := hlarge j
  have hxsm : Monotone xs := by
    intro i j hij
    apply hxm
    change r+(i : ℕ)≤r+(j : ℕ)
    omega
  have hqs0 : 0≤qs 0 := hq0.trans (hqm (Fin.zero_le _))
  have hqsm : Monotone qs := suffixValues_monotone hqm
  have hqsend : qs (Fin.last s)=1 := by dsimp only [qs]; rw [suffix_last,hqend]
  have HS := HM s xs qs (fun j => (hxLarge j).le) hxsm (fun j => hx1 _) hqs0 hqsm hqsend
  change beta*(rawValue k beta m).toReal/2-error/2≤
    (∫g : Model.Vector M,sphericalStage M xs (increments (suffixValues y)) 0
      (Real.sqrt (suffixValues y 0) •g)/(M : ℝ)∂stdGaussian (Model.Vector M))-
        (∑j : Fin s,xs j*increments (suffixValues z) j)/2 at HS
  have HNumRaw := expected_sphericalStage_prefix_lower hMpos x y hx0 hym hy0 hdelta.le hsmall hlarge
  have HNum : (∫g : Model.Vector M,sphericalStage M xs (increments (suffixValues y)) 0
        (Real.sqrt (suffixValues y 0) •g)/(M : ℝ)∂stdGaussian (Model.Vector M))≤
      ∫g : Model.Vector M,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)/(M : ℝ)
        ∂stdGaussian (Model.Vector M) := by
    rw [integral_div,integral_div]
    exact div_le_div_of_nonneg_right HNumRaw hMr.le
  have HLoss := (weighted_correction_suffix_loss x z hdelta.le hx0 hsmall hzm).2
  have Hz0 : theta 0≤z 0 := hTheta (le_refl (0 : ℝ)) hq0 hq0
  have Hzlast : z (Fin.last (r+s))=theta 1 := by dsimp only [z,y,theta]; rw [hqend]
  have HSpread : z (Fin.last (r+s))-z 0≤T := by
    rw [Hzlast]
    dsimp only [T]
    linarith only [Hz0]
  have HLoss' : (∑j : Fin (r+s),x j*increments z j)-
      (∑j : Fin s,xs j*increments (suffixValues z) j)≤delta*T :=
    HLoss.trans (mul_le_mul_of_nonneg_left HSpread hdelta.le)
  linarith only [HS,HNum,HLoss',hdeltaT]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyCavityLower
