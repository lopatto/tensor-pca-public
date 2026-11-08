-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomComparison
public import TensorPCA.NonRSLowerProofs.FiniteCSVarianceProofs
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianPushforwardAlgebra

/-! Finite-temperature Gaussian three-atom competitors. The Gaussian precision is
minimized and a different CS probability law is constructed; there is no assumed
identification of same-law variational costs.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomBridge
open Set FiniteCSGaussianThreeAtomPrecision FiniteCSGaussianThreeAtomComparison
open FiniteCSGaussianPushforwardAlgebra RetainedCountProofs.CrisantiSommers
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def threeAtomGaussianValue (k : ℕ) (beta m x z q0 q1 q2 B : ℝ) : ℝ :=
  let f := fun t ↦ beta^2*Scalar.xiSlice k m t
  let y := fun t ↦ beta^2*deriv (Scalar.xiSlice k m) t
  threeAtomCost x z (y q0) (y q1-y q0) (y q2-y q1) (y 1-y q2) B-
    (x*((q1*y q1-f q1)-(q0*y q0-f q0))+
      z*((q2*y q2-f q2)-(q1*y q1-f q1))+((y 1-f 1)-(q2*y q2-f q2)))

theorem xiSlice_convex_nonneg (k : ℕ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    ConvexOn ℝ (Ici 0) (Scalar.xiSlice k m) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    (fun t _ ↦ (VariationalProofs.hasDerivAt_xiSlice k m t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt.differentiableWithinAt)
  intro s hs t ht hst
  exact FiniteCS.xiSlice_deriv_mono_nonneg_overlap k hm (interior_subset hs) hst

theorem thermal_xiSlice_convex_nonneg (k : ℕ) (beta : ℝ) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    ConvexOn ℝ (Ici 0) (fun t ↦ beta^2*Scalar.xiSlice k m t) := by
  simpa only [smul_eq_mul] using (xiSlice_convex_nonneg k hm).smul (sq_nonneg beta)

theorem thermal_xiSlice_hasDerivAt (k : ℕ) (beta m t : ℝ) :
    HasDerivAt (fun u ↦ beta^2*Scalar.xiSlice k m u)
      (beta^2*deriv (Scalar.xiSlice k m) t) t := by
  convert (VariationalProofs.hasDerivAt_xiSlice k m t).const_mul (beta^2) using 1
  rw [VariationalProofs.deriv_xiSlice]

/-- Every valid Gaussian three-atom competitor dominates the CS minimum. The original
last node may equal one; the constructed CS cutoff is strictly below one by scalar
precision stationarity.
-/
theorem rawValue_le_threeAtomGaussianValue (k : ℕ) (hk : 1 ≤ k)
    {beta m x z q0 q1 q2 B : ℝ} (hbeta : 0 < beta)
    (hm0 : 0 < |m|) (hm1 : |m| < 1) (hx : 0 < x) (hxz : x ≤ z) (hz : z ≤ 1)
    (hq0 : 0 ≤ q0) (hq01 : q0 ≤ q1) (hq12 : q1 ≤ q2) (hq2 : q2 ≤ 1)
    (hB : x*(beta^2*deriv (Scalar.xiSlice k m) q1-beta^2*deriv (Scalar.xiSlice k m) q0)+
      z*(beta^2*deriv (Scalar.xiSlice k m) q2-beta^2*deriv (Scalar.xiSlice k m) q1)+
      (beta^2*deriv (Scalar.xiSlice k m) 1-beta^2*deriv (Scalar.xiSlice k m) q2) < B) :
    beta*(FiniteCS.rawValue k beta m).toReal ≤ threeAtomGaussianValue k beta m x z q0 q1 q2 B := by
  let f := fun t ↦ beta^2*Scalar.xiSlice k m t
  let y := fun t ↦ beta^2*deriv (Scalar.xiSlice k m) t
  have hm : m ∈ Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  have hy : 0 < y q0 := mul_pos (sq_pos_of_pos hbeta)
    (FiniteCS.xiSlice_deriv_pos_nonneg_overlap k hk hm0 hm1 hq0)
  have h01 : y q0 ≤ y q1 := mul_le_mul_of_nonneg_left
    (FiniteCS.xiSlice_deriv_mono_nonneg_overlap k hm hq0 hq01) (sq_nonneg beta)
  have h12 : y q1 ≤ y q2 := mul_le_mul_of_nonneg_left
    (FiniteCS.xiSlice_deriv_mono_nonneg_overlap k hm (hq0.trans hq01) hq12) (sq_nonneg beta)
  have h23 : y q2 ≤ y 1 := mul_le_mul_of_nonneg_left
    (FiniteCS.xiSlice_deriv_mono_nonneg_overlap k hm (hq0.trans (hq01.trans hq12)) hq2) (sq_nonneg beta)
  obtain ⟨P,hP,hroot,hmin⟩ := exists_threeAtom_minimizing_root hx (hx.trans_le hxz) hy
    (sub_nonneg.mpr h01) (sub_nonneg.mpr h12) (sub_nonneg.mpr h23)
  let D0 := P-(x*(y q1-y q0)+z*(y q2-y q1)+(y 1-y q2))
  let D1 := P-(z*(y q2-y q1)+(y 1-y q2))
  let D2 := P-(y 1-y q2)
  let r0 := y q0/D0^2
  let r1 := r0+(y q1-y q0)/(D0*D1)
  let r2 := r1+(y q2-y q1)/(D1*D2)
  have hdata := precision_pushforward_relations hx hxz hz hy
    (sub_nonneg.mpr h01) (sub_nonneg.mpr h12) (sub_nonneg.mpr h23) hP hroot
  change 0 < D0 ∧ 0 < D1 ∧ 0 < D2 ∧ 0 < P ∧ 0 < r0 ∧ r0 ≤ r1 ∧ r1 ≤ r2 ∧ r2 < 1 ∧
    1-r2=1/D2 ∧ 1/D1=1/D2+z*(r2-r1) ∧ 1/D0=1/D1+x*(r1-r0) at hdata
  rcases hdata with ⟨hD0,hD1,hD2,hPpos,hr0,hr01,hr12,hr2,hhat2,hhat1,hhat0⟩
  have hmoment := precision_weighted_moment hx hxz hz hy h01 h12 h23 hP hroot
  change x*r0*y q0+(z-x)*r1*y q1+(1-z)*r2*y q2 = y 1-P+1 at hmoment
  have heval := functional_threeAtom_eval hx hxz hz hr0.le hr01 hr12 hr2
    hD0 hD1 hD2 hhat2 hhat1 hhat0 beta (Scalar.xiSlice k m)
  have hcompare := gaussian_cs_comparison f (thermal_xiSlice_convex_nonneg k beta hm)
    hx hxz hz h01 h12 h23 hq0 (hq0.trans hq01) (hq0.trans (hq01.trans hq12))
    hr0.le (hr0.le.trans hr01) (hr0.le.trans (hr01.trans hr12))
    (thermal_xiSlice_hasDerivAt k beta m q0) (thermal_xiSlice_hasDerivAt k beta m q1)
    (thermal_xiSlice_hasDerivAt k beta m q2) hP rfl hmoment
  change beta*(FiniteCS.rawValue k beta m).toReal ≤
    threeAtomCost x z (y q0) (y q1-y q0) (y q2-y q1) (y 1-y q2) B-
      (x*((q1*y q1-f q1)-(q0*y q0-f q0))+
        z*((q2*y q2-f q2)-(q1*y q1-f q1))+((y 1-f 1)-(q2*y q2-f q2)))
  calc
    beta*(FiniteCS.rawValue k beta m).toReal ≤
        2*functional beta (Scalar.xiSlice k m) (threeAtomLaw x z r0 r1 r2) r2 :=
      rawValue_le_threeAtomFunctional k hk hbeta hm hx.le hxz hz hr0.le hr01 hr12 hr2
    _ = f 1-(x*f r0+(z-x)*f r1+(1-z)*f r2)+r0*D0+
        Real.log (D1/D0)/x+Real.log (D2/D1)/z-Real.log D2 := by
      rw [heval]
      dsimp only [f]
      ring
    _ ≤ threeAtomCost x z (y q0) (y q1-y q0) (y q2-y q1) (y 1-y q2) P-
        (x*((q1*y q1-f q1)-(q0*y q0-f q0))+
          z*((q2*y q2-f q2)-(q1*y q1-f q1))+((y 1-f 1)-(q2*y q2-f q2))) := hcompare
    _ ≤ _ := sub_le_sub_right (hmin B hB) _

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomBridge
