-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthComparison
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomBridge

/-! Every finite positive-height Gaussian competitor dominates the finite-temperature CS
minimum. The original overlap chain reaches one; all transformed atoms, including
the terminal atom, remain in the proof.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthBridge
open MeasureTheory ProbabilityTheory Set
open FiniteCS RetainedCountProofs.CrisantiSommers
open FiniteCSGaussianDepthPrecision FiniteCSGaussianDepthMoment FiniteCSGaussianDepthAtomicLaw
open FiniteCSGaussianDepthPrecisionTrial FiniteCSGaussianDepthComparison
open FiniteCSGaussianThreeAtomBridge
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def depthGaussianValue {d : ℕ} (k : ℕ) (beta m : ℝ) (x : Fin d→ℝ) (q : Fin (d+1)→ℝ) (B : ℝ) : ℝ :=
  gaussianCost x q (fun t => beta^2*Scalar.xiSlice k m t)
    (fun i => beta^2*deriv (Scalar.xiSlice k m) (q i)) B

theorem rawValue_le_atomicLawFunctional {d : ℕ} (k : ℕ) (hk : 1≤ k) {beta m : ℝ}
    (hbeta : 0< beta) (hm : m∈Icc (-1 : ℝ) 1) (x : Fin d→ℝ) (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤ x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hr0 : 0≤ r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1) :
    beta*(rawValue k beta m).toReal≤2*functional beta (Scalar.xiSlice k m) (atomicLaw x r) (r (Fin.last d)) := by
  let nu := atomicTrial x r hx hx1 hxm hr0 hrm hr1
  have hcut : r (Fin.last d)∈Ico (0 : ℝ) 1 := ⟨hr0.trans (hrm (Fin.zero_le _)),hr1⟩
  have hae : ∀ᵐ (s : Overlap)∂(nu : Measure Overlap),(s : ℝ)≤ r (Fin.last d) := by
    letI := atomicLaw_probability r hx hx1 hxm
    exact cutoffTrial_ae_le _ _
  have hfinite := rawFunctional_cutoff_ne_top k hk hbeta hm nu hcut hae
  have H : rawValue k beta m≤ rawFunctional k beta m nu := sInf_le ⟨nu,rfl⟩
  have HR := ENNReal.toReal_mono hfinite H
  rw [rawFunctional_cutoff_toReal k hk hbeta hm nu hcut hae,
    realLaw_atomicTrial x r hx hx1 hxm hr0 hrm hr1] at HR
  have HH := mul_le_mul_of_nonneg_left HR hbeta.le
  have heq : beta*(2*functional beta (Scalar.xiSlice k m) (atomicLaw x r) (r (Fin.last d))/beta)=
      2*functional beta (Scalar.xiSlice k m) (atomicLaw x r) (r (Fin.last d)) := by field_simp [hbeta.ne']
  rwa [heq] at HH

/-- Gaussian-to-CS minimum comparison at every finite depth. Heights remain strictly
positive here; zero-level cofinality is treated separately.
-/
theorem rawValue_le_depthGaussianValue {d : ℕ} (k : ℕ) (hk : 1≤ k)
    {beta m B : ℝ} (hbeta : 0< beta) (hm0 : 0< |m|) (hm1 : |m|<1)
    (x : Fin d→ℝ) (q : Fin (d+1)→ℝ)
    (hx : ∀j,0< x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hq0 : 0≤ q 0) (hqm : Monotone q) (hqend : q (Fin.last d)=1)
    (hB : tail (fun j : Fin d => x j*(beta^2*deriv (Scalar.xiSlice k m) (q j.succ)-
      beta^2*deriv (Scalar.xiSlice k m) (q j.castSucc))) 0< B) :
    beta*(rawValue k beta m).toReal≤ depthGaussianValue k beta m x q B := by
  let f := fun t => beta^2*Scalar.xiSlice k m t
  let y : Fin (d+1)→ℝ := fun i => beta^2*deriv (Scalar.xiSlice k m) (q i)
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  have hq (i : Fin (d+1)) : 0≤ q i := hq0.trans (hqm (Fin.zero_le i))
  have hy : 0< y 0 := mul_pos (sq_pos_of_pos hbeta)
    (xiSlice_deriv_pos_nonneg_overlap k hk hm0 hm1 hq0)
  have hDelta (j : Fin d) : 0≤ increments y j := by
    unfold increments y
    apply sub_nonneg.mpr
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg beta)
    exact xiSlice_deriv_mono_nonneg_overlap k hm (hq j.castSucc) (hqm (by change (j : ℕ)≤(j : ℕ)+1; omega))
  obtain ⟨P,hP,hroot,hmin⟩ := exists_depth_minimizing_root x (increments y) hx hDelta hy
  let r : Fin (d+1)→ℝ := fun i => node x (increments y) (y 0) P i
  have hr0 : 0≤ r 0 := (nodes_pos_le_end_lt_one hx hDelta hy hP hroot (i := 0) (Nat.zero_le _)).1.le
  have hrm : Monotone r := fun i j hij => node_mono (y 0) hx hDelta hP hij
  have hr1 : r (Fin.last d)<1 := (nodes_pos_le_end_lt_one hx hDelta hy hP hroot (i := d) le_rfl).2.2
  have heval := functional_precision_atomicLaw_eval hx hx1 hxm hDelta hy hP hroot beta (Scalar.xiSlice k m)
  have hcompare := FiniteCSGaussianDepthComparison.gaussian_cs_comparison f
    (thermal_xiSlice_convex_nonneg k beta hm) x q y hx hx1 hxm hDelta hy hq hqend
    (fun i => thermal_xiSlice_hasDerivAt k beta m (q i)) hP hroot
  change beta*(rawValue k beta m).toReal≤ gaussianCost x q f y B
  calc
    beta*(rawValue k beta m).toReal≤2*functional beta (Scalar.xiSlice k m) (atomicLaw x r) (r (Fin.last d)) :=
      rawValue_le_atomicLawFunctional k hk hbeta hm x r (fun j => (hx j).le) hx1 hxm hr0 hrm hr1
    _=f 1-(∑i : Fin (d+1),atomWeight x i*f (r i))+y 0/precision x (increments y) P 0+
        (∑j : Fin d,Real.log (precision x (increments y) P ((j : ℕ)+1)/precision x (increments y) P j)/x j)-Real.log P := by
      dsimp only [r,Fin.val_last]
      rw [heval]
      dsimp only [f]
      rw [mul_sub,Finset.mul_sum]
      congr 1
      congr 1
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _≤ gaussianCost x q f y P := hcompare
    _≤ gaussianCost x q f y B := sub_le_sub_right (hmin B hB) _

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthBridge
