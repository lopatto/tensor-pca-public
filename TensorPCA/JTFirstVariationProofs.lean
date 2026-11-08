-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTAnalyticProofs
public import TensorPCA.ScalarThresholdProofs

/-! Profile variations of the zero-temperature functional.
No existence of a minimizer or dual optimizer is assumed as a theorem. -/
@[expose] public section
namespace TensorPCA.JTFirstVariationProofs
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp_mem (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
  rw [clamp,min_eq_right ht.2,max_eq_right ht.1]

def profileExtend (p : ℝ → ℝ) (t : ℝ) : ℝ := p (clamp t)

theorem continuous_profileExtend {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    Continuous (profileExtend p) := by
  change Continuous (p ∘ clamp)
  exact hp.1.comp_continuous (by unfold clamp; fun_prop) clamp_mem

theorem profile_lower {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p 1 ≤ p t :=
  hp.2.1 ht (by norm_num) ht.2

theorem profileExtend_lower {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) (t : ℝ) :
    p 1 ≤ profileExtend p t := profile_lower hp (clamp_mem t)

theorem profile_one_pos {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) : 0 < p 1 :=
  hp.2.2.2 1 (by norm_num)

theorem admissibleProfile_constShift {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {c : ℝ} (hc : -p 1 < c) : Scalar.AdmissibleProfile (fun t => p t+c) := by
  refine ⟨hp.1.add continuousOn_const,?_,?_,?_⟩
  · intro x hx y hy hxy
    linarith [hp.2.1 hx hy hxy]
  · exact hp.2.2.1.add (concaveOn_const c (convex_Icc (0 : ℝ) 1))
  · intro t ht
    linarith [profile_lower hp ht]

def reciprocalKernel (p : ℝ → ℝ) (c t : ℝ) : ℝ :=
  1/(profileExtend p t*(profileExtend p t+max c (-p 1/2)))

theorem continuous_reciprocalKernel {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    Continuous (reciprocalKernel p).uncurry := by
  have hc : Continuous (fun z : ℝ × ℝ => profileExtend p z.2) :=
    (continuous_profileExtend hp).comp continuous_snd
  have hm : Continuous (fun z : ℝ × ℝ => max z.1 (-p 1/2)) := continuous_fst.max continuous_const
  have hden : Continuous (fun z : ℝ × ℝ =>
      profileExtend p z.2*(profileExtend p z.2+max z.1 (-p 1/2))) := hc.mul (hc.add hm)
  apply continuous_const.div hden
  intro z
  have hp1 := profile_one_pos hp
  have hlow := profileExtend_lower hp z.2
  have hmax := le_max_right z.1 (-p 1/2)
  exact mul_ne_zero (by linarith) (by linarith)

theorem reciprocalKernel_eq {p : ℝ → ℝ}
    {c t : ℝ} (hc : -p 1/2 ≤ c) (ht : t ∈ Icc (0 : ℝ) 1) :
    reciprocalKernel p c t = 1/(p t*(p t+c)) := by
  simp only [reciprocalKernel,profileExtend,clamp_eq ht,max_eq_left hc]

theorem reciprocalKernel_zero {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : reciprocalKernel p 0 t = 1/(p t)^2 := by
  rw [reciprocalKernel_eq (by have := profile_one_pos hp; linarith) ht]
  rw [add_zero,pow_two]

def reciprocalKernelIntegral (p : ℝ → ℝ) (c : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, reciprocalKernel p c t

theorem continuous_reciprocalKernelIntegral {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    Continuous (reciprocalKernelIntegral p) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (continuous_reciprocalKernel hp) (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  convert hc using 1
  funext c
  unfold reciprocalKernelIntegral
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]

theorem reciprocalKernelIntegral_zero {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    reciprocalKernelIntegral p 0 = ∫ t in (0 : ℝ)..1, 1/(p t)^2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact reciprocalKernel_zero hp (by simpa using ht)

/-- Exact finite difference identity for the actual P functional; the boundary
coefficient h²+xi'(0) is retained. This precedes any limiting argument. -/
theorem parisiFunctional_constShift_difference {xi p : ℝ → ℝ}
    (hp : Scalar.AdmissibleProfile p)
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    (h : ℝ) {c : ℝ} (hc : -p 1 < c) :
    Scalar.parisiFunctional xi h (fun t => p t+c)-Scalar.parisiFunctional xi h p =
      c*((h^2+deriv xi 0)+∫ t in (0 : ℝ)..1,
        deriv (deriv xi) t-1/(p t*(p t+c))) := by
  have hq := admissibleProfile_constShift hp hc
  have hInvP : ContinuousOn (fun t => 1/p t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp.1 (fun t ht => (hp.2.2.2 t ht).ne')
  have hInvQ : ContinuousOn (fun t => 1/(p t+c)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hq.1 (fun t ht => (hq.2.2.2 t ht).ne')
  have hP : IntervalIntegrable (fun t => deriv (deriv xi) t*p t+1/p t) volume 0 1 :=
    ((hxi.mul hp.1).add hInvP).intervalIntegrable_of_Icc zero_le_one
  have hQ : IntervalIntegrable (fun t => deriv (deriv xi) t*(p t+c)+1/(p t+c)) volume 0 1 :=
    ((hxi.mul hq.1).add hInvQ).intervalIntegrable_of_Icc zero_le_one
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (deriv (deriv xi) t*(p t+c)+1/(p t+c))-(deriv (deriv xi) t*p t+1/p t) =
        c*(deriv (deriv xi) t-1/(p t*(p t+c))) := by
    have hpn : p t ≠ 0 := (hp.2.2.2 t ht).ne'
    have hqn : p t+c ≠ 0 := (hq.2.2.2 t ht).ne'
    field_simp [hpn,hqn]
    ring
  have hi : (∫ t in (0 : ℝ)..1, deriv (deriv xi) t*(p t+c)+1/(p t+c))-
      (∫ t in (0 : ℝ)..1, deriv (deriv xi) t*p t+1/p t) =
      c*(∫ t in (0 : ℝ)..1, deriv (deriv xi) t-1/(p t*(p t+c))) := by
    rw [← intervalIntegral.integral_sub hQ hP,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact he t (by simpa using ht)
  unfold Scalar.parisiFunctional
  nlinarith [hi]


end
end TensorPCA.JTFirstVariationProofs
