-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedScalarDerivatives
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Differentiation of the literal power transform of a bounded mark.
All dominating functions below are proved constants on a fixed open
neighborhood where the power's base lies between1/2 and3/2. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransform
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
variable {V : Type*} [MeasurableSpace V]

def markTransform (nu : Measure V) (Z : V→ℝ) (alpha t : ℝ) : ℝ :=
  ∫v,(1-t*Z v)^alpha ∂nu

private def markDomain (A : ℝ) : Set ℝ := {t | |t| *(A+1)<1/2}

private theorem markDomain_open (A : ℝ) : IsOpen (markDomain A) := by
  exact isOpen_lt (continuous_abs.mul continuous_const) continuous_const

private theorem zero_mem_markDomain (A : ℝ) : 0∈markDomain A := by
  norm_num [markDomain]

private theorem base_mem {A t z : ℝ} (hA : 0≤A) (hz : |z|≤A)
    (ht : t∈markDomain A) : 1-t*z∈Icc (1/2 : ℝ) (3/2) := by
  have H : |t*z|≤|t| *A := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hz (abs_nonneg t)
  have H' : |t| *A<1/2 := by
    change |t| *(A+1)<1/2 at ht
    nlinarith only [ht,abs_nonneg t]
  have hprod := (abs_lt.mp (H.trans_lt H'))
  constructor <;> linarith only [hprod.1,hprod.2]

private theorem uniform_integrand_bound {A : ℝ} (hA : 0≤A) (a : ℝ) (n : ℕ) :
    ∃B,∀z,|z|≤A→∀t∈markDomain A,‖(-z)^n*(1-t*z)^a‖≤B := by
  have hc : ContinuousOn (fun b : ℝ => b^a) (Icc (1/2 : ℝ) (3/2)) :=
    continuousOn_id.rpow_const (fun b hb => Or.inl (by change b≠0; linarith only [hb.1]))
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hC0 : 0≤C := (norm_nonneg ((1 : ℝ)^a)).trans (hC 1 (by constructor <;> norm_num))
  refine ⟨A^n*C,?_⟩
  intro z hz t ht
  rw [norm_mul,norm_pow,Real.norm_eq_abs,abs_neg]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg z) hz n)
    (hC _ (base_mem hA hz ht)) (norm_nonneg _) (pow_nonneg hA n)

private theorem integrand_measurable {Z : V→ℝ} (hZ : Measurable Z) (a t : ℝ) (n : ℕ) :
    Measurable (fun v => (-Z v)^n*(1-t*Z v)^a) := by
  exact (hZ.neg.pow_const n).mul ((measurable_const.sub (hZ.const_mul t)).pow_const a)

private theorem weighted_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (a : ℝ) (n : ℕ) {t : ℝ} (ht : t∈markDomain A) :
    Integrable (fun v => (-Z v)^n*(1-t*Z v)^a) nu := by
  obtain ⟨B,hB⟩ := uniform_integrand_bound hA a n
  exact Integrable.of_bound (integrand_measurable hZ a t n).aestronglyMeasurable B
    (hb.mono (fun v hv => hB _ hv t ht))

theorem weighted_power_hasDerivAt (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (a : ℝ) (n : ℕ) {t : ℝ}
    (ht : |t| *(A+1)<1/2) :
    HasDerivAt (fun s : ℝ => ∫v,(-Z v)^n*(1-s*Z v)^a ∂nu)
      (a*(∫v,(-Z v)^(n+1)*(1-t*Z v)^(a-1) ∂nu)) t := by
  obtain ⟨B,hB⟩ := uniform_integrand_bound hA (a-1) (n+1)
  have hmeas (s : ℝ) : Measurable (fun v => a*((-Z v)^(n+1)*(1-s*Z v)^(a-1))) :=
    (integrand_measurable hZ (a-1) s (n+1)).const_mul a
  have HD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s v => (-Z v)^n*(1-s*Z v)^a)
    (F' := fun s v => a*((-Z v)^(n+1)*(1-s*Z v)^(a-1)))
    (bound := fun _ : V => |a| *B)
    ((markDomain_open A).mem_nhds ht)
    (Eventually.of_forall (fun s => (integrand_measurable hZ a s n).aestronglyMeasurable))
    (weighted_integrable nu hZ hA hb a n ht) (hmeas t).aestronglyMeasurable
    (hb.mono (fun v hv s hs => by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB _ hv s hs) (abs_nonneg a)))
    (integrable_const (|a| *B))
    (hb.mono (fun v hv s hs => by
      have hpos : 0<1-s*Z v := by have H := (base_mem hA hv hs).1; linarith only [H]
      have D := (((hasDerivAt_id s).mul_const (Z v)).const_sub 1).rpow_const (p := a)
        (Or.inl hpos.ne')
      convert D.const_mul ((-Z v)^n) using 1 <;> simp only [id_eq,one_mul,pow_succ] <;> ring))).2
  simpa only [integral_const_mul] using HD

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransform
