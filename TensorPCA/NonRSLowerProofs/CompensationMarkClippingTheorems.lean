-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingEmpiricalTransforms
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorEmpirical

/-! Thermal compensation marks, including canonical iid empirical means. The cutoffs
depend only on cavity size and thermal parameters, before bulk dimension, prior,
sample count or positive masses are chosen. This is analytic clipping, not a
physical hierarchy moment identification.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingTheorems
open MeasureTheory ProbabilityTheory Set
open FiniteCavityGaussianCompatibility FiniteCavityThetaCovariance
open FiniteCavityCompensatorEmpirical GGFiniteEmpiricalNormalizer
open CompensationMarkClippingGaussianTransforms CompensationMarkClippingEmpiricalTransforms
open scoped RealInnerProductSpace
noncomputable section

theorem exists_clipping_cutoffs (C : ℝ) {eta : ℝ} (heta : 0<eta) :
    ∃b L : ℝ,0<b ∧ b≤1 ∧ 1≤L ∧ 2*Real.exp (9*C/2)/L+2*b*Real.exp (2*C)≤eta := by
  let U := 2*Real.exp (9*C/2)
  let V := 2*Real.exp (2*C)
  have hU : 0<U := mul_pos (by norm_num) (Real.exp_pos _)
  have hV : 0<V := mul_pos (by norm_num) (Real.exp_pos _)
  let L := 1+2*U/eta
  let b := min 1 (eta/(2*V))
  have hL : 1≤L := by
    dsimp [L]
    linarith [div_pos (mul_pos (by norm_num : (0 : ℝ)<2) hU) heta]
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hb : 0<b := lt_min zero_lt_one (div_pos heta (mul_pos (by norm_num) hV))
  refine ⟨b,L,hb,min_le_left _ _,hL,?_⟩
  have hUL : U/L≤eta/2 := by
    rw [div_le_iff₀ hL0]
    dsimp [L]
    field_simp
    nlinarith
  have hVb : b*V≤eta/2 := by
    calc
      _ ≤ (eta/(2*V))*V := mul_le_mul_of_nonneg_right (min_le_right _ _) hV.le
      _ = _ := by field_simp
  change U/L+2*b*Real.exp (2*C)≤eta
  have HE : 2*b*Real.exp (2*C)=b*V := by dsimp [V]; ring
  rw [HE]
  linarith

section Actual
variable {N K : ℕ} (hN : 0<N) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
local notation "F" => limitingCompensatorFeature (N := N) M (fun p : Fin k ↦ (p : ℕ)+1)
  (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "C" => (M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1)

private theorem theta_measurable : Measurable F := by
  apply Continuous.measurable
  unfold limitingCompensatorFeature
  exact (continuous_const : Continuous (fun _ : Model.Vector N => Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
    (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)

include hN hmu

private theorem theta_norm_bound (nu : Measure (Model.Vector N))
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) : ∀ᵐx∂nu,‖F x‖≤Real.sqrt C :=
  hnu.mono (fun _ hx => Real.le_sqrt_of_sq_le (thetaFeature_norm_sq hN M k hmu beta hx).le)

theorem compensation_log_clipping_error_le
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu] (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    let A := fun g : GroundState.Disorder N k => ∫x,(Real.exp (inner ℝ (F x) g))^alpha ∂nu
    let Z := fun g : GroundState.Disorder N k => ∫x,(max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha ∂nu
    Integrable (fun g => |Real.log (A g)-Real.log (Z g)|/alpha) (stdGaussian (GroundState.Disorder N k)) ∧
      (∫g,|Real.log (A g)-Real.log (Z g)|/alpha ∂stdGaussian (GroundState.Disorder N k))≤
        2*Real.exp (9*C/2)/L+2*b*Real.exp (2*C) := by
  have H := conditional_normalized_log_clipping_error_le nu (theta_measurable M k beta)
    (Real.sqrt_nonneg C) (theta_norm_bound hN M k hmu beta nu hnu) hb hb1 hL ha0 ha1
  rwa [Real.sq_sqrt (theta_diagonal_nonneg hN M k hmu beta)] at H

theorem compensation_parent_clipping_error_le
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu] (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N)
    {b L alpha p : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (hp : 0<p) (hpa : p≤alpha) (ha1 : alpha≤1) :
    let A := fun g : GroundState.Disorder N k => ∫x,(Real.exp (inner ℝ (F x) g))^alpha ∂nu
    let Z := fun g : GroundState.Disorder N k => ∫x,(max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha ∂nu
    Integrable (fun g => |(A g)^(p/alpha)-(Z g)^(p/alpha)|/p) (stdGaussian (GroundState.Disorder N k)) ∧
      (∫g,|(A g)^(p/alpha)-(Z g)^(p/alpha)|/p ∂stdGaussian (GroundState.Disorder N k))≤
        2*Real.exp (9*C/2)/L+2*b*Real.exp (2*C) := by
  have H := conditional_normalized_parent_clipping_error_le nu (theta_measurable M k beta)
    (Real.sqrt_nonneg C) (theta_norm_bound hN M k hmu beta nu hnu) hb hb1 hL hp hpa ha1
  rwa [Real.sq_sqrt (theta_diagonal_nonneg hN M k hmu beta)] at H

theorem compensation_empirical_log_clipping_error_le (hK : 0<K)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu] (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    let P := (stdGaussian (GroundState.Disorder N k)).prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun z : GroundState.Disorder N k×(Fin K→Model.Vector N) =>
      empiricalMean K (fun x => (Real.exp (inner ℝ (F x) z.1))^alpha) z.2
    let Z := fun z : GroundState.Disorder N k×(Fin K→Model.Vector N) =>
      empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) z.1)) L))^alpha) z.2
    Integrable (fun z => |Real.log (A z)-Real.log (Z z)|/alpha) P ∧
      (∫z,|Real.log (A z)-Real.log (Z z)|/alpha ∂P)≤2*Real.exp (9*C/2)/L+2*b*Real.exp (2*C) := by
  have H := iid_empirical_log_clipping_error_le hK nu (theta_measurable M k beta)
    (Real.sqrt_nonneg C) (theta_norm_bound hN M k hmu beta nu hnu) hb hb1 hL ha0 ha1
  rwa [Real.sq_sqrt (theta_diagonal_nonneg hN M k hmu beta)] at H

theorem compensation_empirical_parent_clipping_error_le (hK : 0<K)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu] (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N)
    {b L alpha p : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (hp : 0<p) (hpa : p≤alpha) (ha1 : alpha≤1) :
    let P := (stdGaussian (GroundState.Disorder N k)).prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun z : GroundState.Disorder N k×(Fin K→Model.Vector N) =>
      empiricalMean K (fun x => (Real.exp (inner ℝ (F x) z.1))^alpha) z.2
    let Z := fun z : GroundState.Disorder N k×(Fin K→Model.Vector N) =>
      empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) z.1)) L))^alpha) z.2
    Integrable (fun z => |(A z)^(p/alpha)-(Z z)^(p/alpha)|/p) P ∧
      (∫z,|(A z)^(p/alpha)-(Z z)^(p/alpha)|/p ∂P)≤2*Real.exp (9*C/2)/L+2*b*Real.exp (2*C) := by
  have H := iid_empirical_parent_clipping_error_le hK nu (theta_measurable M k beta)
    (Real.sqrt_nonneg C) (theta_norm_bound hN M k hmu beta nu hnu) hb hb1 hL hp hpa ha1
  rwa [Real.sq_sqrt (theta_diagonal_nonneg hN M k hmu beta)] at H

end Actual

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingTheorems
