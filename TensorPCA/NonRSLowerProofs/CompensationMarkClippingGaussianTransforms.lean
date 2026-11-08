-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianMixed
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingTransform

/-! Compensation transforms conditional on one shared Gaussian field. Clipping errors
are averaged after the nonlinear prior transform. Bounds depend on the feature norm,
uniformly in ambient dimension and positive masses.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianTransforms
open MeasureTheory ProbabilityTheory Filter
open CompensationMarkClippingGaussianMixed CompensationMarkClippingTransform
open FiniteCavityCompensatorGaussianMoments
open scoped RealInnerProductSpace
noncomputable section
variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem section_inputs (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hFD : ∀ᵐx∂nu,‖F x‖≤D) (g : E) :
    Integrable (fun x => (Real.exp (inner ℝ (F x) g))^2) nu ∧
    Integrable (fun x => (Real.exp (inner ℝ (F x) g))⁻¹) nu ∧
    Integrable (fun x => Real.log (Real.exp (inner ℝ (F x) g))) nu := by
  refine ⟨(expMark_memLp nu hF hFD g).integrable_sq,?_,?_⟩
  · have hnFD : ∀ᵐx∂nu,‖(-F) x‖≤D := hFD.mono (fun _ hx => by simpa only [Pi.neg_apply,norm_neg] using hx)
    have H := (expMark_memLp nu hF.neg hnFD g).integrable one_le_two
    convert H using 1
    funext x
    simp only [Pi.neg_apply,inner_neg_left,Real.exp_neg]
  · simp only [Real.log_exp]
    have hm : Measurable (fun x : V => inner ℝ (F x) g) :=
      continuous_inner.measurable.comp (hF.prodMk measurable_const)
    apply Integrable.of_bound hm.aestronglyMeasurable (D*‖g‖)
    filter_upwards [hFD] with x hx
    simpa only [Real.norm_eq_abs] using (abs_real_inner_le_norm (F x) g).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg g))

private theorem integrate_error_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D)
    {b L : ℝ} (hb : 0≤b) (hL : 0<L) {err : E→ℝ} (hm : Measurable err)
    (h0 : ∀g,0≤err g)
    (he : ∀g,err g≤Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*
      ((∫x,Real.exp (2*inner ℝ (F x) g) ∂nu)/L+b*(∫x,Real.exp ((-1)*inner ℝ (F x) g) ∂nu))) :
    Integrable err (stdGaussian E) ∧ (∫g,err g ∂stdGaussian E)≤
      2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  have h2 := jensen_factor_mixed_bound nu hF hD hFD 2
  have hn := jensen_factor_mixed_bound nu hF hD hFD (-1)
  dsimp only at h2 hn
  let R := fun g : E =>
    (Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫x,Real.exp (2*inner ℝ (F x) g) ∂nu))/L+
      b*(Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫x,Real.exp ((-1)*inner ℝ (F x) g) ∂nu))
  have hR : Integrable R (stdGaussian E) := (h2.1.div_const L).add (hn.1.const_mul b)
  have hER (g : E) : err g≤R g := (he g).trans_eq (by dsimp [R]; ring)
  have hi : Integrable err (stdGaussian E) := hR.mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun g => by rw [Real.norm_of_nonneg (h0 g)]; exact hER g))
  refine ⟨hi,?_⟩
  have H := integral_mono hi hR hER
  change (∫g,err g ∂stdGaussian E)≤∫g,
    (Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫x,Real.exp (2*inner ℝ (F x) g) ∂nu))/L+
      b*(Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫x,Real.exp ((-1)*inner ℝ (F x) g) ∂nu)) ∂stdGaussian E at H
  rw [integral_add (h2.1.div_const L) (hn.1.const_mul b),integral_div,integral_const_mul] at H
  have hEq2 : ((1+|(2 : ℝ)|)*D)^2/2=9*D^2/2 := by norm_num; ring
  have hEqn : ((1+|(-1 : ℝ)|)*D)^2/2=2*D^2 := by norm_num; ring
  have HE' := add_le_add (div_le_div_of_nonneg_right h2.2 hL.le) (mul_le_mul_of_nonneg_left hn.2 hb)
  rw [hEq2,hEqn] at HE'
  exact H.trans (by convert HE' using 1 <;> ring)

theorem conditional_normalized_log_clipping_error_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    let A := fun g : E => ∫x,(Real.exp (inner ℝ (F x) g))^alpha ∂nu
    let C := fun g : E => ∫x,(max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha ∂nu
    Integrable (fun g => |Real.log (A g)-Real.log (C g)|/alpha) (stdGaussian E) ∧
      (∫g,|Real.log (A g)-Real.log (C g)|/alpha ∂stdGaussian E)≤
        2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  dsimp only
  have hmY := expMark_joint_measurable hF
  have hmA : Measurable (fun g : E => ∫x,(Real.exp (inner ℝ (F x) g))^alpha ∂nu) :=
    (hmY.pow_const alpha).stronglyMeasurable.integral_prod_right'.measurable
  have hmC : Measurable (fun g : E => ∫x,(max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha ∂nu) :=
    ((measurable_const.max (hmY.min measurable_const)).pow_const alpha).stronglyMeasurable.integral_prod_right'.measurable
  apply integrate_error_bound nu hF hD hFD hb.le (zero_lt_one.trans_le hL)
    (by simpa only [Pi.sub_apply,Real.norm_eq_abs] using ((hmA.log.sub hmC.log).norm.div_const alpha))
    (fun _ => div_nonneg (abs_nonneg _) ha0.le)
  intro g
  have hi := section_inputs nu hF hFD g
  have hm : Measurable (fun x : V => Real.exp (inner ℝ (F x) g)) :=
    (continuous_inner.measurable.comp (hF.prodMk measurable_const)).exp
  have H := normalized_log_clipping_error_le nu hm (ae_of_all _ (fun _ => Real.exp_pos _))
    hi.1 hi.2.1 hi.2.2 hb hb1 hL ha0 ha1
  simpa only [Real.log_exp,←Real.exp_nat_mul,←Real.exp_neg,neg_one_mul,Nat.cast_ofNat] using H

theorem conditional_normalized_parent_clipping_error_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D)
    {b L alpha p : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (hp : 0<p) (hpa : p≤alpha) (ha1 : alpha≤1) :
    let A := fun g : E => ∫x,(Real.exp (inner ℝ (F x) g))^alpha ∂nu
    let C := fun g : E => ∫x,(max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha ∂nu
    Integrable (fun g => |(A g)^(p/alpha)-(C g)^(p/alpha)|/p) (stdGaussian E) ∧
      (∫g,|(A g)^(p/alpha)-(C g)^(p/alpha)|/p ∂stdGaussian E)≤
        2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  dsimp only
  have hmY := expMark_joint_measurable hF
  have hmA : Measurable (fun g : E => ∫x,(Real.exp (inner ℝ (F x) g))^alpha ∂nu) :=
    (hmY.pow_const alpha).stronglyMeasurable.integral_prod_right'.measurable
  have hmC : Measurable (fun g : E => ∫x,(max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha ∂nu) :=
    ((measurable_const.max (hmY.min measurable_const)).pow_const alpha).stronglyMeasurable.integral_prod_right'.measurable
  apply integrate_error_bound nu hF hD hFD hb.le (zero_lt_one.trans_le hL)
    (by simpa only [Pi.sub_apply,Real.norm_eq_abs] using (((hmA.pow_const (p/alpha)).sub (hmC.pow_const (p/alpha))).norm.div_const p))
    (fun _ => div_nonneg (abs_nonneg _) hp.le)
  intro g
  have hi := section_inputs nu hF hFD g
  have hm : Measurable (fun x : V => Real.exp (inner ℝ (F x) g)) :=
    (continuous_inner.measurable.comp (hF.prodMk measurable_const)).exp
  have H := normalized_parent_clipping_error_le nu hm (ae_of_all _ (fun _ => Real.exp_pos _))
    hi.1 hi.2.1 hi.2.2 hb hb1 hL hp hpa ha1
  simpa only [Real.log_exp,←Real.exp_nat_mul,←Real.exp_neg,neg_one_mul,Nat.cast_ofNat] using H

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianTransforms
