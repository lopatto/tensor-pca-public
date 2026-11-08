-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianTransforms
public import TensorPCA.NonRSLowerProofs.FiniteIIDLabelEmpiricalMoments

/-! Finite empirical means using one shared Gaussian field. Uniform-label integration
rewrites `empiricalMean` with the same Gaussian parameter in every sample.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingEmpiricalTransforms
open MeasureTheory ProbabilityTheory Filter
open CompensationMarkClippingGaussianTransforms
open FiniteIIDLabelCollision FiniteIIDLabelEmpiricalMoments GGFiniteEmpiricalNormalizer
open scoped RealInnerProductSpace BigOperators
noncomputable section
variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem empirical_conditional_log_clipping_error_le {K : ℕ} (hK : 0<K)
    (F : V→E) (s : Fin K→V) {D : ℝ} (hD : 0≤D) (hs : ∀i,‖F (s i)‖≤D)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    let A := fun g : E => empiricalMean K (fun x => (Real.exp (inner ℝ (F x) g))^alpha) s
    let C := fun g : E => empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha) s
    Integrable (fun g => |Real.log (A g)-Real.log (C g)|/alpha) (stdGaussian E) ∧
      (∫g,|Real.log (A g)-Real.log (C g)|/alpha ∂stdGaussian E)≤
        2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  have H := conditional_normalized_log_clipping_error_le (uniformLabelLaw K hK)
    (F := fun i : Fin K => F (s i)) (measurable_of_finite _) hD (ae_of_all _ hs) hb hb1 hL ha0 ha1
  dsimp only at H ⊢
  simpa only [uniformLabelLaw_integral,empiricalMean] using H

theorem empirical_conditional_parent_clipping_error_le {K : ℕ} (hK : 0<K)
    (F : V→E) (s : Fin K→V) {D : ℝ} (hD : 0≤D) (hs : ∀i,‖F (s i)‖≤D)
    {b L alpha p : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (hp : 0<p) (hpa : p≤alpha) (ha1 : alpha≤1) :
    let A := fun g : E => empiricalMean K (fun x => (Real.exp (inner ℝ (F x) g))^alpha) s
    let C := fun g : E => empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) g)) L))^alpha) s
    Integrable (fun g => |(A g)^(p/alpha)-(C g)^(p/alpha)|/p) (stdGaussian E) ∧
      (∫g,|(A g)^(p/alpha)-(C g)^(p/alpha)|/p ∂stdGaussian E)≤
        2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  have H := conditional_normalized_parent_clipping_error_le (uniformLabelLaw K hK)
    (F := fun i : Fin K => F (s i)) (measurable_of_finite _) hD (ae_of_all _ hs) hb hb1 hL hp hpa ha1
  dsimp only at H ⊢
  simpa only [uniformLabelLaw_integral,empiricalMean] using H

private theorem integrate_samples {K : ℕ} (nu : Measure V) [IsProbabilityMeasure nu]
    {err : E×(Fin K→V)→ℝ} (hm : Measurable err) (h0 : ∀p,0≤err p) {B : ℝ}
    (hs : ∀ᵐs∂Measure.pi (fun _ : Fin K => nu),
      Integrable (fun g : E => err (g,s)) (stdGaussian E) ∧ (∫g : E,err (g,s) ∂stdGaussian E)≤B) :
    Integrable err ((stdGaussian E).prod (Measure.pi (fun _ : Fin K => nu))) ∧
      (∫p,err p ∂(stdGaussian E).prod (Measure.pi (fun _ : Fin K => nu)))≤B := by
  have hi : Integrable err ((stdGaussian E).prod (Measure.pi (fun _ : Fin K => nu))) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨hs.mono (fun _ h => h.1),?_⟩
    have hp : AEStronglyMeasurable (fun s : Fin K→V => ∫g : E,‖err (g,s)‖ ∂stdGaussian E)
        (Measure.pi (fun _ : Fin K => nu)) := hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    apply (integrable_const B).mono' hp
    filter_upwards [hs] with s h
    simp only [Real.norm_of_nonneg (h0 _)]
    rw [Real.norm_of_nonneg (integral_nonneg (fun g => h0 (g,s)))]
    exact h.2
  refine ⟨hi,?_⟩
  rw [integral_prod_symm _ hi]
  have H := integral_mono_ae hi.integral_prod_right (integrable_const B) (hs.mono (fun _ h => h.2))
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem iid_empirical_log_clipping_error_le {K : ℕ} (hK : 0<K)
    (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E} (hF : Measurable F)
    {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    let P := (stdGaussian E).prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun p : E×(Fin K→V) => empiricalMean K (fun x => (Real.exp (inner ℝ (F x) p.1))^alpha) p.2
    let C := fun p : E×(Fin K→V) => empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) p.1)) L))^alpha) p.2
    Integrable (fun p => |Real.log (A p)-Real.log (C p)|/alpha) P ∧
      (∫p,|Real.log (A p)-Real.log (C p)|/alpha ∂P)≤2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  dsimp only
  have hmY (i : Fin K) : Measurable (fun p : E×(Fin K→V) => Real.exp (inner ℝ (F (p.2 i)) p.1)) :=
    (continuous_inner.measurable.comp ((hF.comp ((measurable_pi_apply i).comp measurable_snd)).prodMk measurable_fst)).exp
  have hmA : Measurable (fun p : E×(Fin K→V) => empiricalMean K (fun x => (Real.exp (inner ℝ (F x) p.1))^alpha) p.2) := by
    unfold empiricalMean
    exact (Finset.measurable_sum _ (fun i _ => (hmY i).pow_const alpha)).div_const _
  have hmC : Measurable (fun p : E×(Fin K→V) => empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) p.1)) L))^alpha) p.2) := by
    unfold empiricalMean
    exact (Finset.measurable_sum _ (fun i _ => ((measurable_const.max ((hmY i).min measurable_const)).pow_const alpha))).div_const _
  apply integrate_samples nu
    (by simpa only [Pi.sub_apply,Real.norm_eq_abs] using (hmA.log.sub hmC.log).norm.div_const alpha)
    (fun _ => div_nonneg (abs_nonneg _) ha0.le)
  have hs : ∀ᵐs∂Measure.pi (fun _ : Fin K => nu),∀i,‖F (s i)‖≤D :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : Fin K => nu) i).quasiMeasurePreserving.ae hFD)
  exact hs.mono (fun s hs => empirical_conditional_log_clipping_error_le hK F s hD hs hb hb1 hL ha0 ha1)

theorem iid_empirical_parent_clipping_error_le {K : ℕ} (hK : 0<K)
    (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E} (hF : Measurable F)
    {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D)
    {b L alpha p : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (hp : 0<p) (hpa : p≤alpha) (ha1 : alpha≤1) :
    let P := (stdGaussian E).prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun z : E×(Fin K→V) => empiricalMean K (fun x => (Real.exp (inner ℝ (F x) z.1))^alpha) z.2
    let C := fun z : E×(Fin K→V) => empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) z.1)) L))^alpha) z.2
    Integrable (fun z => |(A z)^(p/alpha)-(C z)^(p/alpha)|/p) P ∧
      (∫z,|(A z)^(p/alpha)-(C z)^(p/alpha)|/p ∂P)≤2*Real.exp (9*D^2/2)/L+2*b*Real.exp (2*D^2) := by
  dsimp only
  have hmY (i : Fin K) : Measurable (fun z : E×(Fin K→V) => Real.exp (inner ℝ (F (z.2 i)) z.1)) :=
    (continuous_inner.measurable.comp ((hF.comp ((measurable_pi_apply i).comp measurable_snd)).prodMk measurable_fst)).exp
  have hmA : Measurable (fun z : E×(Fin K→V) => empiricalMean K (fun x => (Real.exp (inner ℝ (F x) z.1))^alpha) z.2) := by
    unfold empiricalMean
    exact (Finset.measurable_sum _ (fun i _ => (hmY i).pow_const alpha)).div_const _
  have hmC : Measurable (fun z : E×(Fin K→V) => empiricalMean K (fun x => (max b (min (Real.exp (inner ℝ (F x) z.1)) L))^alpha) z.2) := by
    unfold empiricalMean
    exact (Finset.measurable_sum _ (fun i _ => ((measurable_const.max ((hmY i).min measurable_const)).pow_const alpha))).div_const _
  apply integrate_samples nu
    (by simpa only [Pi.sub_apply,Real.norm_eq_abs] using ((hmA.pow_const (p/alpha)).sub (hmC.pow_const (p/alpha))).norm.div_const p)
    (fun _ => div_nonneg (abs_nonneg _) hp.le)
  have hs : ∀ᵐs∂Measure.pi (fun _ : Fin K => nu),∀i,‖F (s i)‖≤D :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : Fin K => nu) i).quasiMeasurePreserving.ae hFD)
  exact hs.mono (fun s hs => empirical_conditional_parent_clipping_error_le hK F s hD hs hb hb1 hL hp hpa ha1)

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingEmpiricalTransforms
