-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMoments
public import TensorPCA.NonRSLowerProofs.BoundedMarkedTransformAnalytic

/-! Nested Gaussian powers and the separate logarithmic root, defined by Gaussian
conditional integrals of the bounded terminal deficit. Positivity and fixed-
parameter integrability hold on the binomial domain.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedTransforms
open MeasureTheory ProbabilityTheory Filter
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def parentPower : (depth : ℕ)→(Fin depth→ℝ)→ℝ→(Fin depth→E→L[ℝ]E)→(E→ℝ)→ℝ→E→ℝ
  | 0,_,p,_,Z,t,z => (1-t*Z z)^p
  | depth+1,x,p,T,Z,t,z =>
      (∫g : E,parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t (z+T 0 g) ∂stdGaussian E)^(p/x 0)

def rootLog (depth : ℕ) (x : Fin (depth+1)→ℝ) (T : Fin (depth+1)→E→L[ℝ]E)
    (Z : E→ℝ) (t : ℝ) (z : E) : ℝ :=
  Real.log (∫g : E,parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t (z+T 0 g) ∂stdGaussian E)/(x 0)

theorem parentPower_zero (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) : parentPower depth x p T Z 0 z=1 := by
  induction depth generalizing p z with
  | zero => simp only [parentPower,zero_mul,sub_zero,Real.one_rpow]
  | succ depth ih => simp only [parentPower,ih,integral_const,probReal_univ,one_smul,Real.one_rpow]

theorem rootLog_zero (depth : ℕ) (x : Fin (depth+1)→ℝ) (T : Fin (depth+1)→E→L[ℝ]E)
    (Z : E→ℝ) (z : E) : rootLog depth x T Z 0 z=0 := by
  simp only [rootLog,parentPower_zero,integral_const,probReal_univ,one_smul,Real.log_one,zero_div]

theorem parentPower_measurable (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) :
    Measurable (fun tz : ℝ×E => parentPower depth x p T Z tz.1 tz.2) := by
  induction depth generalizing p with
  | zero => exact (measurable_const.sub (measurable_fst.mul (hZ.comp measurable_snd))).pow_const p
  | succ depth ih =>
    have hm : Measurable (fun tzg : (ℝ×E)×E =>
        parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z tzg.1.1 (tzg.1.2+T 0 tzg.2)) :=
      (ih (fun j => x j.succ) (x 0) (fun j => T j.succ)).comp
        ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).add
          ((T 0).continuous.measurable.comp measurable_snd)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable.pow_const (p/x 0)

private theorem base_bounds {Z : E→ℝ} {a t : ℝ} (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (z : E) : 1-|t| *a≤1-t*Z z ∧ 1-t*Z z≤1+|t| *a := by
  have H : |t*Z z|≤|t| *a := by
    rw [abs_mul,abs_of_nonneg (hb z).1]
    exact mul_le_mul_of_nonneg_left (hb z).2 (abs_nonneg _)
  have HE := abs_le.mp H
  exact ⟨by linarith only [HE.2],by linarith only [HE.1]⟩

theorem parentPower_bounds (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (hp : 0≤p) (hx : ∀j,0<x j) {t : ℝ} (ht : |t| *a<1) (z : E) :
    (1-|t| *a)^p≤parentPower depth x p T Z t z ∧ parentPower depth x p T Z t z≤(1+|t| *a)^p := by
  have hl : 0<1-|t| *a := sub_pos.mpr ht
  have hu : 0<1+|t| *a := by positivity
  induction depth generalizing p z with
  | zero =>
    have hbase := base_bounds (t := t) ha hb z
    exact ⟨Real.rpow_le_rpow hl.le hbase.1 hp,
      Real.rpow_le_rpow (hl.le.trans hbase.1) hbase.2 hp⟩
  | succ depth ih =>
    have hiBounds (g : E) := ih (fun j => x j.succ) (x 0) (fun j => T j.succ) (hx 0).le
      (fun j => hx j.succ) (z+T 0 g)
    have hm : Measurable (fun g : E => parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t (z+T 0 g)) :=
      (parentPower_measurable depth (fun j => x j.succ) (x 0) (fun j => T j.succ) hZ).comp
        (measurable_const.prodMk (measurable_const.add (T 0).continuous.measurable))
    have hi : Integrable (fun g : E => parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t (z+T 0 g)) (stdGaussian E) := by
      apply Integrable.of_bound hm.aestronglyMeasurable ((1+|t| *a)^(x 0))
      exact ae_of_all _ (fun g => by
        rw [Real.norm_of_nonneg ((Real.rpow_nonneg hl.le _).trans (hiBounds g).1)]
        exact (hiBounds g).2)
    have hLow := integral_mono (integrable_const ((1-|t| *a)^(x 0))) hi (fun g => (hiBounds g).1)
    have hUp := integral_mono hi (integrable_const ((1+|t| *a)^(x 0))) (fun g => (hiBounds g).2)
    simp only [integral_const,probReal_univ,one_smul] at hLow hUp
    have hI0 : 0≤∫g : E,parentPower depth (fun j => x j.succ) (x 0) (fun j => T j.succ) Z t (z+T 0 g) ∂stdGaussian E :=
      (Real.rpow_nonneg hl.le _).trans hLow
    have hq : 0≤p/x 0 := div_nonneg hp (hx 0).le
    have HL := Real.rpow_le_rpow (Real.rpow_nonneg hl.le (x 0)) hLow hq
    have HU := Real.rpow_le_rpow hI0 hUp hq
    have hEq : x 0*(p/x 0)=p := by field_simp [ne_of_gt (hx 0)]
    rw [← Real.rpow_mul hl.le,hEq] at HL
    rw [← Real.rpow_mul hu.le,hEq] at HU
    exact ⟨HL,HU⟩

theorem parentPower_integrable_shift (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (hp : 0≤p) (hx : ∀j,0<x j) {t : ℝ} (ht : |t| *a<1)
    (S : E→L[ℝ]E) (z : E) :
    Integrable (fun g : E => parentPower depth x p T Z t (z+S g)) (stdGaussian E) := by
  have hm : Measurable (fun g : E => parentPower depth x p T Z t (z+S g)) :=
    (parentPower_measurable depth x p T hZ).comp (measurable_const.prodMk (measurable_const.add S.continuous.measurable))
  apply Integrable.of_bound hm.aestronglyMeasurable ((1+|t| *a)^p)
  exact ae_of_all _ (fun g => by
    rw [Real.norm_of_nonneg ((Real.rpow_nonneg (sub_pos.mpr ht).le _).trans (parentPower_bounds depth x p T hZ ha hb hp hx ht (z+S g)).1)]
    exact (parentPower_bounds depth x p T hZ ha hb hp hx ht (z+S g)).2)

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedTransforms
