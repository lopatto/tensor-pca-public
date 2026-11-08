-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionLaw
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Prod

/-! Literal Gaussian marking of the authoritative finite nested partition.
Every child block gets its own independent Gaussian integral; replicas in
one terminal block share its mark. Weighted moments use exactly the proved
nested EPPF. No physical GG law or scalar child-law representation is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMoments
open MeasureTheory ProbabilityTheory
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def treeMoment : (depth n : ℕ)→(Fin depth→E→L[ℝ]E)→(E→ℝ)→E→NestedPartition depth n→ℝ
  | 0,n,_,Z,z,_ => (Z z)^n
  | depth+1,_,T,Z,z,t => ∏i : Fin t.1.length,
      ∫g : E,treeMoment depth (t.1.partSize i) (fun j => T j.succ) Z (z+T 0 g) (t.2 i) ∂stdGaussian E

def weightedMoment (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) : ℝ :=
  ∑t : NestedPartition depth n,mass depth n x p t*treeMoment depth n T Z z t

theorem treeMoment_measurable (depth n : ℕ) (T : Fin depth→E→L[ℝ]E)
    {Z : E→ℝ} (hZ : Measurable Z) (t : NestedPartition depth n) :
    Measurable (fun z : E => treeMoment depth n T Z z t) := by
  classical
  induction depth generalizing n with
  | zero => exact hZ.pow_const n
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    change Measurable (fun z : E => ∏i : Fin c.length,
      ∫g : E,treeMoment depth (c.partSize i) (fun j => T j.succ) Z (z+T 0 g) (f i) ∂stdGaussian E)
    apply Finset.measurable_prod
    intro i _
    have hm : Measurable (fun zg : E×E =>
        treeMoment depth (c.partSize i) (fun j => T j.succ) Z (zg.1+T 0 zg.2) (f i)) :=
      (ih (c.partSize i) (fun j => T j.succ) (f i)).comp
        (measurable_fst.add ((T 0).continuous.measurable.comp measurable_snd))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem treeMoment_mem (depth n : ℕ) (T : Fin depth→E→L[ℝ]E)
    {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) (t : NestedPartition depth n) :
    0≤treeMoment depth n T Z z t ∧ treeMoment depth n T Z z t≤a^n := by
  classical
  induction depth generalizing n z with
  | zero => exact ⟨pow_nonneg (hb z).1 n,pow_le_pow_left₀ (hb z).1 (hb z).2 n⟩
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    have hI (i : Fin c.length) :
        0≤(∫g : E,treeMoment depth (c.partSize i) (fun j => T j.succ) Z (z+T 0 g) (f i) ∂stdGaussian E) ∧
        (∫g : E,treeMoment depth (c.partSize i) (fun j => T j.succ) Z (z+T 0 g) (f i) ∂stdGaussian E)≤a^(c.partSize i) := by
      have hm : Measurable (fun g : E => treeMoment depth (c.partSize i) (fun j => T j.succ) Z (z+T 0 g) (f i)) :=
        (treeMoment_measurable depth (c.partSize i) (fun j => T j.succ) hZ (f i)).comp
        (measurable_const.add (T 0).continuous.measurable)
      have hi : Integrable (fun g : E => treeMoment depth (c.partSize i) (fun j => T j.succ) Z (z+T 0 g) (f i)) (stdGaussian E) := by
        apply Integrable.of_bound hm.aestronglyMeasurable (a^(c.partSize i))
        exact ae_of_all _ (fun g => by rw [Real.norm_of_nonneg (ih (c.partSize i) (fun j => T j.succ) (z+T 0 g) (f i)).1]; exact (ih _ _ _ _).2)
      refine ⟨integral_nonneg (fun g => (ih (c.partSize i) (fun j => T j.succ) (z+T 0 g) (f i)).1),?_⟩
      have H := integral_mono hi (integrable_const (a^(c.partSize i)))
        (fun g => (ih (c.partSize i) (fun j => T j.succ) (z+T 0 g) (f i)).2)
      simpa only [integral_const,probReal_univ,one_smul] using H
    change 0≤(∏i : Fin c.length,_) ∧ (∏i : Fin c.length,_)≤a^n
    refine ⟨Finset.prod_nonneg (fun i _ => (hI i).1),?_⟩
    calc
      _ ≤ ∏i : Fin c.length,a^(c.partSize i) :=
        Finset.prod_le_prod₀ (fun i _ => (hI i).1) (fun i _ => (hI i).2)
      _ = a^n := by rw [Finset.prod_pow_eq_pow_sum,sum_partSize]

theorem treeMoment_integrable_shift (depth n : ℕ) (T : Fin depth→E→L[ℝ]E)
    {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (S : E→L[ℝ]E) (z : E) (t : NestedPartition depth n) :
    Integrable (fun g : E => treeMoment depth n T Z (z+S g) t) (stdGaussian E) := by
  apply Integrable.of_bound ((treeMoment_measurable depth n T hZ t).comp
    (measurable_const.add S.continuous.measurable)).aestronglyMeasurable (a^n)
  exact ae_of_all _ (fun g => by
    change ‖treeMoment depth n T Z (z+S g) t‖≤a^n
    rw [Real.norm_of_nonneg (treeMoment_mem depth n T hZ ha hb (z+S g) t).1]
    exact (treeMoment_mem depth n T hZ ha hb (z+S g) t).2)

theorem weightedMoment_measurable (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) :
    Measurable (fun z : E => weightedMoment depth n x p T Z z) := by
  classical
  unfold weightedMoment
  exact Finset.measurable_sum _ (fun t _ => (treeMoment_measurable depth n T hZ t).const_mul _)

theorem treeMoment_zero (depth : ℕ) (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ)
    (z : E) (t : NestedPartition depth 0) : treeMoment depth 0 T Z z t=1 := by
  cases depth with
  | zero => simp only [treeMoment,pow_zero]
  | succ depth =>
    obtain ⟨c,f⟩ := t
    change (∏i : Fin c.length,_) = 1
    apply Finset.prod_eq_one
    intro i _
    have H := c.length_le
    have HI := i.isLt
    omega

theorem weightedMoment_zero (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) : weightedMoment depth 0 x p T Z z=1 := by
  unfold weightedMoment
  simp_rw [treeMoment_zero,mul_one]
  exact mass_sum depth 0 x p hp hpx hxm hx1

theorem weightedMoment_mem (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    0≤weightedMoment depth n x p T Z z ∧ weightedMoment depth n x p T Z z≤a^n := by
  unfold weightedMoment
  have hm (t : NestedPartition depth n) := mass_nonneg depth n x p hp hpx hxm hx1 t
  have ht (t : NestedPartition depth n) := treeMoment_mem depth n T hZ ha hb z t
  refine ⟨Finset.sum_nonneg (fun t _ => mul_nonneg (hm t) (ht t).1),?_⟩
  calc
    _ ≤ ∑t : NestedPartition depth n,mass depth n x p t*a^n :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (ht t).2 (hm t))
    _ = a^n := by rw [← Finset.sum_mul,mass_sum depth n x p hp hpx hxm hx1,one_mul]

theorem weightedMoment_succ (depth n : ℕ) (x : Fin (depth+1)→ℝ) (p : ℝ)
    (T : Fin (depth+1)→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ}
    (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    weightedMoment (depth+1) n x p T Z z=
      ∑c : OrderedFinpartition n,eppf (x 0) p c*∏i : Fin c.length,
        ∫g : E,weightedMoment depth (c.partSize i) (fun j => x j.succ) (x 0)
          (fun j => T j.succ) Z (z+T 0 g) ∂stdGaussian E := by
  classical
  unfold weightedMoment
  change (∑t : (Σc : OrderedFinpartition n,Children depth c),
    (eppf (x 0) p t.1*∏i : Fin t.1.length,mass depth (t.1.partSize i) (fun j => x j.succ) (x 0) (t.2 i))*
      ∏i : Fin t.1.length,∫g : E,treeMoment depth (t.1.partSize i) (fun j => T j.succ) Z (z+T 0 g) (t.2 i) ∂stdGaussian E)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin c.length) (t : NestedPartition depth (c.partSize i)) =>
    mass depth (c.partSize i) (fun j => x j.succ) (x 0) t*
      ∫g : E,treeMoment depth (c.partSize i) (fun j => T j.succ) Z (z+T 0 g) t ∂stdGaussian E)]
  apply Finset.prod_congr rfl
  intro i _
  have hi (t : NestedPartition depth (c.partSize i)) :=
    (treeMoment_integrable_shift depth (c.partSize i) (fun j => T j.succ) hZ ha hb (T 0) z t).const_mul
      (mass depth (c.partSize i) (fun j => x j.succ) (x 0) t)
  rw [integral_finset_sum _ (fun t _ => hi t)]
  simp_rw [integral_const_mul]

theorem weightedMoment_eq_pmf (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (T : Fin depth→E→L[ℝ]E) (Z : E→ℝ) (z : E) :
    weightedMoment depth n x p T Z z=
      ∑t : NestedPartition depth n,(partitionPMF depth n x p hp hpx hxm hx1 t).toReal*treeMoment depth n T Z z t := by
  unfold weightedMoment
  apply Finset.sum_congr rfl
  intro t _
  rw [partitionPMF_apply,ENNReal.toReal_ofReal (mass_nonneg depth n x p hp hpx hxm hx1 t)]

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMoments
