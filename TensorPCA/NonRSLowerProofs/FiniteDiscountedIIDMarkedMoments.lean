-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedBoundedMarkedDerivatives
public import Mathlib.MeasureTheory.Integral.Pi

/-! Literal finite iid block-mark integrals for the canonical discounted
partition law. Each block receives one independent mark. No sampler or
new hierarchy representation is introduced. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedIIDMarkedMoments
open MeasureTheory ProbabilityTheory
open FiniteDiscountedPartitionProofs FiniteDiscountedPartitionLaw
open scoped BigOperators
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem replica_product_eq_block_powers {n : ℕ} (c : OrderedFinpartition n)
    (Z : V→ℝ) (marks : Fin c.length→V) :
    (∏j : Fin n,Z (marks ((c.equivSigma.symm j).1)))=
      ∏i : Fin c.length,(Z (marks i))^(c.partSize i) := by
  classical
  have H := Fintype.prod_equiv c.equivSigma
    (fun s : Σi : Fin c.length,Fin (c.partSize i) => Z (marks s.1))
    (fun j : Fin n => Z (marks ((c.equivSigma.symm j).1))) (fun s => by simp)
  rw [← H,Fintype.prod_sigma]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem iid_block_mark_integral_eq_moments (nu : Measure V) [IsProbabilityMeasure nu]
    {n : ℕ} (c : OrderedFinpartition n) (Z : V→ℝ) :
    (∫marks : Fin c.length→V,∏j : Fin n,Z (marks ((c.equivSigma.symm j).1))
      ∂Measure.pi (fun _ : Fin c.length => nu))=
      ∏i : Fin c.length,∫v,(Z v)^(c.partSize i) ∂nu := by
  simp_rw [replica_product_eq_block_powers]
  exact integral_fintype_prod_eq_prod (fun i v => (Z v)^(c.partSize i))

theorem bounded_mark_power_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (n : ℕ) : Integrable (fun v => (Z v)^n) nu := by
  apply Integrable.of_bound (hZ.pow_const n).aestronglyMeasurable (a^n)
  filter_upwards [hb] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hv.1 n)]
  exact pow_le_pow_left₀ hv.1 hv.2 n

theorem bounded_mark_moment_mem (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (n : ℕ) :
    0≤(∫v,(Z v)^n ∂nu) ∧ (∫v,(Z v)^n ∂nu)≤a^n := by
  refine ⟨integral_nonneg_of_ae (hb.mono (fun _ hv => pow_nonneg hv.1 n)),?_⟩
  have H := integral_mono_ae (bounded_mark_power_integrable nu hZ ha hb n)
    (integrable_const (a^n)) (hb.mono (fun _ hv => pow_le_pow_left₀ hv.1 hv.2 n))
  simpa using H

theorem iid_block_mark_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {n : ℕ} (c : OrderedFinpartition n) {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) :
    Integrable (fun marks : Fin c.length→V => ∏j : Fin n,Z (marks ((c.equivSigma.symm j).1)))
      (Measure.pi (fun _ : Fin c.length => nu)) := by
  simp_rw [replica_product_eq_block_powers]
  exact Integrable.fintype_prod (fun i => bounded_mark_power_integrable nu hZ ha hb (c.partSize i))

theorem iid_block_mark_integral_mem (nu : Measure V) [IsProbabilityMeasure nu]
    {n : ℕ} (c : OrderedFinpartition n) {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) :
    let I := ∫marks : Fin c.length→V,∏j : Fin n,Z (marks ((c.equivSigma.symm j).1))
      ∂Measure.pi (fun _ : Fin c.length => nu)
    0≤I ∧ I≤a^n := by
  dsimp only
  rw [iid_block_mark_integral_eq_moments]
  have H (i : Fin c.length) := bounded_mark_moment_mem nu hZ ha hb (c.partSize i)
  refine ⟨Finset.prod_nonneg (fun i _ => (H i).1),?_⟩
  calc
    (∏i,∫v,(Z v)^(c.partSize i) ∂nu) ≤ ∏i : Fin c.length,a^(c.partSize i) :=
      Finset.prod_le_prod₀ (fun i _ => (H i).1) (fun i _ => (H i).2)
    _ = a^n := by rw [Finset.prod_pow_eq_pow_sum,sum_partSize]

theorem discounted_marked_moment_mem (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) {alpha p : ℝ}
    (hp : 0≤p) (hpa : p<alpha) (halpha : alpha≤1) (n : ℕ) :
    let I := ∑c : OrderedFinpartition n,
      (discountedPartitionPMF alpha p hp hpa halpha n c).toReal*
        (∫marks : Fin c.length→V,∏j : Fin n,Z (marks ((c.equivSigma.symm j).1))
          ∂Measure.pi (fun _ : Fin c.length => nu))
    0≤I ∧ I≤a^n := by
  dsimp only
  simp_rw [discountedPartitionPMF_apply,ENNReal.toReal_ofReal (eppf_nonneg hp hpa halpha _)]
  have H (c : OrderedFinpartition n) := iid_block_mark_integral_mem nu c hZ ha hb
  refine ⟨Finset.sum_nonneg (fun c _ => mul_nonneg (eppf_nonneg hp hpa halpha c) (H c).1),?_⟩
  calc
    _ ≤ ∑c : OrderedFinpartition n,eppf alpha p c*a^n :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (H c).2 (eppf_nonneg hp hpa halpha c))
    _ = a^n := by rw [← Finset.sum_mul,eppf_sum hp hpa halpha n,one_mul]

theorem power_transform_derivative_eq_iid_block_integrals
    (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) {alpha p : ℝ}
    (hp : 0≤p) (hpa : p<alpha) (halpha : alpha≤1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun t : ℝ => (BoundedMarkedPowerTransform.markTransform nu Z alpha t)^(p/alpha)) 0=
      (-p*normalizer p n)*∑c : OrderedFinpartition n,
        (discountedPartitionPMF alpha p hp hpa halpha n c).toReal*
          (∫marks : Fin c.length→V,∏j : Fin n,Z (marks ((c.equivSigma.symm j).1))
            ∂Measure.pi (fun _ : Fin c.length => nu)) := by
  have hb' : ∀ᵐv∂nu,|Z v|≤a := hb.mono (fun _ hv => by rw [abs_of_nonneg hv.1]; exact hv.2)
  simpa only [iid_block_mark_integral_eq_moments] using
    FiniteDiscountedBoundedMarkedDerivatives.power_markTransform_iteratedDeriv nu hZ ha hb' hp hpa halpha hn

theorem log_transform_derivative_eq_iid_block_integrals
    (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) {alpha : ℝ}
    (hpos : 0<alpha) (halpha : alpha≤1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun t : ℝ => Real.log (BoundedMarkedPowerTransform.markTransform nu Z alpha t)/alpha) 0=
      -normalizer 0 n*∑c : OrderedFinpartition n,
        (discountedPartitionPMF alpha 0 le_rfl hpos halpha n c).toReal*
          (∫marks : Fin c.length→V,∏j : Fin n,Z (marks ((c.equivSigma.symm j).1))
            ∂Measure.pi (fun _ : Fin c.length => nu)) := by
  have hb' : ∀ᵐv∂nu,|Z v|≤a := hb.mono (fun _ hv => by rw [abs_of_nonneg hv.1]; exact hv.2)
  simpa only [iid_block_mark_integral_eq_moments] using
    FiniteDiscountedBoundedMarkedDerivatives.log_markTransform_iteratedDeriv nu hZ ha hb' hpos halpha hn

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedIIDMarkedMoments
