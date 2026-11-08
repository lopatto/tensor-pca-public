-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedLawAverage
public import TensorPCA.NonRSLowerProofs.FiniteNestedMarkedMomentMeasurability
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianVectorLaw

/-! Finite Gaussian tree products, averaging over varying strict-height families, and
the common-root weighted moment. The node bank includes variance y0; z0 is a
deterministic offset. Physical marked-law identification is treated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianLawAverage
open MeasureTheory ProbabilityTheory
open FiniteNestedPartition FiniteNestedGaussianFeature FiniteNestedGaussianVectorLaw
open FiniteNestedGaussianMarkedMoments FiniteNestedMarkedMomentMeasurability
open FiniteNestedDiscountedPartitionLaw FiniteNestedMassMeasurability
open FiniteNestedLawComparison FiniteNestedLawAverage FiniteNestedStrictSurrogate
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def treeProduct {depth n M : ℕ} (t : NestedPartition depth n) (y : Fin (depth+1)→ℝ)
    (Z : EuclideanSpace ℝ (Fin M)→ℝ) (z0 : EuclideanSpace ℝ (Fin M)) : ℝ :=
  ∫g : EuclideanSpace ℝ (Σc : Coordinate t,Fin M),
    ∏i : Fin n,Z (z0+vectorReplicaField t y M g i)
      ∂stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M))

theorem treeProduct_mem_Icc {depth n M : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) : treeProduct t y Z z0∈Set.Icc (0 : ℝ) (cap^n) := by
  unfold treeProduct
  refine ⟨integral_nonneg (fun g ↦ Finset.prod_nonneg (fun i _ ↦ (hBound _).1)),?_⟩
  have H := integral_mono (vector_mark_integrable t y M hZ hcap hBound z0)
    (integrable_const (cap^n)) (fun g ↦ by
      calc
        (∏i : Fin n,Z (z0+vectorReplicaField t y M g i))≤∏_i : Fin n,cap :=
          Finset.prod_le_prod₀ (fun i _ ↦ (hBound _).1) (fun i _ ↦ (hBound _).2)
        _=cap^n := by simp)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem treeProduct_eq_root_treeMoment {depth n M : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) :
    treeProduct t y Z z0=∫g : EuclideanSpace ℝ (Fin M),treeMoment depth n
      (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
      Z (z0+Real.sqrt (y 0) •g) t ∂stdGaussian (EuclideanSpace ℝ (Fin M)) :=
  vector_mark_eq_root_treeMoment t y M hZ hcap hBound z0

theorem strict_product_eq_root_weightedMoment {depth n M : ℕ} (x : Fin depth→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) :
    (∑t : NestedPartition depth n,(partitionPMF depth n x 0 (le_refl 0) hx hxm hx1 t).toReal*
      treeProduct t y Z z0)=
      ∫g : EuclideanSpace ℝ (Fin M),weightedMoment depth n x 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z0+Real.sqrt (y 0) •g) ∂stdGaussian (EuclideanSpace ℝ (Fin M)) := by
  classical
  let T := fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin M))
  have hi (t : NestedPartition depth n) : Integrable (fun g : EuclideanSpace ℝ (Fin M) ↦
      treeMoment depth n T Z (z0+Real.sqrt (y 0) •g) t) (stdGaussian (EuclideanSpace ℝ (Fin M))) := by
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using
      treeMoment_integrable_shift depth n T hZ hcap hBound
        (Real.sqrt (y 0) •ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin M))) z0 t
  calc
    _=∑t : NestedPartition depth n,(partitionPMF depth n x 0 (le_refl 0) hx hxm hx1 t).toReal*
        (∫g : EuclideanSpace ℝ (Fin M),treeMoment depth n T Z (z0+Real.sqrt (y 0) •g) t ∂stdGaussian _) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [treeProduct_eq_root_treeMoment t y hZ hcap hBound z0]
    _=∫g : EuclideanSpace ℝ (Fin M),∑t : NestedPartition depth n,
        (partitionPMF depth n x 0 (le_refl 0) hx hxm hx1 t).toReal*
          treeMoment depth n T Z (z0+Real.sqrt (y 0) •g) t ∂stdGaussian _ := by
      rw [integral_finset_sum _ (fun t _ ↦ (hi t).const_mul _)]
      simp_rw [integral_const_mul]
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun g ↦ (weightedMoment_eq_pmf depth n x 0 (le_refl 0) hx hxm hx1 T Z _).symm)

theorem root_weightedMoment_joint_integrable {A : Type*} [MeasurableSpace A] {depth n M : ℕ}
    (x : A→Fin depth→ℝ) (hxs : Measurable x)
    (hx : ∀a j,0<x a j) (hxm : ∀a,StrictMono (x a)) (hx1 : ∀a j,x a j≤1)
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] :
    Integrable (fun w : A×EuclideanSpace ℝ (Fin M) ↦ weightedMoment depth n (x w.1) 0
      (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
      Z (z0+Real.sqrt (y 0) •w.2)) (mu.prod (stdGaussian (EuclideanSpace ℝ (Fin M)))) := by
  let T := fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin M))
  have hShift : Continuous (fun g : EuclideanSpace ℝ (Fin M) ↦ z0+Real.sqrt (y 0) •g) := by
    fun_prop
  have hz : Measurable (fun w : A×EuclideanSpace ℝ (Fin M) ↦ z0+Real.sqrt (y 0) •w.2) :=
    hShift.measurable.comp measurable_snd
  have hm : Measurable (fun w : A×EuclideanSpace ℝ (Fin M) ↦
      weightedMoment depth n (x w.1) 0 T Z (z0+Real.sqrt (y 0) •w.2)) :=
    weightedMoment_measurable_comp depth n T hZ (fun w : A×EuclideanSpace ℝ (Fin M) ↦ x w.1) (fun _ ↦ 0)
      (fun w : A×EuclideanSpace ℝ (Fin M) ↦ z0+Real.sqrt (y 0) •w.2) (hxs.comp measurable_fst) measurable_const
      hz
  apply Integrable.of_bound hm.aestronglyMeasurable (cap^n)
  exact ae_of_all _ (fun w ↦ by
    have H := weightedMoment_mem depth n (x w.1) 0 (le_refl 0) (hx w.1) (hxm w.1) (hx1 w.1)
      T hZ hcap hBound (z0+Real.sqrt (y 0) •w.2)
    rw [Real.norm_of_nonneg H.1]
    exact H.2)

theorem strict_product_average_eq_weightedMoment {A : Type*} [MeasurableSpace A] {depth n M : ℕ}
    (x : A→Fin depth→ℝ) (hxs : Measurable x)
    (hx : ∀a j,0<x a j) (hxm : ∀a,StrictMono (x a)) (hx1 : ∀a j,x a j≤1)
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] :
    (∫a,∑t : NestedPartition depth n,(partitionPMF depth n (x a) 0 (le_refl 0) (hx a) (hxm a) (hx1 a) t).toReal*
      treeProduct t y Z z0 ∂mu)=
      ∫w : A×EuclideanSpace ℝ (Fin M),weightedMoment depth n (x w.1) 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z0+Real.sqrt (y 0) •w.2) ∂mu.prod (stdGaussian (EuclideanSpace ℝ (Fin M))) := by
  calc
    _=∫a,∫g : EuclideanSpace ℝ (Fin M),weightedMoment depth n (x a) 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z0+Real.sqrt (y 0) •g) ∂stdGaussian _ ∂mu := by
      apply integral_congr_ae
      exact ae_of_all _ (fun a ↦ strict_product_eq_root_weightedMoment (x a) (hx a) (hxm a) (hx1 a)
        y hZ hcap hBound z0)
    _=_ := (integral_prod _ (root_weightedMoment_joint_integrable x hxs hx hxm hx1 y hZ hcap hBound z0 mu)).symm

private theorem pmf_atom_le_one {B : Type*} (P : PMF B) (t : B) : (P t).toReal≤1 := by
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (P.coe_le_one t)

theorem law_product_integrable {A : Type*} [MeasurableSpace A] {depth n M : ℕ}
    (P : A→PMF (NestedPartition depth n)) (hP : ∀t,Measurable (fun a ↦ (P a t).toReal))
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] :
    Integrable (fun a ↦ ∑t : NestedPartition depth n,(P a t).toReal*treeProduct t y Z z0) mu := by
  classical
  apply integrable_finset_sum
  intro t _
  have hm : Measurable (fun a ↦ (P a t).toReal*treeProduct t y Z z0) :=
    (hP t).mul_const _
  apply Integrable.of_bound hm.aestronglyMeasurable (cap^n)
  exact ae_of_all _ (fun a ↦ by
    have HT := treeProduct_mem_Icc t y hZ hcap hBound z0
    have HP := pmf_atom_le_one (P a) t
    rw [Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg HT.1)]
    exact (mul_le_mul HP HT.2 HT.1 (by norm_num)).trans_eq (one_mul _))

theorem law_product_difference_le_l1 {A : Type*} [MeasurableSpace A] {depth n M : ℕ}
    (P Q : A→PMF (NestedPartition depth n))
    (hP : ∀t,Measurable (fun a ↦ (P a t).toReal)) (hQ : ∀t,Measurable (fun a ↦ (Q a t).toReal))
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] :
    |(∫a,∑t : NestedPartition depth n,(P a t).toReal*treeProduct t y Z z0 ∂mu)-
      (∫a,∑t : NestedPartition depth n,(Q a t).toReal*treeProduct t y Z z0 ∂mu)|≤
      cap^n*(∫a,l1Distance (P a) (Q a) ∂mu) := by
  have hiP := law_product_integrable P hP y hZ hcap hBound z0 mu
  have hiQ := law_product_integrable Q hQ y hZ hcap hBound z0 mu
  have hiL1 := (l1Distance_integrable P Q hP hQ mu).const_mul (cap^n)
  have hPoint (a : A) :
      ‖(∑t : NestedPartition depth n,(P a t).toReal*treeProduct t y Z z0)-
        (∑t : NestedPartition depth n,(Q a t).toReal*treeProduct t y Z z0)‖≤
        cap^n*l1Distance (P a) (Q a) := by
    rw [Real.norm_eq_abs]
    apply bounded_test_difference_le_l1 (P a) (Q a) (fun t ↦ treeProduct t y Z z0) (cap^n) (pow_nonneg hcap n)
    intro t
    have HT := treeProduct_mem_Icc t y hZ hcap hBound z0
    simpa only [abs_of_nonneg HT.1] using HT.2
  have H := norm_integral_le_of_norm_le hiL1 (ae_of_all mu hPoint)
  rw [integral_sub hiP hiQ,integral_const_mul] at H
  simpa only [Real.norm_eq_abs] using H

theorem law_product_error_le_strict_l1 {A : Type*} [MeasurableSpace A] {depth n M : ℕ}
    (P : A→PMF (NestedPartition depth n)) (hP : ∀t,Measurable (fun a ↦ (P a t).toReal))
    (x : A→Fin depth→ℝ) (hxs : Measurable x)
    (hx : ∀a j,0<x a j) (hxm : ∀a,StrictMono (x a)) (hx1 : ∀a j,x a j≤1)
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] :
    |(∫a,∑t : NestedPartition depth n,(P a t).toReal*treeProduct t y Z z0 ∂mu)-
      (∫w : A×EuclideanSpace ℝ (Fin M),weightedMoment depth n (x w.1) 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z0+Real.sqrt (y 0) •w.2) ∂mu.prod (stdGaussian (EuclideanSpace ℝ (Fin M))))|≤
      cap^n*(∫a,l1Distance (P a)
        (partitionPMF depth n (x a) 0 (le_refl 0) (hx a) (hxm a) (hx1 a)) ∂mu) := by
  let Q := fun a ↦ partitionPMF depth n (x a) 0 (le_refl 0) (hx a) (hxm a) (hx1 a)
  have hQ (t : NestedPartition depth n) : Measurable (fun a ↦ (Q a t).toReal) :=
    partitionPMF_toReal_measurable depth n x (fun _ ↦ 0) hxs measurable_const (fun _ ↦ le_refl 0) hx hxm hx1 t
  have H := law_product_difference_le_l1 P Q hP hQ y hZ hcap hBound z0 mu
  dsimp only [Q] at H
  rw [strict_product_average_eq_weightedMoment x hxs hx hxm hx1 y hZ hcap hBound z0 mu] at H
  exact H

theorem law_product_surrogate_error_le {A : Type*} [MeasurableSpace A] {M : ℕ}
    (depth N : ℕ) (x : A→Fin depth→ℝ) (hx : Measurable x)
    (hx0 : ∀a j,0≤x a j) (hxm : ∀a,Monotone (x a)) (hx1 : ∀a j,x a j≤1)
    (tau : ℝ) (htau : 0<tau) (htau1 : tau≤1)
    (P : (n : ℕ)→A→PMF (NestedPartition depth n))
    (hP : ∀n t,Measurable (fun a ↦ (P n a t).toReal))
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] (hN : 0<N) :
    |(∫a,∑t : NestedPartition depth N,(P N a t).toReal*treeProduct t y Z z0 ∂mu)-
      (∫w : A×EuclideanSpace ℝ (Fin M),weightedMoment depth N (strictHeightApprox depth (x w.1) tau) 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z0+Real.sqrt (y 0) •w.2) ∂mu.prod (stdGaussian (EuclideanSpace ℝ (Fin M))))|≤
      cap^N*((∑j ∈ Finset.Ico 1 N,∫a,recurrenceResidual depth j (x a) (P j a) (P (j+1) a) ∂mu)+
        mu.real Set.univ*(∑j ∈ Finset.Ico 1 N,
          ((j*depth+1 : ℕ) : ℝ)*(((j : ℝ)+1)*tau/(j : ℝ)))) := by
  have HP := law_product_error_le_strict_l1 (P N) (hP N)
    (fun a ↦ strictHeightApprox depth (x a) tau) (strictHeightApprox_measurable_comp depth x hx tau)
    (fun a ↦ strictHeightApprox_pos depth (x a) tau (hx0 a) htau htau1)
    (fun a ↦ strictHeightApprox_strictMono depth (x a) tau (hxm a) htau htau1)
    (fun a j ↦ (strictHeightApprox_lt_one depth (x a) tau (hx1 a) htau htau1 j).le)
    y hZ hcap hBound z0 mu
  have HL := averaged_surrogate_l1_le depth N x hx hx0 hxm hx1 tau htau htau1 P hP mu hN
  exact HP.trans (mul_le_mul_of_nonneg_left HL (pow_nonneg hcap N))


end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianLawAverage
