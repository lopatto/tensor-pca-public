-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedMassMeasurability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite-measure averaging of the exact strict-surrogate law comparison.
Weak insertion coefficients are only nonnegative normalized real rows, never
a second sampler. In particular a restricted amplitude probability is not
renormalized; its true mass multiplies the deterministic row error. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedLawAverage
open MeasureTheory
open FiniteNestedPartition FiniteNestedInsertionNumerators FiniteNestedLawComparison
open FiniteNestedDiscountedPartitionLaw FiniteNestedStrictSurrogate FiniteNestedMassMeasurability
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pmf_real_sum {B : Type*} [Fintype B] (P : PMF B) :
    (∑t : B,(P t).toReal)=1 := by
  rw [← ENNReal.toReal_sum (fun t _ ↦ P.apply_ne_top t)]
  have H : (∑t : B,P t)=1 := by simpa only [tsum_fintype] using P.tsum_coe
  rw [H,ENNReal.toReal_one]

theorem numerator_parameter_measurable {A : Type*} [MeasurableSpace A]
    (depth n : ℕ) (x : A→Fin depth→ℝ) (p : A→ℝ) (hx : Measurable x) (hp : Measurable p)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    Measurable (fun a ↦ numerator depth n (x a) (p a) t o) := by
  induction depth generalizing n p with
  | zero => exact measurable_const.sub hp
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    have hZero : Measurable (fun a ↦ x a (0 : Fin (depth+1))) :=
      (measurable_pi_apply (0 : Fin (depth+1))).comp hx
    have hTail : Measurable (fun a ↦ fun j : Fin depth ↦ x a j.succ) :=
      Measurable.of_eval (fun j ↦ (measurable_pi_apply j.succ).comp hx)
    cases o with
    | none => exact (hZero.const_mul (c.length : ℝ)).sub hp
    | some a =>
      obtain ⟨k,o⟩ := a
      exact ih (c.partSize k) (fun a j ↦ x a j.succ) (fun a ↦ x a 0) hTail hZero (f k) o

theorem weak_root_row_nonneg (depth n : ℕ) (x : Fin depth→ℝ)
    (hx0 : ∀j,0≤x j) (hxm : Monotone x) (hx1 : ∀j,x j≤1) (hn : 0<n)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    0≤numerator depth n x 0 t o/(n : ℝ) := by
  exact div_nonneg (numerator_nonneg depth n x 0 hn (le_refl 0) zero_le_one hx0 hxm hx1 t o)
    (Nat.cast_nonneg n)

theorem weak_root_row_sum (depth n : ℕ) (x : Fin depth→ℝ) (hn : 0<n)
    (t : NestedPartition depth n) :
    (∑o : Insertion depth n t,numerator depth n x 0 t o/(n : ℝ))=1 := by
  rw [← Finset.sum_div,numerator_sum,sub_zero]
  exact div_self (by exact_mod_cast hn.ne')

theorem l1Distance_mem_Icc {B : Type*} [Fintype B] (P Q : PMF B) :
    l1Distance P Q∈Set.Icc (0 : ℝ) 2 := by
  classical
  refine ⟨Finset.sum_nonneg (fun t _ ↦ abs_nonneg _),?_⟩
  calc
    l1Distance P Q≤∑t : B,((P t).toReal+(Q t).toReal) := by
      apply Finset.sum_le_sum
      intro t _
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg ENNReal.toReal_nonneg])
    _=2 := by rw [Finset.sum_add_distrib,pmf_real_sum,pmf_real_sum]; norm_num

theorem recurrenceResidual_mem_Icc (depth n : ℕ) (x : Fin depth→ℝ)
    (hx0 : ∀j,0≤x j) (hxm : Monotone x) (hx1 : ∀j,x j≤1) (hn : 0<n)
    (P : PMF (NestedPartition depth n)) (Pnext : PMF (NestedPartition depth (n+1))) :
    recurrenceResidual depth n x P Pnext∈Set.Icc (0 : ℝ) 2 := by
  classical
  let w := fun (t : NestedPartition depth n) (o : Insertion depth n t) ↦ numerator depth n x 0 t o/(n : ℝ)
  have hw (t) (o) : 0≤w t o := weak_root_row_nonneg depth n x hx0 hxm hx1 hn t o
  have hwSum (t) : (∑o : Insertion depth n t,w t o)=1 := weak_root_row_sum depth n x hn t
  have hLeft : (∑t : NestedPartition depth n,∑o : Insertion depth n t,
      (Pnext ((extendEquiv depth n) ⟨t,o⟩)).toReal)=1 := by
    have H := pmf_real_sum Pnext
    rw [← Fintype.sum_equiv (extendEquiv depth n)
      (fun s ↦ (Pnext ((extendEquiv depth n) s)).toReal) (fun s ↦ (Pnext s).toReal) (fun _ ↦ rfl),
      Fintype.sum_sigma] at H
    exact H
  have hRight : (∑t : NestedPartition depth n,∑o : Insertion depth n t,(P t).toReal*w t o)=1 := by
    simp_rw [← Finset.mul_sum,hwSum,mul_one]
    exact pmf_real_sum P
  refine ⟨Finset.sum_nonneg (fun t _ ↦ Finset.sum_nonneg (fun o _ ↦ abs_nonneg _)),?_⟩
  calc
    recurrenceResidual depth n x P Pnext≤∑t : NestedPartition depth n,∑o : Insertion depth n t,
        ((Pnext ((extendEquiv depth n) ⟨t,o⟩)).toReal+(P t).toReal*w t o) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro o _
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hw t o))])
    _=2 := by simp_rw [Finset.sum_add_distrib]; rw [hLeft,hRight]; norm_num

theorem l1Distance_measurable {A B : Type*} [MeasurableSpace A] [Fintype B]
    (P Q : A→PMF B) (hP : ∀t,Measurable (fun a ↦ (P a t).toReal))
    (hQ : ∀t,Measurable (fun a ↦ (Q a t).toReal)) :
    Measurable (fun a ↦ l1Distance (P a) (Q a)) := by
  unfold l1Distance
  exact Finset.measurable_sum _ (fun t _ ↦ by
    simpa only [Real.norm_eq_abs,Pi.sub_apply,Pi.mul_apply] using ((hP t).sub (hQ t)).norm)

theorem recurrenceResidual_measurable {A : Type*} [MeasurableSpace A]
    (depth n : ℕ) (x : A→Fin depth→ℝ) (hx : Measurable x)
    (P : A→PMF (NestedPartition depth n)) (Pnext : A→PMF (NestedPartition depth (n+1)))
    (hP : ∀t,Measurable (fun a ↦ (P a t).toReal))
    (hPnext : ∀t,Measurable (fun a ↦ (Pnext a t).toReal)) :
    Measurable (fun a ↦ recurrenceResidual depth n (x a) (P a) (Pnext a)) := by
  unfold recurrenceResidual
  apply Finset.measurable_sum
  intro t _
  apply Finset.measurable_sum
  intro o _
  have H := (hPnext ((extendEquiv depth n) ⟨t,o⟩)).sub ((hP t).mul
    ((numerator_parameter_measurable depth n x (fun _ ↦ 0) hx measurable_const t o).div_const (n : ℝ)))
  simpa only [Real.norm_eq_abs,Pi.sub_apply,Pi.mul_apply] using H.norm

theorem l1Distance_integrable {A B : Type*} [MeasurableSpace A] [Fintype B]
    (P Q : A→PMF B) (hP : ∀t,Measurable (fun a ↦ (P a t).toReal))
    (hQ : ∀t,Measurable (fun a ↦ (Q a t).toReal)) (mu : Measure A) [IsFiniteMeasure mu] :
    Integrable (fun a ↦ l1Distance (P a) (Q a)) mu := by
  apply Integrable.of_bound (l1Distance_measurable P Q hP hQ).aestronglyMeasurable 2
  exact ae_of_all _ (fun a ↦ by
    have H := l1Distance_mem_Icc (P a) (Q a)
    rw [Real.norm_of_nonneg H.1]
    exact H.2)

theorem recurrenceResidual_integrable {A : Type*} [MeasurableSpace A]
    (depth n : ℕ) (x : A→Fin depth→ℝ) (hx : Measurable x)
    (hx0 : ∀a j,0≤x a j) (hxm : ∀a,Monotone (x a)) (hx1 : ∀a j,x a j≤1) (hn : 0<n)
    (P : A→PMF (NestedPartition depth n)) (Pnext : A→PMF (NestedPartition depth (n+1)))
    (hP : ∀t,Measurable (fun a ↦ (P a t).toReal))
    (hPnext : ∀t,Measurable (fun a ↦ (Pnext a t).toReal))
    (mu : Measure A) [IsFiniteMeasure mu] :
    Integrable (fun a ↦ recurrenceResidual depth n (x a) (P a) (Pnext a)) mu := by
  apply Integrable.of_bound (recurrenceResidual_measurable depth n x hx P Pnext hP hPnext).aestronglyMeasurable 2
  exact ae_of_all _ (fun a ↦ by
    have H := recurrenceResidual_mem_Icc depth n (x a) (hx0 a) (hxm a) (hx1 a) hn (P a) (Pnext a)
    rw [Real.norm_of_nonneg H.1]
    exact H.2)

/-- Averaging also covers a probability restricted to any measurable mask:
its true mass is retained, with no normalization or weak-height sampler. -/
theorem averaged_surrogate_l1_le {A : Type*} [MeasurableSpace A]
    (depth N : ℕ) (x : A→Fin depth→ℝ) (hx : Measurable x)
    (hx0 : ∀a j,0≤x a j) (hxm : ∀a,Monotone (x a)) (hx1 : ∀a j,x a j≤1)
    (tau : ℝ) (htau : 0<tau) (htau1 : tau≤1)
    (P : (n : ℕ)→A→PMF (NestedPartition depth n))
    (hP : ∀n t,Measurable (fun a ↦ (P n a t).toReal))
    (mu : Measure A) [IsFiniteMeasure mu] (hN : 0<N) :
    (∫a,l1Distance (P N a)
      (partitionPMF depth N (strictHeightApprox depth (x a) tau) 0 (le_refl 0)
        (strictHeightApprox_pos depth (x a) tau (hx0 a) htau htau1)
        (strictHeightApprox_strictMono depth (x a) tau (hxm a) htau htau1)
        (fun j ↦ (strictHeightApprox_lt_one depth (x a) tau (hx1 a) htau htau1 j).le)) ∂mu)≤
      (∑j ∈ Finset.Ico 1 N,∫a,recurrenceResidual depth j (x a) (P j a) (P (j+1) a) ∂mu)+
        mu.real Set.univ*(∑j ∈ Finset.Ico 1 N,
          ((j*depth+1 : ℕ) : ℝ)*(((j : ℝ)+1)*tau/(j : ℝ))) := by
  classical
  let Q := fun (n : ℕ) (a : A) ↦
    partitionPMF depth n (strictHeightApprox depth (x a) tau) 0 (le_refl 0)
      (strictHeightApprox_pos depth (x a) tau (hx0 a) htau htau1)
      (strictHeightApprox_strictMono depth (x a) tau (hxm a) htau htau1)
      (fun j ↦ (strictHeightApprox_lt_one depth (x a) tau (hx1 a) htau htau1 j).le)
  let S := fun j : ℕ ↦ ((j*depth+1 : ℕ) : ℝ)*(((j : ℝ)+1)*tau/(j : ℝ))
  have hQ (n : ℕ) (t : NestedPartition depth n) : Measurable (fun a ↦ (Q n a t).toReal) :=
    surrogate_partitionPMF_toReal_measurable depth n x hx hx0 hxm hx1 tau htau htau1 t
  have hL1 := l1Distance_integrable (P N) (Q N) (hP N) (hQ N) mu
  have hR (j : ℕ) (hj : j∈Finset.Ico 1 N) :
      Integrable (fun a ↦ recurrenceResidual depth j (x a) (P j a) (P (j+1) a)) mu :=
    recurrenceResidual_integrable depth j x hx hx0 hxm hx1 (Finset.mem_Ico.mp hj).1
      (P j) (P (j+1)) (hP j) (hP (j+1)) mu
  have hTerm (j : ℕ) (hj : j∈Finset.Ico 1 N) : Integrable (fun a ↦
      recurrenceResidual depth j (x a) (P j a) (P (j+1) a)+S j) mu := by
    change Integrable ((fun a : A ↦ recurrenceResidual depth j (x a) (P j a) (P (j+1) a)) +
      (fun _ : A ↦ S j)) mu
    exact (hR j hj).add (integrable_const (S j))
  have hSum : Integrable (fun a ↦ ∑j ∈ Finset.Ico 1 N,
      (recurrenceResidual depth j (x a) (P j a) (P (j+1) a)+S j)) mu :=
    integrable_finset_sum _ hTerm
  have hPoint (a : A) : l1Distance (P N a) (Q N a)≤∑j ∈ Finset.Ico 1 N,
      (recurrenceResidual depth j (x a) (P j a) (P (j+1) a)+S j) :=
    surrogate_l1Distance_family_le depth N (x a) tau (hx0 a) (hxm a) (hx1 a) htau htau1
      (fun j ↦ P j a) hN
  change (∫a,l1Distance (P N a) (Q N a) ∂mu)≤
    (∑j ∈ Finset.Ico 1 N,∫a,recurrenceResidual depth j (x a) (P j a) (P (j+1) a) ∂mu)+
      mu.real Set.univ*(∑j ∈ Finset.Ico 1 N,S j)
  calc
    (∫a,l1Distance (P N a) (Q N a) ∂mu)≤∫a,∑j ∈ Finset.Ico 1 N,
        (recurrenceResidual depth j (x a) (P j a) (P (j+1) a)+S j) ∂mu :=
      integral_mono hL1 hSum hPoint
    _=∑j ∈ Finset.Ico 1 N,
        ((∫a,recurrenceResidual depth j (x a) (P j a) (P (j+1) a) ∂mu)+mu.real Set.univ*S j) := by
      rw [integral_finset_sum _ hTerm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_add (hR j hj) (integrable_const (S j)),integral_const,smul_eq_mul]
    _=(∑j ∈ Finset.Ico 1 N,∫a,recurrenceResidual depth j (x a) (P j a) (P (j+1) a) ∂mu)+
        mu.real Set.univ*(∑j ∈ Finset.Ico 1 N,S j) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]


end
end TensorPCA.NonRSLowerProofs.FiniteNestedLawAverage
