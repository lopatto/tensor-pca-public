-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedStrictSurrogate

/-! Parametric measurability of the literal finite nested mass formula. Division is
total real division, so no probability interpretation is asserted outside the
strict-height domain. No measurable PMF/Tree instance is added.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedMassMeasurability
open MeasureTheory
open FiniteNestedPartition FiniteDiscountedPartitionProofs FiniteNestedDiscountedPartitionLaw
open FiniteNestedStrictSurrogate
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem clusterFactor_joint_measurable (b : ℕ) :
    Measurable (fun p : ℝ×ℝ ↦ clusterFactor p.1 p.2 b) := by
  unfold clusterFactor
  exact Finset.measurable_prod _ (fun j _ ↦ (measurable_fst.const_mul (j : ℝ)).sub measurable_snd)

theorem blockFactor_measurable (s : ℕ) : Measurable (fun alpha : ℝ ↦ blockFactor alpha s) := by
  unfold blockFactor
  exact Finset.measurable_prod _ (fun j _ ↦ measurable_const.sub measurable_id)

theorem normalizer_measurable (n : ℕ) : Measurable (fun p : ℝ ↦ normalizer p n) := by
  unfold normalizer
  exact Finset.measurable_prod _ (fun j _ ↦ measurable_const.sub measurable_id)

theorem eppf_joint_measurable {n : ℕ} (c : OrderedFinpartition n) :
    Measurable (fun p : ℝ×ℝ ↦ eppf p.1 p.2 c) := by
  unfold eppf
  exact ((clusterFactor_joint_measurable c.length).mul
    (Finset.measurable_prod _ (fun i _ ↦ (blockFactor_measurable (c.partSize i)).comp measurable_fst))).div
      ((normalizer_measurable n).comp measurable_snd)

theorem mass_joint_measurable (depth n : ℕ) (t : NestedPartition depth n) :
    Measurable (fun p : (Fin depth→ℝ)×ℝ ↦ mass depth n p.1 p.2 t) := by
  classical
  induction depth generalizing n with
  | zero => simp only [mass]; exact measurable_const
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    change Measurable (fun p : (Fin (depth+1)→ℝ)×ℝ ↦
      eppf (p.1 0) p.2 c*∏i : Fin c.length,
        mass depth (c.partSize i) (fun j ↦ p.1 j.succ) (p.1 0) (f i))
    have hTail : Measurable (fun p : (Fin (depth+1)→ℝ)×ℝ ↦ fun j : Fin depth ↦ p.1 j.succ) := by
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply j.succ).comp measurable_fst
    have hZero : Measurable (fun p : (Fin (depth+1)→ℝ)×ℝ ↦ p.1 (0 : Fin (depth+1))) :=
      (measurable_pi_apply (0 : Fin (depth+1))).comp measurable_fst
    apply Measurable.mul
    · exact (eppf_joint_measurable c).comp (hZero.prodMk measurable_snd)
    · exact Finset.measurable_prod _ (fun i _ ↦ (ih (c.partSize i) (f i)).comp
        (hTail.prodMk hZero))

theorem mass_measurable_comp {A : Type*} [MeasurableSpace A] (depth n : ℕ)
    (x : A→Fin depth→ℝ) (p : A→ℝ) (hx : Measurable x) (hp : Measurable p)
    (t : NestedPartition depth n) : Measurable (fun a ↦ mass depth n (x a) (p a) t) :=
  (mass_joint_measurable depth n t).comp (hx.prodMk hp)

theorem partitionPMF_toReal_apply (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) :
    (partitionPMF depth n x p hp hpx hxm hx1 t).toReal=mass depth n x p t := by
  rw [partitionPMF_apply,ENNReal.toReal_ofReal (mass_nonneg depth n x p hp hpx hxm hx1 t)]

theorem partitionPMF_toReal_measurable {A : Type*} [MeasurableSpace A] (depth n : ℕ)
    (x : A→Fin depth→ℝ) (p : A→ℝ) (hx : Measurable x) (hp : Measurable p)
    (hp0 : ∀a,0≤p a) (hpx : ∀a j,p a<x a j) (hxm : ∀a,StrictMono (x a)) (hx1 : ∀a j,x a j≤1)
    (t : NestedPartition depth n) :
    Measurable (fun a ↦ (partitionPMF depth n (x a) (p a) (hp0 a) (hpx a) (hxm a) (hx1 a) t).toReal) := by
  simp_rw [partitionPMF_toReal_apply]
  exact mass_measurable_comp depth n x p hx hp t

theorem strictHeightApprox_measurable_comp {A : Type*} [MeasurableSpace A] (depth : ℕ)
    (x : A→Fin depth→ℝ) (hx : Measurable x) (tau : ℝ) :
    Measurable (fun a ↦ strictHeightApprox depth (x a) tau) :=
  (strictHeightApprox_joint_measurable depth).comp (hx.prodMk measurable_const)

theorem surrogate_partitionPMF_toReal_measurable {A : Type*} [MeasurableSpace A]
    (depth n : ℕ) (x : A→Fin depth→ℝ) (hx : Measurable x)
    (hx0 : ∀a j,0≤x a j) (hxm : ∀a,Monotone (x a)) (hx1 : ∀a j,x a j≤1)
    (tau : ℝ) (htau : 0<tau) (htau1 : tau≤1) (t : NestedPartition depth n) :
    Measurable (fun a ↦ (partitionPMF depth n (strictHeightApprox depth (x a) tau) 0 (le_refl 0)
      (strictHeightApprox_pos depth (x a) tau (hx0 a) htau htau1)
      (strictHeightApprox_strictMono depth (x a) tau (hxm a) htau htau1)
      (fun j ↦ (strictHeightApprox_lt_one depth (x a) tau (hx1 a) htau htau1 j).le) t).toReal) := by
  apply partitionPMF_toReal_measurable
  · exact strictHeightApprox_measurable_comp depth x hx tau
  · exact measurable_const

end
end TensorPCA.NonRSLowerProofs.FiniteNestedMassMeasurability
