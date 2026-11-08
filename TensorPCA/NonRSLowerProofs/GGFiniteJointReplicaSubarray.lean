-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaPermutation

/-! Iid subarrays along finite injections, retaining the entire original
amplitude/disorder state. No GG or ultrametricity identity is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaSubarray
open MeasureTheory ProbabilityTheory
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable
noncomputable section
variable {Omega V : Type*} [MeasurableSpace Omega] [MeasurableSpace V]

def jointSubarray {m n : ℕ} (e : Fin m ↪ Fin n)
    (q : Omega×(Fin n → V)) : Omega×(Fin m → V) := (q.1,fun i ↦ q.2 (e i))

theorem jointSubarray_measurable {m n : ℕ} (e : Fin m ↪ Fin n) :
    Measurable (jointSubarray (Omega := Omega) (V := V) e) :=
  measurable_fst.prodMk (Measurable.of_eval (fun i ↦ (measurable_pi_apply (e i)).comp measurable_snd))

theorem subarray_pi_hasLaw (nu : Measure V) [IsProbabilityMeasure nu]
    {m n : ℕ} (e : Fin m ↪ Fin n) :
    HasLaw (fun old : Fin n → V ↦ fun i ↦ old (e i))
      (Measure.pi (fun _ : Fin m ↦ nu)) (Measure.pi (fun _ : Fin n ↦ nu)) := by
  have hInd : iIndepFun (fun i (old : Fin n → V) ↦ old i) (Measure.pi (fun _ : Fin n ↦ nu)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hSub := iIndepFun.precomp e.injective hInd
  exact hSub.hasLaw_pi (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ nu) (e i)).hasLaw)

theorem iid_map_subarray (G : Kernel Omega V) [IsMarkovKernel G]
    {m n : ℕ} (e : Fin m ↪ Fin n) :
    (iid G n).map (fun old : Fin n → V ↦ fun i ↦ old (e i))=iid G m := by
  have hm : Measurable (fun old : Fin n → V ↦ fun i ↦ old (e i)) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  apply Kernel.ext
  intro w
  rw [Kernel.map_apply _ hm,iid_apply,iid_apply]
  exact (subarray_pi_hasLaw (G w) e).map_eq

theorem joint_replica_subarray_hasLaw (d : Measure Omega) [IsProbabilityMeasure d]
    (G : Kernel Omega V) [IsMarkovKernel G] {m n : ℕ} (e : Fin m ↪ Fin n) :
    HasLaw (jointSubarray e) (d⊗ₘiid G m) (d⊗ₘiid G n) := by
  have hm : Measurable (fun old : Fin n → V ↦ fun i ↦ old (e i)) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  refine ⟨(jointSubarray_measurable e).aemeasurable,?_⟩
  have H := Measure.compProd_map (μ := d) (κ := iid G n) hm
  rw [iid_map_subarray G e] at H
  convert H.symm using 1
  rfl

theorem jointLaw_subarray_hasLaw {N K m n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (e : Fin (m+1) ↪ Fin (n+1)) :
    HasLaw (jointSubarray e) (jointLaw (K := K) nu v m) (jointLaw nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact joint_replica_subarray_hasLaw
    ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)))
    (parameterizedGibbsKernel nu v) e

end
end TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaSubarray
