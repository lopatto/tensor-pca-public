-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGWeightObservable
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Joint-state replica permutation. Amplitude and Gaussian state are retained, so
amplitude-dependent old tests remain legitimate.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaPermutation
open MeasureTheory ProbabilityTheory
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable
noncomputable section
variable {Omega V : Type*} [MeasurableSpace Omega] [MeasurableSpace V]

def jointReindex (m : ℕ) (e : Equiv.Perm (Fin m)) (q : Omega×(Fin m → V)) : Omega×(Fin m → V) :=
  (q.1,fun i ↦ q.2 (e i))

theorem jointReindex_measurable (m : ℕ) (e : Equiv.Perm (Fin m)) :
    Measurable (jointReindex (Omega := Omega) (V := V) m e) :=
  measurable_fst.prodMk (Measurable.of_eval (fun i ↦ (measurable_pi_apply (e i)).comp measurable_snd))

theorem iid_map_permutation (G : Kernel Omega V) [IsMarkovKernel G]
    (m : ℕ) (e : Equiv.Perm (Fin m)) :
    (iid G m).map (fun old : Fin m → V ↦ fun i ↦ old (e i))=iid G m := by
  have hm : Measurable (fun old : Fin m → V ↦ fun i ↦ old (e i)) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  apply Kernel.ext
  intro w
  simp only [Kernel.map_apply _ hm,iid_apply]
  have H := (measurePreserving_piCongrLeft (fun _ : Fin m ↦ G w) e.symm).map_eq
  convert H using 1
  congr 1
  funext old i
  simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

theorem joint_replica_permutation_hasLaw (d : Measure Omega) [IsProbabilityMeasure d]
    (G : Kernel Omega V) [IsMarkovKernel G] (m : ℕ) (e : Equiv.Perm (Fin m)) :
    HasLaw (jointReindex m e) (d⊗ₘiid G m) (d⊗ₘiid G m) := by
  have hm : Measurable (fun old : Fin m → V ↦ fun i ↦ old (e i)) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  refine ⟨(jointReindex_measurable m e).aemeasurable,?_⟩
  have H := Measure.compProd_map (μ := d) (κ := iid G m) hm
  rw [iid_map_permutation G m e] at H
  convert H.symm using 1
  rfl

theorem jointLaw_permutation_hasLaw {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (e : Equiv.Perm (Fin (n+1))) :
    HasLaw (jointReindex (n+1) e) (jointLaw (K := K) nu v n) (jointLaw nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact joint_replica_permutation_hasLaw
    ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)))
    (parameterizedGibbsKernel nu v) (n+1) e

theorem old_test_reindex_measurable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (m : ℕ) (e : Equiv.Perm (Fin m))
    (Phi : X → (Fin m → W) → ℝ)
    (hPhi : Measurable (fun q : X×(Fin m → W) ↦ Phi q.1 q.2)) :
    Measurable (fun q : X×(Fin m → W) ↦ Phi q.1 (fun i ↦ q.2 (e i))) := by
  convert hPhi.comp (jointReindex_measurable m e) using 1 <;> rfl

theorem old_test_integral_reindex {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (e : Equiv.Perm (Fin (n+1)))
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun q : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi q.1 q.2)) :
    (∫ q,Phi q.1.1 (fun i ↦ q.2 (e i)) ∂jointLaw nu v n)=
      ∫ q,Phi q.1.1 q.2 ∂jointLaw nu v n := by
  have HM : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) ↦ Phi q.1.1 q.2) :=
    hPhi.comp (measurable_fst.fst.prodMk measurable_snd)
  exact (jointLaw_permutation_hasLaw nu hv n e).integral_comp HM.aestronglyMeasurable

end
end TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaPermutation
