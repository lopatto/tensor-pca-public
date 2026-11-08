-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaPermutation

/-! State-preserving iid reindex along an explicit finite equivalence.
This handles the two block orders without dependent arithmetic casts. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaReindex
open MeasureTheory ProbabilityTheory
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable
noncomputable section
variable {Omega W : Type*} [MeasurableSpace Omega] [MeasurableSpace W]

def jointAlong {m k : ℕ} (e : Fin k ≃ Fin m) (q : Omega×(Fin m → W)) : Omega×(Fin k → W) :=
  (q.1,fun i ↦ q.2 (e i))

theorem jointAlong_measurable {m k : ℕ} (e : Fin k ≃ Fin m) :
    Measurable (jointAlong (Omega := Omega) (W := W) e) :=
  measurable_fst.prodMk (Measurable.of_eval (fun i ↦ (measurable_pi_apply (e i)).comp measurable_snd))

theorem iid_map_along (G : Kernel Omega W) [IsMarkovKernel G] {m k : ℕ} (e : Fin k ≃ Fin m) :
    (iid G m).map (fun old : Fin m → W ↦ fun i ↦ old (e i))=iid G k := by
  have hm : Measurable (fun old : Fin m → W ↦ fun i ↦ old (e i)) := Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  apply Kernel.ext
  intro w
  simp only [Kernel.map_apply _ hm,iid_apply]
  have H := (measurePreserving_piCongrLeft (fun _ : Fin k ↦ G w) e.symm).map_eq
  convert H using 1
  congr 1
  funext old i
  simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

theorem joint_along_hasLaw (d : Measure Omega) [IsProbabilityMeasure d]
    (G : Kernel Omega W) [IsMarkovKernel G] {m k : ℕ} (e : Fin k ≃ Fin m) :
    HasLaw (jointAlong e) (d⊗ₘiid G k) (d⊗ₘiid G m) := by
  have hm : Measurable (fun old : Fin m → W ↦ fun i ↦ old (e i)) := Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  refine ⟨(jointAlong_measurable e).aemeasurable,?_⟩
  have H := Measure.compProd_map (μ := d) (κ := iid G m) hm
  rw [iid_map_along G e] at H
  convert H.symm using 1
  rfl

theorem jointLaw_along_hasLaw {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) {n k : ℕ} (e : Fin (k+1) ≃ Fin (n+1)) :
    HasLaw (jointAlong e) (jointLaw (K := K) nu v k) (jointLaw nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact joint_along_hasLaw
    ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)))
    (parameterizedGibbsKernel nu v) e

theorem old_test_integral_along {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) {n k : ℕ} (e : Fin (k+1) ≃ Fin (n+1))
    (Phi : (Fin K → ℝ) → (Fin (k+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun q : (Fin K → ℝ)×(Fin (k+1) → UnitSpin N) ↦ Phi q.1 q.2)) :
    (∫ q,Phi q.1.1 (fun i ↦ q.2 (e i)) ∂jointLaw nu v n)=
      ∫ q,Phi q.1.1 q.2 ∂jointLaw nu v k := by
  have HM : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (k+1) → UnitSpin N) ↦ Phi q.1.1 q.2) :=
    hPhi.comp (measurable_fst.fst.prodMk measurable_snd)
  exact (jointLaw_along_hasLaw nu hv e).integral_comp HM.aestronglyMeasurable

end
end TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaReindex
