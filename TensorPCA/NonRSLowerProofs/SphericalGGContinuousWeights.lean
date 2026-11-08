-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGWeightObservable
public import TensorPCA.NonRSLowerProofs.FiniteGGContinuousMomentTransfer

/-! Uniform continuous one-weight invariance in the full-field joint model, obtained
from finitely many fresh-replica moments.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGContinuousWeights
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteReplicaWeightMoments SphericalGGJetFamily SphericalGGZeroJets
open SphericalGGPartitionMoments SphericalGGWeightObservable
open scoped BigOperators
noncomputable section

private theorem repeatedMoment_integrable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hbb : ∀ x q, |b x q|≤1) (t : ℝ) :
    Integrable (fun x ↦ partitionMoment nu v n m P Phi (fun x _ ↦ b x) x t) (positiveCubeLaw K) := by
  let L := fun x ↦ momentLift n (Phi x) m (fun _ ↦ b x)
  have hL : Measurable (fun p : (Fin K → ℝ)×(Fin (n+m+1) → UnitSpin N) ↦ L p.1 p.2) :=
    momentLift_joint_measurable n m hPhi (fun x _ ↦ b x) (fun _ ↦ hb)
  have hLb (x : Fin K → ℝ) (old : Fin (n+m+1) → UnitSpin N) : |L x old|≤C :=
    momentLift_abs_le n m hC (hp x) (fun _ ↦ b x) (fun _ ↦ hbb x) old
  have HI := polynomialJet_abs_integrable nu hv 0 (n+m) (padZero n P m) hL hC hLb t
  have HM := polynomialJet_measurable nu hv 0 (n+m) (padZero n P m) (Phi := L) hL t
  have HJ := HI.mono' HM.aestronglyMeasurable (Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs]))
  have hPhis (x : Fin K → ℝ) : Measurable (Phi x) := by
    convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hbs (x : Fin K → ℝ) : Measurable (b x) := by
    convert hb.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  simpa only [L,lifted_jet_eq_partitionMoment nu hv n m P hPhis hC hp (fun x _ ↦ b x)
    (fun x _ ↦ hbs x) (fun x _ ↦ hbb x)] using HJ

theorem exists_uniform_continuous_weight_threshold (K n : ℕ)
    (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    {C : ℝ} (hC : 0≤C) (t : ℝ) (f : C(Icc (0 : ℝ) 1,ℝ)) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ), V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old, |Phi x old|≤C) →
        ∀ b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ),
          Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2) →
          (∀ x q, 0≤b x q) → (∀ x q, b x q≤1) →
          |weightObservable nu v n P Phi b f t-weightObservable nu v n P Phi b f 0|≤eps := by
  classical
  let L0 := C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, testBounds P j))
  have hL0 : 0≤L0 := mul_nonneg hC (Real.exp_nonneg _)
  obtain ⟨D,delta,hd,hTransfer⟩ := FiniteGGContinuousMomentTransfer.exists_uniform_weighted_moment_transfer f hL0 hC heps
  have hEx (j : Fin (D+1)) := exists_uniform_partition_moment_threshold K n j.val P hPK hC t hd
  let Vj : Fin (D+1) → ℝ := fun j ↦ Classical.choose (hEx j)
  have hVj (j : Fin (D+1)) := Classical.choose_spec (hEx j)
  let V : ℝ := 1+∑ j, Vj j
  have hNon (j : Fin (D+1)) : 0≤Vj j := (by norm_num : (0 : ℝ)≤1).trans (hVj j).1
  have hV : 1≤V := by
    dsimp only [V]
    have hSum : 0≤∑ j, Vj j := Finset.sum_nonneg (fun j _ ↦ hNon j)
    linarith
  have hVjV (j : Fin (D+1)) : Vj j≤V := by
    have HH := Finset.single_le_sum (fun k _ ↦ hNon k) (Finset.mem_univ j)
    dsimp only [V]
    linarith
  refine ⟨V,hV,?_⟩
  intro N nu _ v hv Phi hPhi hp b hb hb0 hb1
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  have hbb (x : Fin K → ℝ) (q : (Fin (n+1) → UnitSpin N)×UnitSpin N) : |b x q|≤1 := by
    rw [abs_of_nonneg (hb0 x q)]; exact hb1 x q
  have hMom (m : ℕ) (hm : m≤D) :
      |(∫ p, rootFactor nu v n P Phi t p*(weightValue nu v n P b t p : ℝ)^m ∂jointLaw nu v n)-
        (∫ p, rootFactor nu v n P Phi 0 p*(weightValue nu v n P b 0 p : ℝ)^m ∂jointLaw nu v n)|≤delta := by
    let j : Fin (D+1) := ⟨m,by omega⟩
    have H := (hVj j).2 nu v ((hVjV j).trans hv) Phi hPhi hp (fun x _ ↦ b x)
      (fun _ ↦ hb) (fun x _ ↦ hbb x)
    rw [weighted_power_eq_partitionMoment nu hv0 n m P hPhi hp hb hb0 hb1 t,
      weighted_power_eq_partitionMoment nu hv0 n m P hPhi hp hb hb0 hb1 0]
    rw [← integral_sub (repeatedMoment_integrable nu hv0 n m P hPhi hC hp hb hbb t)
      (repeatedMoment_integrable nu hv0 n m P hPhi hC hp hb hbb 0)]
    exact abs_integral_le_integral_abs.trans H
  have hCap0 := rootFactor_l1_le nu hv0 n P hPhi hp t
  have hCap1 : (∫ p, |rootFactor nu v n P Phi 0 p| ∂jointLaw nu v n)≤C := by
    simpa only [abs_zero,mul_zero,zero_mul,Real.exp_zero,mul_one] using rootFactor_l1_le nu hv0 n P hPhi hp 0
  have H := hTransfer _ (jointLaw nu v n) (weightValue nu v n P b t) (weightValue nu v n P b 0)
    (weightValue_measurable nu hv0 n P hb t) (weightValue_measurable nu hv0 n P hb 0)
    (rootFactor nu v n P Phi t) (rootFactor nu v n P Phi 0)
    (rootFactor_integrable nu hv0 n P hPhi hp t) (rootFactor_integrable nu hv0 n P hPhi hp 0)
    hCap0 hCap1 hMom
  exact H.2.2

end
end TensorPCA.NonRSLowerProofs.SphericalGGContinuousWeights
