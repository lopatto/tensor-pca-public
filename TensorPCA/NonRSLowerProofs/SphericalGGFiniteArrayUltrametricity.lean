-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaSubarray
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteUltrametricity

/-! Finite-array ultrametricity from the designated-triple bound. Distinct triples have
the exact full-state three-replica law. Repeated indices cannot violate the
positive-gap inequality on unit spins.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteArrayUltrametricity
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalGGWeightObservable
open GGFiniteJointReplicaSubarray SphericalGGFiniteUltrametricity
open scoped BigOperators
noncomputable section

theorem bad_triple_distinct {N r : ℕ} (old : Fin r → UnitSpin N) {gap : ℝ} (hgap : 0<gap)
    (i j k : Fin r) (hBad : unitOverlap (old i) (old j)+gap≤
      min (unitOverlap (old i) (old k)) (unitOverlap (old j) (old k))) :
    i≠j ∧ i≠k ∧ j≠k := by
  have hSelf (z : UnitSpin N) : unitOverlap z z=1 := by
    change inner ℝ z.val z.val=1
    rw [real_inner_self_eq_norm_sq,z.property,one_pow]
  refine ⟨?_,?_,?_⟩
  · intro hij
    subst j
    have H := (le_min_iff.mp hBad).1
    rw [hSelf] at H
    have hUpper := (unitOverlap_mem_Icc (old i) (old k)).2
    linarith only [H,hUpper,hgap]
  · intro hik
    subst k
    have H := (le_min_iff.mp hBad).2
    have hSym : unitOverlap (old j) (old i)=unitOverlap (old i) (old j) :=
      real_inner_comm (old i).val (old j).val
    rw [hSym] at H
    linarith only [H,hgap]
  · intro hjk
    subst k
    have H := (le_min_iff.mp hBad).1
    linarith only [H,hgap]

theorem triple_coordinate_mass_le_designated {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) {gap : ℝ} (hgap : 0<gap) (i j k : Fin (n+1)) :
    (jointLaw (K := K) nu v n).real {q | unitOverlap (q.2 i) (q.2 j)+gap≤
      min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}≤
    (jointLaw (K := K) nu v 2).real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
      min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))} := by
  classical
  by_cases hDistinct : i≠j ∧ i≠k ∧ j≠k
  · let f : Fin 3 → Fin (n+1) := Fin.cons i (Fin.cons j (fun _ : Fin 1 ↦ k))
    have hConst : Function.Injective (fun _ : Fin 1 ↦ k) := fun a b _ ↦ Subsingleton.elim a b
    have hTail : Function.Injective (Fin.cons j (fun _ : Fin 1 ↦ k) : Fin 2 → Fin (n+1)) :=
      Fin.cons_injective_of_injective (by rintro ⟨l,hl⟩; exact hDistinct.2.2 hl.symm) hConst
    have hHead : i∉Set.range (Fin.cons j (fun _ : Fin 1 ↦ k) : Fin 2 → Fin (n+1)) := by
      rintro ⟨l,hl⟩
      cases l using Fin.cases with
      | zero => exact hDistinct.1 (by simpa only [Fin.cons_zero] using hl.symm)
      | succ l => exact hDistinct.2.1 (by simpa only [Fin.cons_succ] using hl.symm)
    have hf : Function.Injective f := Fin.cons_injective_of_injective hHead hTail
    let e : Fin 3 ↪ Fin (n+1) := ⟨f,hf⟩
    have hR (a b : Fin 3) : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) ↦
        unitOverlap (q.2 a) (q.2 b)) := by
      have hPair : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) ↦
          (q.2 a,q.2 b)) := ((measurable_pi_apply a).comp measurable_snd).prodMk ((measurable_pi_apply b).comp measurable_snd)
      simpa only [Function.comp_def] using (unitOverlap_measurable N).comp hPair
    have hBad : MeasurableSet {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin 3 → UnitSpin N) |
        unitOverlap (q.2 0) (q.2 1)+gap≤min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))} :=
      measurableSet_le ((hR 0 1).add_const gap) ((hR 0 2).min (hR 1 2))
    have H := (jointLaw_subarray_hasLaw (K := K) nu hv e).measureReal_eq hBad
    have he0 : e 0=i := rfl
    have he1 : e 1=j := rfl
    have he2 : e 2=k := rfl
    apply le_of_eq
    simpa only [jointSubarray,he0,he1,he2] using H
  · have hEmpty : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
        unitOverlap (q.2 i) (q.2 j)+gap≤min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}=∅ := by
      ext q
      constructor
      · intro h; exact False.elim (hDistinct (bad_triple_distinct q.2 hgap i j k h))
      · intro h; exact False.elim h
    rw [hEmpty,measureReal_empty]
    exact measureReal_nonneg

theorem finite_array_bad_mass_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) {gap : ℝ} (hgap : 0<gap) :
    (jointLaw (K := K) nu v n).real {q | ∃ i j k : Fin (n+1),unitOverlap (q.2 i) (q.2 j)+gap≤
      min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}≤
    ((n+1 : ℕ) : ℝ)^3*(jointLaw (K := K) nu v 2).real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
      min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))} := by
  let mu := jointLaw (K := K) nu v n
  let E := fun i j k : Fin (n+1) ↦ {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
    unitOverlap (q.2 i) (q.2 j)+gap≤min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}
  let d := (jointLaw (K := K) nu v 2).real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
    min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))}
  have hEq : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
      ∃ i j k : Fin (n+1),unitOverlap (q.2 i) (q.2 j)+gap≤
        min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}=⋃ i,⋃ j,⋃ k,E i j k := by
    ext q
    simp only [E,Set.mem_setOf_eq,Set.mem_iUnion]
  rw [hEq]
  calc
    _ ≤ ∑ i,mu.real (⋃ j,⋃ k,E i j k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i,∑ j,mu.real (⋃ k,E i j k) := Finset.sum_le_sum (fun i _ ↦ measureReal_iUnion_fintype_le _)
    _ ≤ ∑ i,∑ j,∑ k,mu.real (E i j k) := Finset.sum_le_sum (fun i _ ↦
      Finset.sum_le_sum (fun j _ ↦ measureReal_iUnion_fintype_le _))
    _ ≤ ∑ _i : Fin (n+1),∑ _j : Fin (n+1),∑ _k : Fin (n+1),d := Finset.sum_le_sum (fun i _ ↦
      Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun k _ ↦ triple_coordinate_mass_le_designated nu hv n hgap i j k)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem exists_uniform_finite_array_ultrametricity_threshold (n : ℕ)
    {gap delta : ℝ} (hgap : 0<gap) (hdelta : 0<delta) :
    ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        (jointLaw (K := K) nu v n).real {q | ∃ i j k : Fin (n+1),unitOverlap (q.2 i) (q.2 j)+gap≤
          min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}<delta := by
  let C : ℝ := ((n+1 : ℕ) : ℝ)^3
  have hC : 0<C := by dsimp only [C]; positivity
  obtain ⟨Q,hMain⟩ := exists_uniform_bad_triple_threshold hgap (div_pos hdelta hC)
  refine ⟨Q,?_⟩
  intro K hK
  obtain ⟨V,hV,hTriple⟩ := hMain K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  calc
    _ ≤ C*(jointLaw (K := K) nu v 2).real {q | unitOverlap (q.2 0) (q.2 1)+gap≤
        min (unitOverlap (q.2 0) (q.2 2)) (unitOverlap (q.2 1) (q.2 2))} := finite_array_bad_mass_le nu hv0 n hgap
    _ < C*(delta/C) := mul_lt_mul_of_pos_left (hTriple nu v hv) hC
    _ = delta := by field_simp

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteArrayUltrametricity
