-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdBadMass
public import TensorPCA.NonRSLowerProofs.SphericalLargeCutoffPositivity

/-! The same-cutoff pair positivity theorem controls the full finite-array negative-
overlap event. Amplitude/Gaussian averaging and diagonal exclusions are explicit.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteArrayPositivity
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianGGEnsemble
open SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open SphericalGGThresholdBadMass SphericalLargeCutoffPositivity
open scoped BigOperators
noncomputable section

theorem cube_pairMean_eq_perturbed_mass {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ x,pairMean nu v (B.indicator (fun _ ↦ (1 : ℝ))) x ∂positiveCubeLaw K)=
      (perturbedOverlapLaw (K := K) nu v).real B := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  rw [perturbedOverlapLaw_mass_eq_gibbs_pair_integral nu hv B hB]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  rw [pairMean,integral_indicator_const (1 : ℝ) hB,smul_eq_mul,mul_one,
    map_measureReal_apply (unitOverlap_measurable N) hB,
    kernel_real_mean _ _ _ (hB.preimage (unitOverlap_measurable N))]
  apply integral_congr_ae
  refine Eventually.of_forall (fun w ↦ ?_)
  dsimp only
  rw [Kernel.prod_apply,Kernel.sectR_apply,parameterizedGibbsKernel_apply nu hv]
  rfl

theorem pair_negative_mass_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (i j : Fin (n+1)) {neg : ℝ} (hNeg : 0<neg) :
    (jointLaw (K := K) nu v n).real {q | unitOverlap (q.2 i) (q.2 j)≤-neg}≤
      (perturbedOverlapLaw (K := K) nu v).real (Iic (-neg)) := by
  by_cases hij : i=j
  · subst j
    have hEmpty : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
        unitOverlap (q.2 i) (q.2 i)≤-neg}=∅ := by
      ext q
      have hSelf : unitOverlap (q.2 i) (q.2 i)=1 := by
        change inner ℝ (q.2 i).val (q.2 i).val=1
        rw [real_inner_self_eq_norm_sq,(q.2 i).property,one_pow]
      simp only [mem_setOf_eq,hSelf,mem_empty_iff_false,iff_false]
      linarith only [hNeg]
    rw [hEmpty,measureReal_empty]
    exact measureReal_nonneg
  · exact le_of_eq ((pair_set_mass_eq_cube nu hv n i j hij measurableSet_Iic).trans
      (cube_pairMean_eq_perturbed_mass nu hv measurableSet_Iic))

theorem finite_array_negative_mass_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) {neg : ℝ} (hNeg : 0<neg) :
    (jointLaw (K := K) nu v n).real {q | ∃ i j : Fin (n+1),unitOverlap (q.2 i) (q.2 j)≤-neg}≤
      ((n+1 : ℕ) : ℝ)^2*(perturbedOverlapLaw (K := K) nu v).real (Iic (-neg)) := by
  let mu := jointLaw (K := K) nu v n
  let E := fun i j : Fin (n+1) ↦ {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
    unitOverlap (q.2 i) (q.2 j)≤-neg}
  have hUnion : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
      ∃ i j : Fin (n+1),unitOverlap (q.2 i) (q.2 j)≤-neg}=⋃ i,⋃ j,E i j := by
    ext q
    simp only [E,mem_setOf_eq,mem_iUnion]
  rw [hUnion]
  calc
    _ ≤ ∑ i,mu.real (⋃ j,E i j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i,∑ j,mu.real (E i j) := Finset.sum_le_sum (fun i _ ↦ measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _i : Fin (n+1),∑ _j : Fin (n+1),(perturbedOverlapLaw (K := K) nu v).real (Iic (-neg)) :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ pair_negative_mass_le nu hv n i j hNeg))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem exists_uniform_finite_array_positivity_threshold (n : ℕ)
    {neg delta : ℝ} (hNeg : 0<neg) (hNeg1 : neg≤1) (hDelta : 0<delta) :
    ∃ Q : ℕ,∃ V : ℝ,1≤V ∧ ∀ K : ℕ,Q≤K →
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        (jointLaw (K := K) nu v n).real
          {q | ∃ i j : Fin (n+1),unitOverlap (q.2 i) (q.2 j)≤-neg}≤delta := by
  let C : ℝ := ((n+1 : ℕ) : ℝ)^2
  have hC : 0<C := by dsimp only [C]; positivity
  obtain ⟨Q,V,_,hV,hPos⟩ := exists_uniform_largeCutoff_perturbation_positivity
    hNeg hNeg1 (div_pos hDelta hC)
  refine ⟨Q,V,hV,?_⟩
  intro K hK N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  calc
    _ ≤ C*(perturbedOverlapLaw (K := K) nu v).real (Iic (-neg)) :=
      finite_array_negative_mass_le nu hv0 n hNeg
    _ ≤ C*(delta/C) := mul_le_mul_of_nonneg_left (hPos hK nu v hv) hC.le
    _ = delta := by field_simp

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteArrayPositivity
