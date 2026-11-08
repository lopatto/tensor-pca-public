-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGThresholdEquivalence
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteArrayUltrametricity
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage

/-! Finite-array threshold error is bounded by the ultrametricity error and boundary
masses under each amplitude's Gaussian-averaged pair law. Diagonal pairs contribute
zero because the lower bands exclude one.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGThresholdBadMass
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open SphericalGGThresholdFirstMomentAverage FiniteGGThresholdEquivalence
open SphericalGGFiniteArrayUltrametricity
open scoped BigOperators
noncomputable section

theorem bad_thresholds_mass_le {X I L : Type*} [MeasurableSpace X] [Fintype I] [Fintype L]
    (mu : Measure X) [IsFiniteMeasure mu] (R : X → I → I → ℝ)
    (hSelf : ∀ x i,R x i i=1) (hSym : ∀ x i j,R x i j=R x j i)
    (cuts : L → ℝ) (hCuts : ∀ l,cuts l≤1) {h : ℝ} (hh : 0<h) :
    mu.real {x | ¬∀ l,Equivalence (fun i j ↦ cuts l≤R x i j)}≤
      mu.real {x | ∃ i j k,R x i j+h≤min (R x i k) (R x j k)}+
        ∑ l,∑ i,∑ j,mu.real {x | R x i j∈Ico (cuts l-h) (cuts l)} := by
  have hUnion : {x | ∃ l i j,R x i j∈Ico (cuts l-h) (cuts l)}=
      ⋃ l,⋃ i,⋃ j,{x | R x i j∈Ico (cuts l-h) (cuts l)} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion]
  calc
    _ ≤ mu.real ({x | ∃ i j k,R x i j+h≤min (R x i k) (R x j k)}∪
        {x | ∃ l i j,R x i j∈Ico (cuts l-h) (cuts l)}) :=
      measureReal_mono (bad_thresholds_subset R hSelf hSym cuts hCuts hh)
    _ ≤ _+mu.real {x | ∃ l i j,R x i j∈Ico (cuts l-h) (cuts l)} := measureReal_union_le _ _
    _ ≤ _+∑ l,∑ i,∑ j,mu.real {x | R x i j∈Ico (cuts l-h) (cuts l)} := by
      apply add_le_add le_rfl
      rw [hUnion]
      exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun l _ ↦
        (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun i _ ↦ measureReal_iUnion_fintype_le _))))

theorem pair_set_mass_eq_cube {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (i j : Fin (n+1)) (hij : i≠j) {B : Set ℝ} (hB : MeasurableSet B) :
    (jointLaw (K := K) nu v n).real {q | unitOverlap (q.2 i) (q.2 j)∈B}=
      ∫ x,pairMean nu v (B.indicator (fun _ ↦ (1 : ℝ))) x ∂positiveCubeLaw K := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  letI := jointLaw_probability (K := K) nu hv n
  let I : ℝ → ℝ := B.indicator (fun _ ↦ (1 : ℝ))
  let Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ :=
    fun _ old ↦ I (unitOverlap (old i) (old j))
  have hI : Measurable I := measurable_const.indicator hB
  have hIb (r : ℝ) : |I r|≤1 := by dsimp only [I]; by_cases hr : r∈B <;> simp [hr]
  have hOld : Measurable (fun old : Fin (n+1) → UnitSpin N ↦ unitOverlap (old i) (old j)) := by
    have hPair : Measurable (fun old : Fin (n+1) → UnitSpin N ↦ (old i,old j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    simpa only [Function.comp_def] using (unitOverlap_measurable N).comp hPair
  have hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) :=
    (hI.comp hOld).comp measurable_snd
  have hEvent : MeasurableSet {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
      unitOverlap (q.2 i) (q.2 j)∈B} := hB.preimage (hOld.comp measurable_snd)
  have hEq : (jointLaw (K := K) nu v n).real {q | unitOverlap (q.2 i) (q.2 j)∈B}=
      ∫ q,Phi q.1.1 q.2 ∂jointLaw nu v n := by
    calc
      _ = ∫ q,({q | unitOverlap (q.2 i) (q.2 j)∈B}).indicator (fun _ ↦ (1 : ℝ)) q
          ∂jointLaw nu v n := by
        simpa only [smul_eq_mul,mul_one] using
          (integral_indicator_const (μ := jointLaw (K := K) nu v n) (1 : ℝ) hEvent).symm
      _ = _ := integral_congr_ae (Eventually.of_forall
        (fun q ↦ by
          classical
          by_cases hr : unitOverlap (q.2 i) (q.2 j)∈B <;> simp [Phi,I,hr]))
  rw [hEq,joint_old_integral_eq_cube nu hv n Phi hPhi (fun _ old ↦ hIb _)]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  have hLaw := overlap_hasLaw
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((parameterizedGibbsKernel nu v).sectR x) (unitOverlap_measurable N) i j hij
  exact hLaw.integral_comp hI.aestronglyMeasurable

theorem pair_lower_band_mass_le_cube {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (i j : Fin (n+1)) {u h : ℝ} (hu : u≤1) :
    (jointLaw (K := K) nu v n).real {q | unitOverlap (q.2 i) (q.2 j)∈Ico (u-h) u}≤
      ∫ x,pairMean nu v ((Ico (u-h) u).indicator (fun _ ↦ (1 : ℝ))) x ∂positiveCubeLaw K := by
  by_cases hij : i=j
  · subst j
    have hEmpty : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
        unitOverlap (q.2 i) (q.2 i)∈Ico (u-h) u}=∅ := by
      ext q
      have hSelf : unitOverlap (q.2 i) (q.2 i)=1 := by
        change inner ℝ (q.2 i).val (q.2 i).val=1
        rw [real_inner_self_eq_norm_sq,(q.2 i).property,one_pow]
      simp only [mem_setOf_eq,mem_Ico,hSelf,mem_empty_iff_false,iff_false,not_and]
      intro _
      exact not_lt_of_ge hu
    rw [hEmpty,measureReal_empty]
    apply integral_nonneg
    intro x
    apply integral_nonneg
    intro r
    exact indicator_nonneg (fun _ _ ↦ zero_le_one) r
  · exact le_of_eq (pair_set_mass_eq_cube nu hv n i j hij measurableSet_Ico)

theorem finite_array_threshold_mass_le {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (cuts : Fin depth → ℝ) (hCuts : ∀ l,cuts l≤1) {h : ℝ} (hh : 0<h) :
    (jointLaw (K := K) nu v n).real {q | ¬∀ l,Equivalence (fun i j ↦ cuts l≤unitOverlap (q.2 i) (q.2 j))}≤
      (jointLaw (K := K) nu v n).real {q | ∃ i j k : Fin (n+1),unitOverlap (q.2 i) (q.2 j)+h≤
        min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}+
      ((n+1 : ℕ) : ℝ)^2*∑ l,∫ x,pairMean nu v
        ((Ico (cuts l-h) (cuts l)).indicator (fun _ ↦ (1 : ℝ))) x ∂positiveCubeLaw K := by
  letI := jointLaw_probability (K := K) nu hv n
  have hSelf (q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) (i : Fin (n+1)) :
      unitOverlap (q.2 i) (q.2 i)=1 := by
    change inner ℝ (q.2 i).val (q.2 i).val=1
    rw [real_inner_self_eq_norm_sq,(q.2 i).property,one_pow]
  have hSym (q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) (i j : Fin (n+1)) :
      unitOverlap (q.2 i) (q.2 j)=unitOverlap (q.2 j) (q.2 i) := real_inner_comm _ _
  apply (bad_thresholds_mass_le (jointLaw (K := K) nu v n)
    (fun q i j ↦ unitOverlap (q.2 i) (q.2 j)) hSelf hSym cuts hCuts hh).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ l : Fin depth,∑ _i : Fin (n+1),∑ _j : Fin (n+1),∫ x,pairMean nu v
        ((Ico (cuts l-h) (cuts l)).indicator (fun _ ↦ (1 : ℝ))) x ∂positiveCubeLaw K :=
      Finset.sum_le_sum (fun l _ ↦ Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum
        (fun j _ ↦ pair_lower_band_mass_le_cube nu hv n i j (hCuts l))))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.mul_sum,← Finset.mul_sum,← mul_assoc,← pow_two]

theorem exists_uniform_threshold_mass_bound (n depth : ℕ)
    (cuts : Fin depth → ℝ) (hCuts : ∀ l,cuts l≤1)
    {h delta : ℝ} (hh : 0<h) (hdelta : 0<delta) :
    ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        (jointLaw (K := K) nu v n).real
          {q | ¬∀ l,Equivalence (fun i j ↦ cuts l≤unitOverlap (q.2 i) (q.2 j))}<
          delta+((n+1 : ℕ) : ℝ)^2*∑ l,∫ x,pairMean nu v
            ((Ico (cuts l-h) (cuts l)).indicator (fun _ ↦ (1 : ℝ))) x ∂positiveCubeLaw K := by
  obtain ⟨Q,hQ⟩ := exists_uniform_finite_array_ultrametricity_threshold n hh hdelta
  refine ⟨Q,?_⟩
  intro K hK
  obtain ⟨V,hV,hMain⟩ := hQ K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  exact (finite_array_threshold_mass_le nu hv0 n cuts hCuts hh).trans_lt
    (add_lt_add_of_lt_of_le (hMain nu v hv) (le_refl _))

end
end TensorPCA.NonRSLowerProofs.SphericalGGThresholdBadMass
