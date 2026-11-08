-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdBadMass

/-! Amplitude-only cut masks retain the exact own-amplitude pair law. The
UM bad event is counted once before the finite boundary-band union, so no
factor for the number of alternative cut vectors enters that error. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGMaskedThresholdBadMass
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteFirstJet SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open SphericalGGThresholdFirstMomentAverage FiniteGGThresholdEquivalence
open SphericalGGThresholdBadMass
open scoped BigOperators
noncomputable section

theorem masked_pair_set_mass_eq_cube {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (i j : Fin (n+1)) (hij : i≠j)
    {S : Set (Fin K → ℝ)} (hS : MeasurableSet S) {B : Set ℝ} (hB : MeasurableSet B) :
    (jointLaw (K := K) nu v n).real {q | q.1.1∈S ∧ unitOverlap (q.2 i) (q.2 j)∈B}=
      ∫ x,S.indicator (fun x ↦ pairMean nu v (B.indicator (fun _ ↦ (1 : ℝ))) x) x ∂positiveCubeLaw K := by
  classical
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  letI := jointLaw_probability (K := K) nu hv n
  let I : ℝ → ℝ := B.indicator (fun _ ↦ (1 : ℝ))
  let Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ :=
    fun x old ↦ if x∈S then I (unitOverlap (old i) (old j)) else 0
  have hI : Measurable I := measurable_const.indicator hB
  have hIb (r : ℝ) : |I r|≤1 := by dsimp only [I]; by_cases hr : r∈B <;> simp [hr]
  have hOld : Measurable (fun old : Fin (n+1) → UnitSpin N ↦ unitOverlap (old i) (old j)) := by
    have hPair : Measurable (fun old : Fin (n+1) → UnitSpin N ↦ (old i,old j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    simpa only [Function.comp_def] using (unitOverlap_measurable N).comp hPair
  have hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) :=
    Measurable.ite (hS.preimage measurable_fst) ((hI.comp hOld).comp measurable_snd) measurable_const
  have hPb (x old) : |Phi x old|≤1 := by
    dsimp only [Phi]
    split_ifs
    · exact hIb _
    · norm_num
  have hEvent : MeasurableSet {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
      q.1.1∈S ∧ unitOverlap (q.2 i) (q.2 j)∈B} :=
    (hS.preimage measurable_fst.fst).inter (hB.preimage (hOld.comp measurable_snd))
  have hEq : (jointLaw (K := K) nu v n).real {q | q.1.1∈S ∧ unitOverlap (q.2 i) (q.2 j)∈B}=
      ∫ q,Phi q.1.1 q.2 ∂jointLaw nu v n := by
    calc
      _ = ∫ q,({q | q.1.1∈S ∧ unitOverlap (q.2 i) (q.2 j)∈B}).indicator (fun _ ↦ (1 : ℝ)) q
          ∂jointLaw nu v n := by
        simpa only [smul_eq_mul,mul_one] using
          (integral_indicator_const (μ := jointLaw (K := K) nu v n) (1 : ℝ) hEvent).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun q ↦ by
        by_cases hx : q.1.1∈S <;> by_cases hr : unitOverlap (q.2 i) (q.2 j)∈B <;> simp [Phi,I,hx,hr]))
  rw [hEq,joint_old_integral_eq_cube nu hv n Phi hPhi hPb]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  by_cases hx : x∈S
  · rw [indicator_of_mem hx]
    have hLaw := overlap_hasLaw
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) (unitOverlap_measurable N) i j hij
    simpa only [Phi,if_pos hx,Function.comp_def,pairMean,I] using hLaw.integral_comp hI.aestronglyMeasurable
  · simp only [Phi,if_neg hx,integral_zero,indicator_of_notMem hx]

theorem masked_pair_lower_band_mass_le_cube {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (i j : Fin (n+1)) {S : Set (Fin K → ℝ)} (hS : MeasurableSet S)
    {u h : ℝ} (hu : u≤1) :
    (jointLaw (K := K) nu v n).real {q | q.1.1∈S ∧ unitOverlap (q.2 i) (q.2 j)∈Ico (u-h) u}≤
      ∫ x,S.indicator (fun x ↦ pairMean nu v ((Ico (u-h) u).indicator (fun _ ↦ (1 : ℝ))) x) x
        ∂positiveCubeLaw K := by
  by_cases hij : i=j
  · subst j
    have hEmpty : {q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) |
        q.1.1∈S ∧ unitOverlap (q.2 i) (q.2 i)∈Ico (u-h) u}=∅ := by
      ext q
      have hSelf : unitOverlap (q.2 i) (q.2 i)=1 := by
        change inner ℝ (q.2 i).val (q.2 i).val=1
        rw [real_inner_self_eq_norm_sq,(q.2 i).property,one_pow]
      constructor
      · intro hMem
        have H := hMem.2.2
        rw [hSelf] at H
        exact False.elim ((not_lt_of_ge hu) H)
      · exact False.elim
    rw [hEmpty,measureReal_empty]
    apply integral_nonneg
    intro x
    apply indicator_nonneg
    intro _ _
    exact integral_nonneg (fun r ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) r)
  · exact le_of_eq (masked_pair_set_mass_eq_cube nu hv n i j hij hS measurableSet_Ico)

theorem masked_bad_thresholds_subset {X I A L : Type*} (R : X → I → I → ℝ)
    (hSelf : ∀ x i,R x i i=1) (hSym : ∀ x i j,R x i j=R x j i)
    (cuts : A → L → ℝ) (hCuts : ∀ a l,cuts a l≤1) (mask : A → Set X)
    {h : ℝ} (hh : 0<h) :
    {x | ∃ a,x∈mask a ∧ ¬∀ l,Equivalence (fun i j ↦ cuts a l≤R x i j)}⊆
      {x | ∃ i j k,R x i j+h≤min (R x i k) (R x j k)}∪
      {x | ∃ a l i j,x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)} := by
  rintro x ⟨a,hMask,hBad⟩
  rcases bad_thresholds_subset R hSelf hSym (cuts a) (hCuts a) hh hBad with hUM|hBand
  · exact Or.inl hUM
  · obtain ⟨l,i,j,hBand⟩ := hBand
    exact Or.inr ⟨a,l,i,j,hMask,hBand⟩

theorem masked_bad_thresholds_mass_le_pair_sum {X I A L : Type*}
    [MeasurableSpace X] [Fintype I] [Fintype A] [Fintype L]
    (mu : Measure X) [IsFiniteMeasure mu] (R : X → I → I → ℝ)
    (hSelf : ∀ x i,R x i i=1) (hSym : ∀ x i j,R x i j=R x j i)
    (cuts : A → L → ℝ) (hCuts : ∀ a l,cuts a l≤1) (mask : A → Set X)
    {h : ℝ} (hh : 0<h) :
    mu.real {x | ∃ a,x∈mask a ∧ ¬∀ l,Equivalence (fun i j ↦ cuts a l≤R x i j)}≤
      mu.real {x | ∃ i j k,R x i j+h≤min (R x i k) (R x j k)}+
        ∑ a,∑ l,∑ i,∑ j,mu.real {x | x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)} := by
  have hUnion : {x | ∃ a l i j,x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)}=
      ⋃ a,⋃ l,⋃ i,⋃ j,{x | x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion]
  calc
    _ ≤ mu.real ({x | ∃ i j k,R x i j+h≤min (R x i k) (R x j k)}∪
        {x | ∃ a l i j,x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)}) :=
      measureReal_mono (masked_bad_thresholds_subset R hSelf hSym cuts hCuts mask hh)
    _ ≤ _+mu.real {x | ∃ a l i j,x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)} :=
      measureReal_union_le _ _
    _ ≤ _+∑ a,∑ l,∑ i,∑ j,mu.real {x | x∈mask a ∧ R x i j∈Ico (cuts a l-h) (cuts a l)} := by
      apply add_le_add le_rfl
      rw [hUnion]
      exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun a _ ↦
        (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun l _ ↦
          (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun i _ ↦ measureReal_iUnion_fintype_le _))))))

theorem finite_masked_threshold_mass_le {A : Type*} [Fintype A] {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (cuts : A → Fin depth → ℝ) (hCuts : ∀ a l,cuts a l≤1)
    (mask : A → Set (Fin K → ℝ)) (hMask : ∀ a,MeasurableSet (mask a)) {h : ℝ} (hh : 0<h) :
    (jointLaw (K := K) nu v n).real {q | ∃ a,q.1.1∈mask a ∧
      ¬∀ l,Equivalence (fun i j ↦ cuts a l≤unitOverlap (q.2 i) (q.2 j))}≤
      (jointLaw (K := K) nu v n).real {q | ∃ i j k : Fin (n+1),unitOverlap (q.2 i) (q.2 j)+h≤
        min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}+
      ((n+1 : ℕ) : ℝ)^2*∑ a,∑ l,∫ x,(mask a).indicator (fun x ↦ pairMean nu v
        ((Ico (cuts a l-h) (cuts a l)).indicator (fun _ ↦ (1 : ℝ))) x) x ∂positiveCubeLaw K := by
  letI := jointLaw_probability (K := K) nu hv n
  have hSelf (q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) (i : Fin (n+1)) :
      unitOverlap (q.2 i) (q.2 i)=1 := by
    change inner ℝ (q.2 i).val (q.2 i).val=1
    rw [real_inner_self_eq_norm_sq,(q.2 i).property,one_pow]
  have hSym (q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) (i j : Fin (n+1)) :
      unitOverlap (q.2 i) (q.2 j)=unitOverlap (q.2 j) (q.2 i) := real_inner_comm _ _
  apply (masked_bad_thresholds_mass_le_pair_sum (jointLaw (K := K) nu v n)
    (fun q i j ↦ unitOverlap (q.2 i) (q.2 j)) hSelf hSym cuts hCuts
    (fun a ↦ {q | q.1.1∈mask a}) hh).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ a : A,∑ l : Fin depth,∑ _i : Fin (n+1),∑ _j : Fin (n+1),∫ x,(mask a).indicator
        (fun x ↦ pairMean nu v ((Ico (cuts a l-h) (cuts a l)).indicator (fun _ ↦ (1 : ℝ))) x) x
          ∂positiveCubeLaw K :=
      Finset.sum_le_sum (fun a _ ↦ Finset.sum_le_sum (fun l _ ↦ Finset.sum_le_sum
        (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ masked_pair_lower_band_mass_le_cube nu hv n i j (hMask a) (hCuts a l)))))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [← mul_assoc,← pow_two]
      simp_rw [← Finset.mul_sum]

theorem masked_pair_mean_integrable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    {S : Set (Fin K → ℝ)} (hS : MeasurableSet S) {B : Set ℝ} (hB : MeasurableSet B) :
    Integrable (fun x ↦ S.indicator (fun x ↦ pairMean nu v (B.indicator (fun _ ↦ (1 : ℝ))) x) x)
      (positiveCubeLaw K) := by
  have hBound (r : ℝ) : |B.indicator (fun _ ↦ (1 : ℝ)) r|≤1 := by
    by_cases hr : r∈B <;> simp [hr]
  have hInt : Integrable (fun x : Fin K → ℝ ↦ pairMean nu v (B.indicator (fun _ ↦ (1 : ℝ))) x)
      (positiveCubeLaw K) := Integrable.of_bound
    (pairMean_measurable nu hv (measurable_const.indicator hB) hBound).aestronglyMeasurable 1
    (Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using pairMean_abs_le nu hv hBound x))
  exact hInt.indicator hS

theorem finite_masked_threshold_mass_le_of_budget {A : Type*} [Fintype A] {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (cuts : A → Fin depth → ℝ) (hCuts : ∀ a l,cuts a l≤1)
    (mask : A → Set (Fin K → ℝ)) (hMask : ∀ a,MeasurableSet (mask a)) {h eta : ℝ} (hh : 0<h)
    (hBudget : ∀ x,(∑ a,∑ l,(mask a).indicator (fun x ↦ pairMean nu v
      ((Ico (cuts a l-h) (cuts a l)).indicator (fun _ ↦ (1 : ℝ))) x) x)≤eta) :
    (jointLaw (K := K) nu v n).real {q | ∃ a,q.1.1∈mask a ∧
      ¬∀ l,Equivalence (fun i j ↦ cuts a l≤unitOverlap (q.2 i) (q.2 j))}≤
      (jointLaw (K := K) nu v n).real {q | ∃ i j k : Fin (n+1),unitOverlap (q.2 i) (q.2 j)+h≤
        min (unitOverlap (q.2 i) (q.2 k)) (unitOverlap (q.2 j) (q.2 k))}+
        ((n+1 : ℕ) : ℝ)^2*eta := by
  have hInt (a : A) (l : Fin depth) := masked_pair_mean_integrable nu hv (hMask a)
    (show MeasurableSet (Ico (cuts a l-h) (cuts a l)) from measurableSet_Ico)
  have hSum (a : A) := integrable_finset_sum Finset.univ (fun l _ ↦ hInt a l)
  have hAll := integrable_finset_sum Finset.univ (fun a _ ↦ hSum a)
  have hIntegral := integral_mono hAll (integrable_const eta) hBudget
  rw [integral_finset_sum _ (fun a _ ↦ hSum a)] at hIntegral
  simp_rw [integral_finset_sum _ (fun l _ ↦ hInt _ l)] at hIntegral
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hIntegral
  exact (finite_masked_threshold_mass_le nu hv n cuts hCuts mask hMask hh).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hIntegral (sq_nonneg _)))

end
end TensorPCA.NonRSLowerProofs.SphericalGGMaskedThresholdBadMass
