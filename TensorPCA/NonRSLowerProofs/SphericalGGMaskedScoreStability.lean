-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGBoundedScoreWeights

/-! Amplitude-only masks retain the L1 score error measured under each amplitude's pair
law. A fixed finite polynomial family incurs no cardinality factor.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGMaskedScoreStability
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open SphericalGGJetFamily SphericalGGWeightObservable SphericalGGBoundedScoreWeights
open scoped BigOperators
noncomputable section

def maskedPhi {X V : Type*} (S : Set X) (Phi : X → V → ℝ) (x : X) (old : V) : ℝ :=
  by classical exact if x∈S then Phi x old else 0

theorem maskedPhi_measurable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    {S : Set X} (hS : MeasurableSet S) {Phi : X → V → ℝ}
    (hPhi : Measurable (fun p : X×V ↦ Phi p.1 p.2)) :
    Measurable (fun p : X×V ↦ maskedPhi S Phi p.1 p.2) := by
  exact Measurable.ite (hS.preimage measurable_fst) hPhi measurable_const

theorem maskedPhi_abs_le {X V : Type*} (S : Set X) {Phi : X → V → ℝ} {C : ℝ}
    (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C) (x : X) (old : V) : |maskedPhi S Phi x old|≤C := by
  by_cases hx : x∈S
  · simpa only [maskedPhi,if_pos hx] using hp x old
  · simpa only [maskedPhi,if_neg hx,abs_zero] using hC

theorem scoreObservable_sub_le_masked {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (psi phi : Fin (n+1) → ℝ → ℝ)
    (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j)
    {S : Set (Fin K → ℝ)} (hS : MeasurableSet S)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hb0 : ∀ x q, 0≤b x q) (hb1 : ∀ x q, b x q≤1)
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) {L : ℝ} (hL : 0≤L)
    (hLip : ∀ x y, |chi x-chi y|≤L*|x-y|) (t : ℝ) :
    |scoreObservable nu v n psi (maskedPhi S Phi) b chi t-scoreObservable nu v n phi (maskedPhi S Phi) b chi t|≤
      (2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L))*
        (∫ x, S.indicator (fun x ↦ ∑ j, pairMean nu v (fun r ↦ |psi j r-phi j r|) x) x ∂positiveCubeLaw K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let M := maskedPhi S Phi
  have hM : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ M p.1 p.2) := maskedPhi_measurable hS hPhi
  have hMb (x) (old) : |M x old|≤C := maskedPhi_abs_le S hC hp x old
  let Sp := fun x ↦ GGFiniteJointScoreStability.observable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap psi (M x) (b x) chi t
  let Sf := fun x ↦ GGFiniteJointScoreStability.observable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap phi (M x) (b x) chi t
  let A := 2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L)
  let E : (Fin K → ℝ) → ℝ := fun x ↦ ∑ j, pairMean nu v (fun r ↦ |psi j r-phi j r|) x
  have hDI (j : Fin (n+1)) : Integrable (fun x : Fin K → ℝ ↦ pairMean nu v (fun r ↦ |psi j r-phi j r|) x)
      (positiveCubeLaw K) := by
    have hDM : Measurable (fun r ↦ |psi j r-phi j r|) := by
      convert continuous_abs.measurable.comp ((hpsi j).sub (hphi j)) using 1 <;> rfl
    have hDB (r : ℝ) : |(|psi j r-phi j r|)|≤2*B j := by
      rw [abs_abs]; exact (abs_sub _ _).trans (by linarith [hpb j r,hfb j r])
    refine Integrable.of_bound (pairMean_measurable nu hv hDM hDB).aestronglyMeasurable
      (2*B j) (Eventually.of_forall (fun x ↦ ?_))
    simpa only [Real.norm_eq_abs] using pairMean_abs_le nu hv hDB x
  have hEI : Integrable E (positiveCubeLaw K) := integrable_finset_sum Finset.univ (fun j _ ↦ hDI j)
  have hSp : Integrable Sp (positiveCubeLaw K) := fixed_observable_integrable nu hv n hpsi B hpb hM hMb hbM hchiM hchi t
  have hSf : Integrable Sf (positiveCubeLaw K) := fixed_observable_integrable nu hv n hphi B hfb hM hMb hbM hchiM hchi t
  have hPoint (x : Fin K → ℝ) : |Sp x-Sf x|≤A*S.indicator E x := by
    have hpM : Measurable (M x) := by
      convert hM.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
    have hbS : Measurable (b x) := by
      convert hbM.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx]
      exact GGFiniteJointScoreStability.observable_sub_le
        (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ((parameterizedGibbsKernel nu v).sectR x)
        n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) psi phi hpsi hphi B hpb hfb hpM hC
        (hMb x) hbS (hb0 x) (hb1 x) hchiM hchi hL hLip t
    · rw [Set.indicator_of_notMem hx,mul_zero]
      have hp0 (old) : |M x old|≤0 := by simp only [M,maskedPhi,if_neg hx,abs_zero,le_refl]
      have H := GGFiniteJointScoreStability.observable_sub_le
        (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ((parameterizedGibbsKernel nu v).sectR x)
        n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) psi phi hpsi hphi B hpb hfb hpM (le_refl 0)
        hp0 hbS (hb0 x) (hb1 x) hchiM hchi hL hLip t
      simpa only [mul_zero,zero_mul] using H
  have hAbsI : Integrable (fun x ↦ |Sp x-Sf x|) (positiveCubeLaw K) := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hSp.sub hSf).norm
  have HI := integral_mono hAbsI ((hEI.indicator hS).const_mul A) hPoint
  rw [integral_const_mul] at HI
  rw [scoreObservable_eq_cube nu hv n hpsi B hpb hM hMb hbM hchiM hchi t,
    scoreObservable_eq_cube nu hv n hphi B hfb hM hMb hbM hchiM hchi t]
  change |(∫ x, Sp x ∂positiveCubeLaw K)-(∫ x, Sf x ∂positiveCubeLaw K)|≤_
  rw [← integral_sub hSp hSf]
  exact abs_integral_le_integral_abs.trans HI

theorem finite_masked_score_sum_sub_le {N K J : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (psi phi : Fin J → Fin (n+1) → ℝ → ℝ)
    (hpsi : ∀ i j, Measurable (psi i j)) (hphi : ∀ i j, Measurable (phi i j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ i j r, |psi i j r|≤B j) (hfb : ∀ i j r, |phi i j r|≤B j)
    (S : Fin J → Set (Fin K → ℝ)) (hS : ∀ i, MeasurableSet (S i))
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (b : Fin J → (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (hbM : ∀ i, Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b i p.1 p.2))
    (hb0 : ∀ i x q, 0≤b i x q) (hb1 : ∀ i x q, b i x q≤1)
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) {L : ℝ} (hL : 0≤L)
    (hLip : ∀ x y, |chi x-chi y|≤L*|x-y|) {eta : ℝ}
    (hBudget : ∀ x, (∑ i, (S i).indicator
      (fun x ↦ ∑ j, pairMean nu v (fun r ↦ |psi i j r-phi i j r|) x) x)≤eta) (t : ℝ) :
    |(∑ i, scoreObservable nu v n (psi i) (maskedPhi (S i) Phi) (b i) chi t)-
      (∑ i, scoreObservable nu v n (phi i) (maskedPhi (S i) Phi) (b i) chi t)|≤
      (2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L))*eta := by
  let A := 2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L)
  let E : Fin J → (Fin K → ℝ) → ℝ := fun i x ↦
    (S i).indicator (fun x ↦ ∑ j, pairMean nu v (fun r ↦ |psi i j r-phi i j r|) x) x
  have hA : 0≤A := by dsimp only [A]; positivity
  have hEI (i : Fin J) : Integrable (E i) (positiveCubeLaw K) := by
    apply Integrable.indicator (s := S i) _ (hS i)
    apply integrable_finset_sum Finset.univ
    intro j _
    have hDM : Measurable (fun r ↦ |psi i j r-phi i j r|) := by
      convert continuous_abs.measurable.comp ((hpsi i j).sub (hphi i j)) using 1 <;> rfl
    have hDB (r : ℝ) : |(|psi i j r-phi i j r|)|≤2*B j := by
      rw [abs_abs]; exact (abs_sub _ _).trans (by linarith [hpb i j r,hfb i j r])
    refine Integrable.of_bound (pairMean_measurable nu hv hDM hDB).aestronglyMeasurable
      (2*B j) (Eventually.of_forall (fun x ↦ ?_))
    simpa only [Real.norm_eq_abs] using pairMean_abs_le nu hv hDB x
  have hInt : (∫ x, (∑ i, E i x) ∂positiveCubeLaw K)≤eta := by
    have H := integral_mono (integrable_finset_sum Finset.univ (fun i _ ↦ hEI i))
      (integrable_const eta) hBudget
    simpa only [integral_const,probReal_univ,one_smul] using H
  calc
    _ = |∑ i, (scoreObservable nu v n (psi i) (maskedPhi (S i) Phi) (b i) chi t-
        scoreObservable nu v n (phi i) (maskedPhi (S i) Phi) (b i) chi t)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |scoreObservable nu v n (psi i) (maskedPhi (S i) Phi) (b i) chi t-
        scoreObservable nu v n (phi i) (maskedPhi (S i) Phi) (b i) chi t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, A*(∫ x, E i x ∂positiveCubeLaw K) := Finset.sum_le_sum (fun i _ ↦
      scoreObservable_sub_le_masked nu hv n (psi i) (phi i) (hpsi i) (hphi i) B (hpb i) (hfb i)
        (hS i) hPhi hC hp (hbM i) (hb0 i) (hb1 i) hchiM hchi hL hLip t)
    _ = A*(∫ x, (∑ i, E i x) ∂positiveCubeLaw K) := by
      rw [← Finset.mul_sum,integral_finsetSum Finset.univ (fun i _ ↦ hEI i)]
    _ ≤ A*eta := mul_le_mul_of_nonneg_left hInt hA

end
end TensorPCA.NonRSLowerProofs.SphericalGGMaskedScoreStability
