-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGMaskedScoreStability

/-! Finite fixed-score weight invariance from prechosen polynomial scores.
Only the old observable is restricted by amplitude-dependent masks. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteScoreInvariance
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGZeroJets SphericalGGWeightObservable
open SphericalGGBoundedScoreWeights SphericalGGMaskedScoreStability
open scoped BigOperators
noncomputable section

 theorem exists_uniform_finite_score_weight_threshold (K n J : ℕ) (hJ : 0<J)
    (P : Fin J → Fin (n+1) → Polynomial ℝ) (hPK : ∀ i j, (P i j).natDegree≤K)
    (psi : Fin J → Fin (n+1) → ℝ → ℝ) (hpsi : ∀ i j, Measurable (psi i j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ i j r, |psi i j r|≤B j)
    (hPolyB : ∀ i j r, |tests (P i) j r|≤B j)
    {C : ℝ} (hC : 0≤C) (t : ℝ) (f : C(Icc (0 : ℝ) 1,ℝ))
    (chi : ℝ → ℝ) (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1)
    (hc : ∀ z : Icc (0 : ℝ) 1,chi z=f z) {L : ℝ} (hL : 0≤L)
    (hLip : ∀ x y, |chi x-chi y|≤L*|x-y|) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ), V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old, |Phi x old|≤C) →
        ∀ S : Fin J → Set (Fin K → ℝ), (∀ i, MeasurableSet (S i)) →
        ∀ b : Fin J → (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ),
          (∀ i, Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b i p.1 p.2)) →
          (∀ i x q, 0≤b i x q) → (∀ i x q, b i x q≤1) →
          ∀ eta : ℝ, (∀ x, (∑ i, (S i).indicator
            (fun x ↦ ∑ j, pairMean nu v (fun r ↦ |psi i j r-tests (P i) j r|) x) x)≤eta) →
            |(∑ i, scoreObservable nu v n (psi i) (maskedPhi (S i) Phi) (b i) chi t)-
              (∑ i, scoreObservable nu v n (psi i) (maskedPhi (S i) Phi) (b i) chi 0)|≤
              eps+(2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L))*eta := by
  classical
  have hJR : 0<(J : ℝ) := Nat.cast_pos.mpr hJ
  have hSmall : 0<eps/(J : ℝ) := div_pos heps hJR
  have hEx (i : Fin J) := SphericalGGContinuousWeights.exists_uniform_continuous_weight_threshold
    K n (P i) (hPK i) hC t f hSmall
  let Vj : Fin J → ℝ := fun i ↦ Classical.choose (hEx i)
  have hVj (i : Fin J) := Classical.choose_spec (hEx i)
  let V : ℝ := 1+∑ i, Vj i
  have hNon (i : Fin J) : 0≤Vj i := (by norm_num : (0 : ℝ)≤1).trans (hVj i).1
  have hV : 1≤V := by dsimp only [V]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hNon i))
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhi hp S hS b hbM hb0 hb1 eta hBudget
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  let Q := fun i ↦ tests (P i)
  let I := fun s : ℝ ↦ ∑ i, scoreObservable nu v n (psi i) (maskedPhi (S i) Phi) (b i) chi s
  let W := fun s : ℝ ↦ ∑ i, scoreObservable nu v n (Q i) (maskedPhi (S i) Phi) (b i) chi s
  have hPoly (i : Fin J) :
      |scoreObservable nu v n (Q i) (maskedPhi (S i) Phi) (b i) chi t-
        scoreObservable nu v n (Q i) (maskedPhi (S i) Phi) (b i) chi 0|≤eps/(J : ℝ) := by
    have hVi : Vj i≤v := by
      have HH : Vj i≤∑ j, Vj j := Finset.single_le_sum (fun j _ ↦ hNon j) (Finset.mem_univ i)
      exact (HH.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ)≤1))).trans hv
    rw [polynomial_scoreObservable_eq nu hv0 n (P i) _ (hbM i) (hb0 i) (hb1 i) f chi hc t,
      polynomial_scoreObservable_eq nu hv0 n (P i) _ (hbM i) (hb0 i) (hb1 i) f chi hc 0]
    exact (hVj i).2 nu v hVi (maskedPhi (S i) Phi) (maskedPhi_measurable (hS i) hPhi)
      (fun x old ↦ maskedPhi_abs_le (S i) hC hp x old) (b i) (hbM i) (hb0 i) (hb1 i)
  have hW : |W t-W 0|≤eps := by
    dsimp only [W]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |scoreObservable nu v n (Q i) (maskedPhi (S i) Phi) (b i) chi t-
          scoreObservable nu v n (Q i) (maskedPhi (S i) Phi) (b i) chi 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin J, eps/(J : ℝ) := Finset.sum_le_sum (fun i _ ↦ hPoly i)
      _ = eps := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
  have hStab := finite_masked_score_sum_sub_le nu hv0 n psi Q hpsi
    (fun i ↦ tests_measurable (P i)) B hpb hPolyB S hS hPhi hC hp b hbM hb0 hb1 hchiM hchi hL hLip hBudget t
  have hZero := finite_masked_score_sum_sub_le nu hv0 n psi Q hpsi
    (fun i ↦ tests_measurable (P i)) B hpb hPolyB S hS hPhi hC hp b hbM hb0 hb1 hchiM hchi hL hLip hBudget 0
  have hZ : I 0=W 0 := by
    have HH : |I 0-W 0|≤0 := by simpa only [abs_zero,mul_zero,zero_mul] using hZero
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm HH (abs_nonneg _)))
  change |I t-I 0|≤_
  rw [hZ]
  calc
    _ ≤ |I t-W t|+|W t-W 0| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hStab hW).trans_eq (by ring)

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteScoreInvariance
