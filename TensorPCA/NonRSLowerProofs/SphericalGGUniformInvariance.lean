-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGInvariance

/-! A finite threshold uniform over dimensions, fixed priors and uniformly bounded old-
test families, suitable for averaging a varying-dimensional random background.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGUniformInvariance
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation SphericalGGZeroJets SphericalGGInvariance
open scoped Topology
noncomputable section

private theorem uniform_of_all_sequences {Y : Type*} (strength error : Y → ℝ)
    (hseq : ∀ y : ℕ → Y, Tendsto (fun i ↦ strength (y i)) atTop atTop →
      Tendsto (fun i ↦ error (y i)) atTop (𝓝 0)) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ y, V≤strength y → error y≤eps := by
  classical
  by_contra h
  have hbad (V : ℝ) (hV : 1≤V) : ∃ y, V≤strength y ∧ eps<error y := by
    by_contra hnone
    apply h
    refine ⟨V,hV,?_⟩
    intro y hy
    by_contra he
    exact hnone ⟨y,hy,lt_of_not_ge he⟩
  have hfloor (i : ℕ) : (1 : ℝ)≤(i : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) i; linarith
  let y : ℕ → Y := fun i ↦ Classical.choose (hbad ((i : ℝ)+1) (hfloor i))
  have hy (i : ℕ) : (i : ℝ)+1≤strength (y i) ∧ eps<error (y i) :=
    Classical.choose_spec (hbad ((i : ℝ)+1) (hfloor i))
  have hs : Tendsto (fun i ↦ strength (y i)) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨M,hM⟩ := exists_nat_gt b
    refine eventually_atTop.2 ⟨M,fun i hi ↦ ?_⟩
    have hMi : (M : ℝ) ≤ i := Nat.cast_le.mpr hi
    have hh := (hy i).1
    linarith
  obtain ⟨i,hi⟩ := ((tendsto_order.1 (hseq y hs)).2 eps heps).exists
  exact lt_asymm hi (hy i).2

/-- Proof-only dependent witnesses for a failure of uniformity. -/
private structure BoundedTrial (K n : ℕ) (C : ℝ) where
  dim : ℕ
  prior : Measure (UnitSpin dim)
  probability : IsProbabilityMeasure prior
  strength : ℝ
  positive : 0<strength
  test : (Fin K → ℝ) → (Fin (n+1) → UnitSpin dim) → ℝ
  measurable : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin dim) ↦ test p.1 p.2)
  bounded : ∀ x old, |test x old|≤C

private def trialError {K n : ℕ} {C : ℝ} (P : Fin (n+1) → Polynomial ℝ)
    (t : ℝ) (q : BoundedTrial K n C) : ℝ :=
  letI := q.probability
  ∫ x : Fin K → ℝ, |polynomialJet q.prior q.strength 0 n P q.test x t-
    polynomialJet q.prior q.strength 0 n P q.test x 0| ∂positiveCubeLaw K

theorem exists_uniform_polynomial_invariance_threshold (K n : ℕ)
    (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    {C : ℝ} (hC : 0≤C) (t : ℝ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ), V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old, |Phi x old|≤C) →
        (∫ x : Fin K → ℝ, |polynomialJet nu v 0 n P Phi x t-
          polynomialJet nu v 0 n P Phi x 0| ∂positiveCubeLaw K)≤eps := by
  have hseq : ∀ q : ℕ → BoundedTrial K n C,
      Tendsto (fun i ↦ (q i).strength) atTop atTop →
        Tendsto (fun i ↦ trialError P t (q i)) atTop (𝓝 0) := by
    intro q hq
    letI : ∀ i, IsProbabilityMeasure (q i).prior := fun i ↦ (q i).probability
    exact (polynomial_invariance_l1 (fun i ↦ (q i).dim) K n (fun i ↦ (q i).prior)
      (fun i ↦ (q i).strength) hq (fun i ↦ (q i).positive) P hPK (fun i ↦ (q i).test)
        (fun i ↦ (q i).measurable) hC (fun i ↦ (q i).bounded) t).1
  obtain ⟨V,hV,hU⟩ := uniform_of_all_sequences (fun q : BoundedTrial K n C ↦ q.strength) (trialError P t) hseq heps
  refine ⟨V,hV,?_⟩
  intro N nu _ v hv Phi hPhi hp
  let q : BoundedTrial K n C := ⟨N,nu,inferInstance,v,lt_of_lt_of_le zero_lt_one (hV.trans hv),Phi,hPhi,hp⟩
  exact hU q hv

end
end TensorPCA.NonRSLowerProofs.SphericalGGUniformInvariance
