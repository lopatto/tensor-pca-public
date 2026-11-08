-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGOldEventPairMean
public import TensorPCA.NonRSLowerProofs.FiniteGGAmplitudeMassRestriction

/-! An old observable restricted by its own amplitude's disorder-averaged event mass.
The joint mass is retained, and the amplitude-conditional closed-threshold pair mean
has a pointwise gap on its support.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGOldEventMassRestriction
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGWeightObservable SphericalGGMaskedScoreStability
open SphericalGGThresholdFirstMomentAverage SphericalGGOldEventPairMean
open FiniteGGAmplitudeMassRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def restrictedPhi {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (p : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ) :
    (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ :=
  maskedPhi {x | p/2≤∫ old,Phi x old
    ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) (n+2)} Phi

theorem restrictedPhi_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (p : ℝ) (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi q.1 q.2))
    (hp : ∀ x old,0≤Phi x old ∧ Phi x old≤1) :
    Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ restrictedPhi nu v n p Phi q.1 q.2) := by
  exact maskedPhi_measurable (measurableSet_le measurable_const (old_event_mass_measurable nu hv n Phi hPhi hp)) hPhi

theorem restrictedPhi_mem_Icc {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (n : ℕ) (p : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hp : ∀ x old,0≤Phi x old ∧ Phi x old≤1) (x : Fin K → ℝ) (old : Fin (n+2) → UnitSpin N) :
    restrictedPhi nu v n p Phi x old∈Icc (0 : ℝ) 1 := by
  unfold restrictedPhi maskedPhi
  split
  · exact hp x old
  · exact ⟨le_refl 0,zero_le_one⟩

theorem restrictedPhi_ne_zero {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (n : ℕ) (p : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (x : Fin K → ℝ) (old : Fin (n+2) → UnitSpin N)
    (h : restrictedPhi nu v n p Phi x old≠0) :
    Phi x old≠0 ∧ restrictedPhi nu v n p Phi x old=Phi x old ∧
      p/2≤∫ old,Phi x old
        ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+2) := by
  unfold restrictedPhi maskedPhi at h ⊢
  split at h
  · rename_i hx
    simp only [if_pos hx]
    exact ⟨h,True.intro,hx⟩
  · exact False.elim (h rfl)

theorem restrictedPhi_preserves_support {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (n : ℕ) (p : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (A : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → Prop)
    (hSupport : ∀ x old,Phi x old≠0→A x old) :
    ∀ x old,restrictedPhi nu v n p Phi x old≠0→A x old := by
  intro x old h
  exact hSupport x old (restrictedPhi_ne_zero nu v n p Phi x old h).1

theorem restrictedPhi_own_pairMean_gap {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (p : ℝ) (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi q.1 q.2))
    (hp : ∀ x old,0≤Phi x old ∧ Phi x old≤1)
    (x : Fin K → ℝ) (old : Fin (n+2) → UnitSpin N)
    (h : restrictedPhi nu v n p Phi x old≠0) (u : ℝ)
    (hSupport : ∀ old,Phi x old≠0→unitOverlap (old (Fin.last (n+1))) (old 0)<u) :
    pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) x≤1-p/2 := by
  exact own_pairMean_le_of_old_event_mass nu hv n u p x (Phi x)
    (hPhi.comp (measurable_const.prodMk measurable_id)) (hp x) hSupport
    (restrictedPhi_ne_zero nu v n p Phi x old h).2.2

theorem restrictedPhi_joint_mass_lower {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (p : ℝ) (hp0 : 0≤p)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi q.1 q.2))
    (hp : ∀ x old,0≤Phi x old ∧ Phi x old≤1) :
    (∫ q,Phi q.1.1 q.2 ∂jointLaw nu v (n+1))-p/2≤
      ∫ q,restrictedPhi nu v n p Phi q.1.1 q.2 ∂jointLaw nu v (n+1) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let delta : (Fin K → ℝ) → ℝ := fun x ↦ ∫ old,Phi x old ∂law d ((parameterizedGibbsKernel nu v).sectR x) (n+2)
  have hDm : Measurable delta := old_event_mass_measurable nu hv n Phi hPhi hp
  have hDb (x : Fin K → ℝ) : 0≤delta x ∧ delta x≤1 := by
    refine ⟨integral_nonneg (fun old ↦ (hp x old).1),?_⟩
    have H := norm_integral_le_of_norm_le_const (μ := law d ((parameterizedGibbsKernel nu v).sectR x) (n+2))
      (f := Phi x) (C := 1) (.of_forall (fun old ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (hp x old).1]; exact (hp x old).2))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H)
  have H := (retained_amplitude_mass (positiveCubeLaw K) delta hDm hDb p hp0).2.1
  have hRM := restrictedPhi_measurable nu hv n p Phi hPhi hp
  have hpAbs (x) (old) : |Phi x old|≤1 := by rw [abs_of_nonneg (hp x old).1]; exact (hp x old).2
  have hRAbs (x) (old) : |restrictedPhi nu v n p Phi x old|≤1 := by
    rw [abs_of_nonneg (restrictedPhi_mem_Icc nu v n p Phi hp x old).1]
    exact (restrictedPhi_mem_Icc nu v n p Phi hp x old).2
  rw [joint_old_integral_eq_cube nu hv (n+1) Phi hPhi hpAbs,
    joint_old_integral_eq_cube nu hv (n+1) (restrictedPhi nu v n p Phi) hRM hRAbs]
  convert H using 1
  apply integral_congr_ae
  exact .of_forall (fun x ↦ by
    change (∫ old,(if p/2≤delta x then Phi x old else 0)
      ∂law d ((parameterizedGibbsKernel nu v).sectR x) (n+2))=
        (if p/2≤delta x then delta x else 0)
    by_cases hx : p/2≤delta x
    · simp only [if_pos hx]; rfl
    · simp only [if_neg hx,integral_zero])

theorem restrictedPhi_joint_mass_ge_half {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (p : ℝ) (hp0 : 0≤p)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi q.1 q.2))
    (hp : ∀ x old,0≤Phi x old ∧ Phi x old≤1)
    (hMass : p≤∫ q,Phi q.1.1 q.2 ∂jointLaw nu v (n+1)) :
    p/2≤∫ q,restrictedPhi nu v n p Phi q.1.1 q.2 ∂jointLaw nu v (n+1) := by
  have H := restrictedPhi_joint_mass_lower nu hv n p hp0 Phi hPhi hp
  linarith only [H,hMass]

end
end TensorPCA.NonRSLowerProofs.SphericalGGOldEventMassRestriction
