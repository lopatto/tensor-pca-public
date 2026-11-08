-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage

/-! Old-event mass controls the complementary amplitude-conditional pair mean. Strict
overlap below u is complementary to the closed threshold Ici u, including any atom
at u.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGOldEventPairMean
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGThresholdFirstMomentAverage GGFiniteFirstJet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem old_event_mass_add_own_pairMean_le_one {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (u : ℝ) (x : Fin K → ℝ)
    (Phi : (Fin (n+2) → UnitSpin N) → ℝ) (hPhi : Measurable Phi)
    (hp : ∀ old,0≤Phi old ∧ Phi old≤1)
    (hSupport : ∀ old,Phi old≠0→unitOverlap (old (Fin.last (n+1))) (old 0)<u) :
    (∫ old,Phi old ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) (n+2))+
      pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) x≤1 := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)
  let I : ℝ → ℝ := (Ici u).indicator (fun _ ↦ (1 : ℝ))
  let R : (Fin (n+2) → UnitSpin N) → ℝ := fun old ↦ unitOverlap (old (Fin.last (n+1))) (old 0)
  have hI : Measurable I := measurable_const.indicator measurableSet_Ici
  have hIb (r : ℝ) : |I r|≤1 := by dsimp only [I]; by_cases h : r∈Ici u <;> simp [h]
  have hLaw : HasLaw R rho mu := overlap_hasLaw d G
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (Fin.last (n+1)) 0 (by
      intro he; have hh := congrArg Fin.val he; simp only [Fin.val_last,Fin.val_zero] at hh; omega)
  have hRI : Integrable I rho := Integrable.of_bound hI.aestronglyMeasurable 1
    (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hIb r))
  have hPI : Integrable Phi mu := Integrable.of_bound hPhi.aestronglyMeasurable 1
    (Eventually.of_forall (fun old ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hp old).1]; exact (hp old).2))
  have hPoint (old : Fin (n+2) → UnitSpin N) : Phi old+I (R old)≤1 := by
    by_cases h : Phi old=0
    · rw [h,zero_add]; exact (le_abs_self _).trans (hIb _)
    · have hlt := hSupport old h
      have hnot : R old∉Ici u := not_le.mpr hlt
      rw [show I (R old)=0 from Set.indicator_of_notMem hnot _,add_zero]
      exact (hp old).2
  have hComp : Integrable (fun old ↦ I (R old)) mu := by
    convert hLaw.integrable_comp hRI using 1
    rfl
  have H := integral_mono (hPI.add hComp) (integrable_const (1 : ℝ)) hPoint
  simp only [Pi.add_apply,Function.comp_def] at H
  rw [integral_add hPI hComp,integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hMean : (∫ old,I (R old) ∂mu)=∫ r,I r ∂rho := hLaw.integral_comp hI.aestronglyMeasurable
  rw [hMean] at H
  exact H

theorem old_event_mass_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2))
    (hp : ∀ x old,0≤Phi x old ∧ Phi x old≤1) :
    Measurable (fun x ↦ ∫ old,Phi x old
      ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+2)) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact parameterized_law_integral_measurable _ _ (n+2) Phi hPhi
    (by intro x old; rw [abs_of_nonneg (hp x old).1]; exact (hp x old).2)

theorem own_pairMean_le_of_old_event_mass {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (u p : ℝ) (x : Fin K → ℝ)
    (Phi : (Fin (n+2) → UnitSpin N) → ℝ) (hPhi : Measurable Phi)
    (hp : ∀ old,0≤Phi old ∧ Phi old≤1)
    (hSupport : ∀ old,Phi old≠0→unitOverlap (old (Fin.last (n+1))) (old 0)<u)
    (hMass : p/2≤∫ old,Phi old
      ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+2)) :
    pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) x≤1-p/2 := by
  have H := old_event_mass_add_own_pairMean_le_one nu hv n u x Phi hPhi hp hSupport
  linarith only [H,hMass]

end
end TensorPCA.NonRSLowerProofs.SphericalGGOldEventPairMean
