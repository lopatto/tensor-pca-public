-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMoment
public import TensorPCA.NonRSLowerProofs.SphericalGGIndicatorTilt

/-! Joint-law and amplitude-average forms of the threshold first moment, using the
conditional spin and Gaussian laws.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteFirstJet GGFiniteReplicaSnocIntegration
open SphericalGGJetFamily SphericalGGThresholdWeights SphericalGGIndicatorTilt
open SphericalGGWeightObservable SphericalGGMaskedScoreStability
open SphericalPolynomialFirstJetClippedBudget SphericalPolynomialFirstJetCubeMean
open SphericalGGThresholdFirstMoment FiniteGGBoundaryBands
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integral_law_eq_nested {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ s,|f s|≤C) :
    (∫ s,f s ∂law d G n)=∫ w,(∫ s,f s ∂Measure.pi (fun _ : Fin n ↦ G w)) ∂d := by
  have hi : Integrable f (law d G n) := Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hb s))
  unfold law at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  simp only [Kernel.const_apply,iid_apply]

theorem fixed_amplitude_membership_integral {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (u : ℝ) (x : Fin K → ℝ)
    (Phi : (Fin (n+1) → UnitSpin N) → ℝ) (hPhi : Measurable Phi) (hp : ∀ old,|Phi old|≤1) :
    (∫ s,Phi (initial s)*(Ici u).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
      ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+2))=
      ∫ w,(∫ old,Phi old*membershipMass nu v n u ((x,w),old)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ parameterizedGibbsKernel nu v (x,w)))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let G := (parameterizedGibbsKernel nu v).sectR x
  let f : (Fin (n+2) → UnitSpin N) → ℝ := fun s ↦ Phi (initial s)*(Ici u).indicator (fun _ ↦ (1 : ℝ))
    (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
  have hI : Measurable ((Ici u).indicator (fun _ : ℝ ↦ (1 : ℝ))) := measurable_const.indicator measurableSet_Ici
  have hPair : Measurable (fun s : Fin (n+2) → UnitSpin N ↦
      (s (Fin.last n).castSucc,s (Fin.last (n+1)))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hR : Measurable (fun s : Fin (n+2) → UnitSpin N ↦
      unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1)))) := by
    simpa only [Function.comp_def] using (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair
  have hf : Measurable f := (hPhi.comp (initial_measurable _)).mul (hI.comp hR)
  have hIb (r : ℝ) : |(Ici u).indicator (fun _ ↦ (1 : ℝ)) r|≤1 := by
    by_cases hr : r∈Ici u <;> simp [hr]
  have hfb (s) : |f s|≤1 := by
    dsimp only [f]; rw [abs_mul]
    exact (mul_le_mul (hp _) (hIb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [integral_law_eq_nested _ G (n+2) f hf hfb]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w ↦ by
    dsimp only
    rw [integral_pi_snoc (G w) n f hf hfb]
    apply integral_congr_ae
    exact Eventually.of_forall (fun old ↦ by
      dsimp only
      unfold membershipMass
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z ↦ by
        have hs : initial (Fin.snoc old z)=old := by funext i; simp [initial]
        simp only [f,hs,Fin.snoc_castSucc,Fin.snoc_last,thresholdMembership]
        congr 2
        exact (real_inner_comm (old (Fin.last n)).val z.val).symm)))

theorem parameterized_law_integral_measurable {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel (X×Ω) V) [IsMarkovKernel G]
    (n : ℕ) (F : X → (Fin n → V) → ℝ)
    (hF : Measurable (fun p : X×(Fin n → V) ↦ F p.1 p.2)) {C : ℝ}
    (hb : ∀ x s,|F x s|≤C) :
    Measurable (fun x ↦ ∫ s,F x s ∂law d (G.sectR x) n) := by
  have H : Measurable (fun p : X×Ω ↦ ∫ s,F p.1 s ∂iid G n p) := by
    convert ((hF.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable.integral_kernel_prod_right'
      (κ := iid G n)).measurable using 1 <;> rfl
  have H' := H.stronglyMeasurable.integral_prod_right' (ν := d)
  convert H'.measurable using 1
  funext x
  rw [integral_law_eq_nested d (G.sectR x) n (F x)
    (hF.comp (measurable_const.prodMk measurable_id)) (hb x)]
  simp only [iid_apply,Kernel.sectR_apply]

theorem joint_membership_integral_eq_cube {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (u : ℝ) (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    (hp : ∀ x old,|Phi x old|≤1) :
    (∫ p,Phi p.1.1 p.2*membershipMass nu v n u p ∂jointLaw nu v n)=
      ∫ x,(∫ s,Phi x (initial s)*(Ici u).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
        ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+2)) ∂positiveCubeLaw K := by
  letI := jointLaw_probability (K := K) nu hv n
  have hM : Measurable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) ↦
      Phi p.1.1 p.2*membershipMass nu v n u p) :=
    (hPhi.comp (measurable_fst.fst.prodMk measurable_snd)).mul (membershipMass_measurable nu hv n u)
  have hI : Integrable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) ↦
      Phi p.1.1 p.2*membershipMass nu v n u p) (jointLaw nu v n) := by
    apply Integrable.of_bound hM.aestronglyMeasurable 1
    refine Eventually.of_forall (fun p ↦ ?_)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (membershipMass_mem nu hv n u p).1]
    exact (mul_le_mul (hp _ _) (membershipMass_mem nu hv n u p).2 (membershipMass_mem nu hv n u p).1 zero_le_one).trans_eq (one_mul _)
  rw [integral_jointLaw_eq nu hv n hM hI]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ (fixed_amplitude_membership_integral nu hv n u x (Phi x)
    (hPhi.comp (measurable_const.prodMk measurable_id)) (hp x)).symm)

theorem joint_old_integral_eq_cube {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n : ℕ) (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    (hp : ∀ x old,|Phi x old|≤1) :
    (∫ p,Phi p.1.1 p.2 ∂jointLaw nu v n)=
      ∫ x,(∫ old,Phi x old ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) (n+1)) ∂positiveCubeLaw K := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  letI := jointLaw_probability (K := K) nu hv n
  have hM : Measurable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) ↦
      Phi p.1.1 p.2) := hPhi.comp (measurable_fst.fst.prodMk measurable_snd)
  have hI : Integrable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N) ↦
      Phi p.1.1 p.2) (jointLaw nu v n) := Integrable.of_bound hM.aestronglyMeasurable 1
    (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hp p.1.1 p.2))
  rw [integral_jointLaw_eq nu hv n hM hI]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by
    simpa only [Kernel.sectR_apply] using (integral_law_eq_nested
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) (n+1) (Phi x)
      (hPhi.comp (measurable_const.prodMk measurable_id)) (hp x)).symm)

end
end TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage
