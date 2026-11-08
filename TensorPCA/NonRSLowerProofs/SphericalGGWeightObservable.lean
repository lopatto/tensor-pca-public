-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGPartitionMoments

/-! The joint amplitude/disorder/old-replica probability model for a univariate
continuous partition-weight observable.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGWeightObservable
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open GGFiniteFirstJet GGFiniteReweightingDerivative GGFiniteParameterizedJets
open GGFiniteReplicaWeightMoments SphericalGGJetFamily SphericalGGZeroJets SphericalGGPartitionMoments
open scoped BigOperators
noncomputable section

theorem parameterized_tiltedWeightMean_measurable {Ω V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {b : Ω → (((Fin (n+1) → V)×V) → ℝ)}
    (hb : Measurable (fun p : Ω×((Fin (n+1) → V)×V) ↦ b p.1 p.2)) (t : ℝ) :
    Measurable (fun p : Ω×(Fin (n+1) → V) ↦ tiltedWeightMean n G overlap psi (b p.1) t p.1 p.2) := by
  let P := Ω×(Fin (n+1) → V)
  let kap : Kernel P V := G.comap Prod.fst measurable_fst
  have hS : Measurable (fun p : P×V ↦ score n overlap psi p.1.2 p.2) :=
    (score_joint_measurable n hR hpsi).comp (measurable_fst.snd.prodMk measurable_snd)
  have hb' : Measurable (fun p : P×V ↦ b p.1.1 (p.1.2,p.2)) :=
    hb.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hNum : Measurable (fun p : P ↦ ∫ z, b p.1 (p.2,z)*Real.exp (t*score n overlap psi p.2 z) ∂G p.1) := by
    simpa only [kap,Kernel.comap_apply,Pi.mul_apply,Function.comp_def] using
      ((hb'.mul (hS.const_mul t).exp).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable
  have hZ : Measurable (fun p : P ↦ reweightingNormalizer n G overlap psi t p.1 p.2) :=
    (normalizer_joint_measurable G n hR hpsi).1.comp (measurable_const.prodMk measurable_id)
  convert hNum.div hZ using 1
  funext p
  exact integral_div _ _

def jointLaw {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (n : ℕ) :
    Measure (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :=
  ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))) ⊗ₘ
    iid (parameterizedGibbsKernel nu v) (n+1)

theorem jointLaw_probability {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) : IsProbabilityMeasure (jointLaw (K := K) nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  unfold jointLaw
  infer_instance

def rootFactor {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) : ℝ :=
  Phi p.1.1 p.2*Real.exp (t*(∑ l, correctedScore n unitOverlap (tests P)
    (fun j ↦ pairMean nu v (tests P j) p.1.1) p.2 l))/
      (reweightingNormalizer n (parameterizedGibbsKernel nu v) unitOverlap (tests P) t p.1 p.2)^(n+1)

def meanValue {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) : ℝ :=
  tiltedWeightMean n (parameterizedGibbsKernel nu v) unitOverlap (tests P) (b p.1.1) t p.1 p.2

def weightValue {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) : Icc (0 : ℝ) 1 :=
  projIcc 0 1 (by norm_num) (meanValue nu v n P b t p)

def weightObservable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (f : C(Icc (0 : ℝ) 1,ℝ)) (t : ℝ) : ℝ :=
  ∫ p, rootFactor nu v n P Phi t p*f (weightValue nu v n P b t p) ∂jointLaw nu v n

theorem rootFactor_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) (t : ℝ) :
    Measurable (rootFactor nu v n P Phi t) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  convert parameterized_weight_measurable (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (tests_measurable P)
      (fun j ↦ pairMean_measurable nu hv (tests_measurable P j) (tests_bound P j)) hPhi
      (t := fun _ ↦ t) measurable_const using 1
  rfl

theorem rootFactor_abs_le {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ} {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    |rootFactor nu v n P Phi t p|≤C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, testBounds P j)) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact GGFiniteReweightingPadding.weight_abs_le (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (tests_measurable P)
      (fun j ↦ pairMean nu v (tests P j) p.1.1) (testBounds P) (tests_bound P)
        (fun j ↦ pairMean_abs_le nu hv (tests_bound P j) p.1.1) (hp p.1.1) t p.1 p.2

theorem rootFactor_integrable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hp : ∀ x old, |Phi x old|≤C) (t : ℝ) :
    Integrable (rootFactor nu v n P Phi t) (jointLaw nu v n) := by
  letI := jointLaw_probability nu hv n (K := K)
  exact Integrable.of_bound (rootFactor_measurable nu hv n P hPhi t).aestronglyMeasurable
    (C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, testBounds P j)))
    (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using rootFactor_abs_le nu hv n P hp t p))

theorem rootFactor_l1_le {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hp : ∀ x old, |Phi x old|≤C) (t : ℝ) :
    (∫ p, |rootFactor nu v n P Phi t p| ∂jointLaw nu v n)≤
      C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, testBounds P j)) := by
  letI := jointLaw_probability nu hv n (K := K)
  have H := integral_mono_ae (rootFactor_integrable nu hv n P hPhi hp t).norm (integrable_const _)
    (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using rootFactor_abs_le nu hv n P hp t p))
  simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using H

theorem meanValue_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2)) (t : ℝ) :
    Measurable (meanValue nu v n P b t) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hbState : Measurable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×
      ((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1.1 p.2) := by
    convert hb.comp (measurable_fst.fst.prodMk measurable_snd) using 1 <;> rfl
  exact parameterized_tiltedWeightMean_measurable (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (tests_measurable P)
      (b := fun p ↦ b p.1) hbState t

theorem weightValue_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2)) (t : ℝ) :
    Measurable (weightValue nu v n P b t) :=
  continuous_projIcc.measurable.comp (meanValue_measurable nu hv n P hb t)

theorem meanValue_mem_unit {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hb0 : ∀ x p, 0≤b x p) (hb1 : ∀ x p, b x p≤1) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    meanValue nu v n P b t p ∈ Icc (0 : ℝ) 1 := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hbM : Measurable (b p.1.1) := by
    convert hb.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hbb (q : ((Fin (n+1) → UnitSpin N)×UnitSpin N)) : |b p.1.1 q|≤1 := by
    rw [abs_of_nonneg (hb0 _ _)]; exact hb1 _ _
  refine ⟨tiltedWeightMean_nonneg (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (tests_measurable P) (testBounds P)
      (tests_bound P) (hb0 p.1.1) t p.1 p.2,?_⟩
  exact (le_abs_self _).trans (tiltedWeightMean_abs_le (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (tests_measurable P) (testBounds P)
      (tests_bound P) hbM hbb t p.1 p.2)

theorem weightValue_coe_eq_meanValue {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hb0 : ∀ x p, 0≤b x p) (hb1 : ∀ x p, b x p≤1) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    (weightValue nu v n P b t p : ℝ)=meanValue nu v n P b t p := by
  unfold weightValue
  rw [projIcc_of_mem _ (meanValue_mem_unit nu hv n P hb hb0 hb1 t p)]

theorem weighted_power_integrable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2)) (t : ℝ) (m : ℕ) :
    Integrable (fun p ↦ rootFactor nu v n P Phi t p*(weightValue nu v n P b t p : ℝ)^m) (jointLaw nu v n) := by
  have hM := (measurable_subtype_coe.comp (weightValue_measurable nu hv n P hb t)).pow_const m
  have H := (rootFactor_integrable nu hv n P hPhi hp t).bdd_mul hM.aestronglyMeasurable
    (c := 1) (Eventually.of_forall (fun p ↦ by
      simp only [Function.comp_def]
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg (weightValue nu v n P b t p).property.1]
      exact pow_le_one₀ (weightValue nu v n P b t p).property.1 (weightValue nu v n P b t p).property.2))
  convert H using 1
  funext p
  dsimp only [Function.comp_def]
  ring

theorem integral_jointLaw_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ)
    {F : (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) → ℝ}
    (hM : Measurable F) (hF : Integrable F (jointLaw nu v n)) :
    (∫ p, F p ∂jointLaw nu v n)=
      ∫ x, (∫ w, (∫ old, F ((x,w),old) ∂Measure.pi (fun _ : Fin (n+1) ↦ parameterizedGibbsKernel nu v (x,w)))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ∂positiveCubeLaw K := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  unfold jointLaw at hF ⊢
  have hIM : Measurable (fun z ↦ ∫ old, F (z,old) ∂iid (parameterizedGibbsKernel nu v) (n+1) z) :=
    (hM.stronglyMeasurable.integral_kernel_prod_right' (κ := iid (parameterizedGibbsKernel nu v) (n+1))).measurable
  have hN := ((Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF).2
  have hS := hN.mono' hIM.aestronglyMeasurable (Eventually.of_forall (fun z ↦ norm_integral_le_integral_norm
    (f := fun old ↦ F (z,old))))
  rw [Measure.integral_compProd hF,integral_prod _ hS]
  simp only [iid_apply]

theorem weighted_power_eq_partitionMoment {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hb : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hb0 : ∀ x p, 0≤b x p) (hb1 : ∀ x p, b x p≤1) (t : ℝ) :
    (∫ p, rootFactor nu v n P Phi t p*(weightValue nu v n P b t p : ℝ)^m ∂jointLaw nu v n)=
      ∫ x, partitionMoment nu v n m P Phi (fun x _ ↦ b x) x t ∂positiveCubeLaw K := by
  have hM : Measurable (fun p ↦ rootFactor nu v n P Phi t p*(weightValue nu v n P b t p : ℝ)^m) := by
    convert (rootFactor_measurable nu hv n P hPhi t).mul
      ((measurable_subtype_coe.comp (weightValue_measurable nu hv n P hb t)).pow_const m) using 1
    rfl
  rw [integral_jointLaw_eq nu hv n hM (weighted_power_integrable nu hv n P hPhi hp hb t m)]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  simp only [partitionMoment,Kernel.sectR_apply]
  apply integral_congr_ae
  refine Eventually.of_forall (fun w ↦ ?_)
  apply integral_congr_ae
  refine Eventually.of_forall (fun old ↦ ?_)
  dsimp only
  rw [weightValue_coe_eq_meanValue nu hv n P hb hb0 hb1]
  simp only [rootFactor,meanValue,tiltedWeightMean,reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,
    Kernel.sectR_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]


end
end TensorPCA.NonRSLowerProofs.SphericalGGWeightObservable
