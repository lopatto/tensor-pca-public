-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteJointScoreStability
public import TensorPCA.NonRSLowerProofs.SphericalGGContinuousWeights

/-! Bounded-overlap-score weight observables. Each amplitude retains its own Gaussian-
averaged pair means.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGBoundedScoreWeights
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open GGFiniteFirstJet GGFiniteReweightingDerivative GGFiniteParameterizedJets
open GGFiniteReplicaWeightMoments SphericalGGJetFamily SphericalGGWeightObservable
open scoped BigOperators
noncomputable section

def scoreIntegrand {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (psi : Fin (n+1) → ℝ → ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (chi : ℝ → ℝ) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) : ℝ :=
  GGFiniteJointScoreStability.integrand n (parameterizedGibbsKernel nu v) unitOverlap psi
    (fun j ↦ pairMean nu v (psi j) p.1.1) (Phi p.1.1) (b p.1.1) chi t p

def scoreObservable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (psi : Fin (n+1) → ℝ → ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (chi : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ p, scoreIntegrand nu v n psi Phi b chi t p ∂jointLaw nu v n

theorem scoreIntegrand_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (t : ℝ) :
    Measurable (scoreIntegrand nu v n psi Phi b chi t) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hW := parameterized_weight_measurable (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) hpsi
    (fun j ↦ pairMean_measurable nu hv (hpsi j) (hb j)) hPhi (t := fun _ ↦ t) measurable_const
  have hbState : Measurable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×
      ((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1.1 p.2) := by
    convert hbM.comp (measurable_fst.fst.prodMk measurable_snd) using 1 <;> rfl
  have hU := parameterized_tiltedWeightMean_measurable (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) hpsi (b := fun p ↦ b p.1) hbState t
  convert hW.mul (hchiM.comp hU) using 1 <;> rfl

theorem scoreIntegrand_abs_le {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ} {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C)
    (b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    {chi : ℝ → ℝ} (hchi : ∀ z, |chi z|≤1) (t : ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N)) :
    |scoreIntegrand nu v n psi Phi b chi t p|≤C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact GGFiniteJointScoreStability.integrand_abs_le (parameterizedGibbsKernel nu v) n
    (SphericalFirstJetPowerBudget.unitOverlap_measurable N) hpsi
    (fun j ↦ pairMean nu v (psi j) p.1.1) B hb
    (fun j ↦ pairMean_abs_le nu hv (hb j) p.1.1) (hp p.1.1) (b p.1.1) hchi t p

theorem scoreIntegrand_integrable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) (t : ℝ) :
    Integrable (scoreIntegrand nu v n psi Phi b chi t) (jointLaw nu v n) := by
  letI := jointLaw_probability nu hv n (K := K)
  exact Integrable.of_bound (scoreIntegrand_measurable nu hv n hpsi B hb hPhi hbM hchiM t).aestronglyMeasurable
    (C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j))) (Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs] using scoreIntegrand_abs_le nu hv n hpsi B hb hp b hchi t p))

theorem fixed_observable_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) (t : ℝ) (x : Fin K → ℝ) :
    GGFiniteJointScoreStability.observable (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap psi (Phi x) (b x) chi t=
      ∫ w, ∫ old, scoreIntegrand nu v n psi Phi b chi t ((x,w),old)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ parameterizedGibbsKernel nu v (x,w))
          ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hpM : Measurable (Phi x) := by
    convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hbS : Measurable (b x) := by
    convert hbM.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have HI := GGFiniteJointScoreStability.integrand_integrable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ((parameterizedGibbsKernel nu v).sectR x)
    n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) hpsi
    (fun j ↦ pairMean nu v (psi j) x) B hb (fun j ↦ pairMean_abs_le nu hv (hb j) x)
    hpM (hp x) hbS hchiM hchi t
  unfold GGFiniteJointScoreStability.observable
  change (∫ p, GGFiniteJointScoreStability.integrand n ((parameterizedGibbsKernel nu v).sectR x)
    unitOverlap psi (fun j ↦ pairMean nu v (psi j) x) (Phi x) (b x) chi t p
      ∂(SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ⊗ₘ
        iid ((parameterizedGibbsKernel nu v).sectR x) (n+1)))=_
  rw [Measure.integral_compProd HI]
  simp only [scoreIntegrand,GGFiniteJointScoreStability.integrand,pairMean,
    GGFiniteReplicaWeightMoments.tiltedWeightMean,reweightingNormalizer,
    GGFiniteEmpiricalNormalizer.normalizer,Kernel.sectR_apply,iid_apply]

theorem scoreObservable_eq_cube {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) (t : ℝ) :
    scoreObservable nu v n psi Phi b chi t=
      ∫ x, GGFiniteJointScoreStability.observable (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap psi (Phi x) (b x) chi t ∂positiveCubeLaw K := by
  unfold scoreObservable
  rw [integral_jointLaw_eq nu hv n (scoreIntegrand_measurable nu hv n hpsi B hb hPhi hbM hchiM t)
    (scoreIntegrand_integrable nu hv n hpsi B hb hPhi hp hbM hchiM hchi t)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ (fixed_observable_eq nu hv n hpsi B hb hPhi hp hbM hchiM hchi t x).symm)

theorem fixed_observable_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) (t : ℝ) :
    Measurable (fun x ↦ GGFiniteJointScoreStability.observable
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap psi (Phi x) (b x) chi t) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have H := ((scoreIntegrand_measurable nu hv n hpsi B hb hPhi hbM hchiM t).stronglyMeasurable.integral_kernel_prod_right'
    (κ := iid (parameterizedGibbsKernel nu v) (n+1))).measurable
  have H' := H.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
  convert H'.measurable using 1
  funext x
  rw [fixed_observable_eq nu hv n hpsi B hb hPhi hp hbM hchiM hchi t x]
  simp only [iid_apply]

theorem fixed_observable_integrable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2)) {C : ℝ}
    (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) (t : ℝ) :
    Integrable (fun x ↦ GGFiniteJointScoreStability.observable
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap psi (Phi x) (b x) chi t) (positiveCubeLaw K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  refine Integrable.of_bound (fixed_observable_measurable nu hv n hpsi B hb hPhi hp hbM hchiM hchi t).aestronglyMeasurable
    (C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j))) (Eventually.of_forall (fun x ↦ ?_))
  unfold GGFiniteJointScoreStability.observable
  have H := norm_integral_le_of_norm_le_const
    (μ := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ⊗ₘ
      iid ((parameterizedGibbsKernel nu v).sectR x) (n+1))
    (f := GGFiniteJointScoreStability.integrand n ((parameterizedGibbsKernel nu v).sectR x) unitOverlap psi
      (fun j ↦ pairMean nu v (psi j) x) (Phi x) (b x) chi t)
    (C := C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j))) (Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs] using GGFiniteJointScoreStability.integrand_abs_le
        ((parameterizedGibbsKernel nu v).sectR x) n (SphericalFirstJetPowerBudget.unitOverlap_measurable N)
        hpsi (fun j ↦ pairMean nu v (psi j) x) B hb (fun j ↦ pairMean_abs_le nu hv (hb j) x)
        (hp x) (b x) hchi t p))
  simpa only [probReal_univ,mul_one,pairMean] using H

theorem polynomial_scoreObservable_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hb0 : ∀ x p, 0≤b x p) (hb1 : ∀ x p, b x p≤1)
    (f : C(Icc (0 : ℝ) 1,ℝ)) (chi : ℝ → ℝ) (hc : ∀ z : Icc (0 : ℝ) 1,chi z=f z) (t : ℝ) :
    scoreObservable nu v n (SphericalGGZeroJets.tests P) Phi b chi t=weightObservable nu v n P Phi b f t := by
  unfold scoreObservable weightObservable
  apply integral_congr_ae
  refine Eventually.of_forall (fun p ↦ ?_)
  have he := hc (weightValue nu v n P b t p)
  rw [weightValue_coe_eq_meanValue nu hv n P hbM hb0 hb1 t p] at he
  simpa only [scoreIntegrand,GGFiniteJointScoreStability.integrand,rootFactor,meanValue] using
    congrArg (fun z : ℝ ↦ rootFactor nu v n P Phi t p*z) he

theorem scoreObservable_sub_le {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (psi phi : Fin (n+1) → ℝ → ℝ)
    (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    {b : (Fin K → ℝ) → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ)}
    (hbM : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 p.2))
    (hb0 : ∀ x q, 0≤b x q) (hb1 : ∀ x q, b x q≤1)
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) {L : ℝ} (hL : 0≤L)
    (hLip : ∀ x y, |chi x-chi y|≤L*|x-y|) (t : ℝ) :
    |scoreObservable nu v n psi Phi b chi t-scoreObservable nu v n phi Phi b chi t|≤
      (2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L))*
        (∫ x, (∑ j, pairMean nu v (fun r ↦ |psi j r-phi j r|) x) ∂positiveCubeLaw K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let Sp := fun x ↦ GGFiniteJointScoreStability.observable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap psi (Phi x) (b x) chi t
  let Sf := fun x ↦ GGFiniteJointScoreStability.observable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) n unitOverlap phi (Phi x) (b x) chi t
  let A := 2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L)
  let E : (Fin K → ℝ) → ℝ := fun x ↦ ∑ j, pairMean nu v (fun r ↦ |psi j r-phi j r|) x
  have hDMeas (j : Fin (n+1)) : Measurable (fun r ↦ |psi j r-phi j r|) := by
    convert continuous_abs.measurable.comp ((hpsi j).sub (hphi j)) using 1 <;> rfl
  have hDB (j : Fin (n+1)) (r : ℝ) : |(|psi j r-phi j r|)|≤2*B j := by
    rw [abs_abs]
    exact (abs_sub _ _).trans (by linarith [hpb j r,hfb j r])
  have hEachI (j : Fin (n+1)) : Integrable (fun x : Fin K → ℝ ↦ pairMean nu v (fun r ↦ |psi j r-phi j r|) x)
      (positiveCubeLaw K) := by
    refine Integrable.of_bound (pairMean_measurable nu hv (hDMeas j) (hDB j)).aestronglyMeasurable
      (2*B j) (Eventually.of_forall (fun x ↦ ?_))
    simpa only [Real.norm_eq_abs] using pairMean_abs_le nu hv (hDB j) x
  have hEI : Integrable E (positiveCubeLaw K) := integrable_finset_sum Finset.univ (fun j _ ↦ hEachI j)
  have hSp : Integrable Sp (positiveCubeLaw K) := fixed_observable_integrable nu hv n hpsi B hpb hPhi hp hbM hchiM hchi t
  have hSf : Integrable Sf (positiveCubeLaw K) := fixed_observable_integrable nu hv n hphi B hfb hPhi hp hbM hchiM hchi t
  have hPoint (x : Fin K → ℝ) : |Sp x-Sf x|≤A*E x := by
    have hpM : Measurable (Phi x) := by
      convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
    have hbS : Measurable (b x) := by
      convert hbM.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
    exact GGFiniteJointScoreStability.observable_sub_le
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ((parameterizedGibbsKernel nu v).sectR x)
      n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) psi phi hpsi hphi B hpb hfb hpM hC
      (hp x) hbS (hb0 x) (hb1 x) hchiM hchi hL hLip t
  have hAbsI : Integrable (fun x ↦ |Sp x-Sf x|) (positiveCubeLaw K) := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hSp.sub hSf).norm
  have HI := integral_mono hAbsI (hEI.const_mul A) hPoint
  rw [integral_const_mul] at HI
  rw [scoreObservable_eq_cube nu hv n hpsi B hpb hPhi hp hbM hchiM hchi t,
    scoreObservable_eq_cube nu hv n hphi B hfb hPhi hp hbM hchiM hchi t]
  change |(∫ x, Sp x ∂positiveCubeLaw K)-(∫ x, Sf x ∂positiveCubeLaw K)|≤_
  rw [← integral_sub hSp hSf]
  exact abs_integral_le_integral_abs.trans HI

end
end TensorPCA.NonRSLowerProofs.SphericalGGBoundedScoreWeights
