-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdWeights
public import TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetCubeMean

/-! The threshold GG first moment. Earlier-anchor threshold terms vanish only on the
stated support of the old observable; the remaining pair mean is the same
amplitude's disorder-averaged pair mean.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMoment
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteFirstJet GGFiniteFirstJetPermutation
open SphericalGGJetFamily SphericalGGThresholdWeights
open SphericalPolynomialFirstJetClippedBudget
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem threshold_discrepancy_eq {V : Type*} [MeasurableSpace V]
    (n : ℕ) (mu : Measure (Fin (n+2) → V)) (rho : Measure ℝ)
    (R : V → V → ℝ) (u : ℝ) (Phi : (Fin (n+1) → V) → ℝ)
    (hSupport : ∀ old,Phi old≠0→∀ l : Fin n,R (old (Fin.last n)) (old l.castSucc)<u) :
    discrepancy n mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ R (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
      (fun l s ↦ R (s (Fin.last n).castSucc) (s ((Fin.last n).succAbove l).castSucc))
      ((Ici u).indicator (fun _ ↦ (1 : ℝ))) =
      (∫ s,Phi (initial s)*(Ici u).indicator (fun _ ↦ (1 : ℝ))
        (R (s (Fin.last n).castSucc) (s (Fin.last (n+1)))) ∂mu)-
      (∫ s,Phi (initial s) ∂mu)*(∫ r,(Ici u).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)/((n : ℝ)+1) := by
  have hz (l : Fin n) : (∫ s,Phi (initial s)*(Ici u).indicator (fun _ ↦ (1 : ℝ))
      (R (s (Fin.last n).castSucc) (s ((Fin.last n).succAbove l).castSucc)) ∂mu)=0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall (fun s ↦ by
      by_cases hp : Phi (initial s)=0
      · simp only [hp,zero_mul,Pi.zero_apply]
      · have hlt := hSupport (initial s) hp l
        simp only [initial,Fin.succAbove_last] at hlt ⊢
        rw [Set.indicator_of_notMem (show R (s (Fin.last n).castSucc) (s l.castSucc.castSucc)∉Ici u from not_le.mpr hlt),mul_zero]
        rfl)
  unfold discrepancy
  simp only [hz,Finset.sum_const_zero,zero_div,sub_zero]

theorem fixed_amplitude_threshold_first_moment {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p,|x p|≤2) (hxp : ∀ p,0<x p)
    (n : ℕ) (u : ℝ) (Phi : (Fin (n+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable Phi) (hp : ∀ old,|Phi old|≤1)
    (hSupport : ∀ old,Phi old≠0→∀ l : Fin n,
      unitOverlap (old (Fin.last n)) (old l.castSucc)<u)
    (P : Polynomial ℝ) (hPK : P.natDegree≤K)
    (hGlobal : ∀ r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := (parameterizedGibbsKernel nu v).sectR x
    |(∫ s,Phi (initial s)*(Ici u).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1)))) ∂law d G (n+2))-
      (∫ old,Phi old ∂law d G (n+1))*pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) x/((n : ℝ)+1)|≤
      (∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q)+
        2*pairMean nu v (fun r ↦ |(Ici u).indicator (fun _ ↦ (1 : ℝ)) r-
          extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x := by
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv.le
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
  let I : ℝ → ℝ := (Ici u).indicator (fun _ ↦ (1 : ℝ))
  let Q : ℝ → ℝ := extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1))
  let f : (Fin (n+2) → UnitSpin N) → ℝ := fun s ↦ Phi (initial s)
  let F : (Fin (n+1) → UnitSpin N) → ℝ := fun old ↦ Phi (fun i ↦ old ((Equiv.swap (Fin.last n) 0) i))
  have hI : Measurable I := measurable_const.indicator measurableSet_Ici
  have hIb (r : ℝ) : |I r|≤2 := by
    dsimp only [I]; by_cases hr : r∈Ici u <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hr]
  have hQ : Measurable Q := (extendTest_continuous _).measurable
  have hf : Measurable f := hPhi.comp (initial_measurable _)
  have hFb (old) : |F old|≤1 := hp _
  have hFm : Measurable F := hPhi.comp (Measurable.of_eval (fun i ↦ measurable_pi_apply _))
  have hTransfer := discrepancy_l1_lipschitz n mu rho f
    (fun s ↦ unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
    (fun l s ↦ unitOverlap (s (Fin.last n).castSucc) (s ((Fin.last n).succAbove l).castSucc))
    hf.aestronglyMeasurable (Eventually.of_forall (fun s ↦ hp _))
    (fresh_overlap_hasLaw d G n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (Fin.last n))
    (old_overlap_hasLaw d G n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) (Fin.last n))
    (Integrable.of_bound hI.aestronglyMeasurable 2 (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hIb r)))
    (Integrable.of_bound hQ.aestronglyMeasurable 2 (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hGlobal r)))
  have hPoly := full_polynomial_discrepancy_clipped_le nu hv x hx hxp n F hFm hFb P hPK
  dsimp only at hPoly
  rw [← parameterized_slice_eq_actual nu hv.le x] at hPoly
  have hAnchor := anchored_discrepancy_eq_first d G n (SphericalFirstJetPowerBudget.unitOverlap_measurable N)
    Phi hPhi hp Q hQ hGlobal (Fin.last n)
  have hPoly' : |discrepancy n mu rho f
      (fun s ↦ unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
      (fun l s ↦ unitOverlap (s (Fin.last n).castSucc) (s ((Fin.last n).succAbove l).castSucc)) Q|≤
      ∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q := by
    rw [hAnchor]; exact hPoly
  have H : |discrepancy n mu rho f
      (fun s ↦ unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
      (fun l s ↦ unitOverlap (s (Fin.last n).castSucc) (s ((Fin.last n).succAbove l).castSucc)) I|≤
      2*(∫ r,|I r-Q r| ∂rho)+(∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q) := by
    have ht := abs_le.mp hTransfer
    have hh := abs_le.mp hPoly'
    exact abs_le.mpr ⟨by linarith only [ht.1,hh.1],by linarith only [ht.2,hh.2]⟩
  rw [threshold_discrepancy_eq n mu rho unitOverlap u Phi hSupport,
    prefix_test_mean d G n Phi hPhi] at H
  exact H.trans_eq (add_comm _ _)

end
end TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMoment
