-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeCylinder

/-! On a Tree cylinder, the GG fresh-ball coefficient is (ball size - lower-tail
height)/(old count), where the height comes from the pair law at that amplitude. The
error follows from the clipped polynomial budget and its L1 score approximation.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeBallGG
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteFirstJet GGFiniteFirstJetPermutation
open SphericalGGJetFamily SphericalGGTreeCylinder SphericalPolynomialFirstJetClippedBudget
open FiniteNestedPartition
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem indicator_discrepancy_bound {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p,|x p|≤2) (hxp : ∀ p,0<x p)
    (n : ℕ) (cut : ℝ) (i : Fin (n+1)) (Phi : (Fin (n+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable Phi) (hp : ∀ old,|Phi old|≤1)
    (P : Polynomial ℝ) (hPK : P.natDegree≤K)
    (hGlobal : ∀ r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := (parameterizedGibbsKernel nu v).sectR x
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    |discrepancy n mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s i.castSucc) (s (Fin.last (n+1))))
      (fun j s ↦ unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc))
      ((Ici cut).indicator (fun _ ↦ (1 : ℝ)))|≤
      (∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q)+
        2*pairMean nu v (fun r ↦ |(Ici cut).indicator (fun _ ↦ (1 : ℝ)) r-
          extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x := by
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv.le
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
  let I : ℝ → ℝ := (Ici cut).indicator (fun _ ↦ (1 : ℝ))
  let Q : ℝ → ℝ := extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1))
  let f : (Fin (n+2) → UnitSpin N) → ℝ := fun s ↦ Phi (initial s)
  let F : (Fin (n+1) → UnitSpin N) → ℝ := fun old ↦ Phi (fun j ↦ old ((Equiv.swap i 0) j))
  have hI : Measurable I := measurable_const.indicator measurableSet_Ici
  have hIb (r : ℝ) : |I r|≤2 := by dsimp only [I]; by_cases h : r∈Ici cut <;> simp [h]
  have hQ : Measurable Q := (extendTest_continuous _).measurable
  have hf : Measurable f := hPhi.comp (initial_measurable _)
  have hFb (old) : |F old|≤1 := hp _
  have hFm : Measurable F := hPhi.comp (Measurable.of_eval (fun j ↦ measurable_pi_apply _))
  have hTransfer := discrepancy_l1_lipschitz n mu rho f
    (fun s ↦ unitOverlap (s i.castSucc) (s (Fin.last (n+1))))
    (fun j s ↦ unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc))
    hf.aestronglyMeasurable (.of_forall (fun s ↦ hp _))
    (fresh_overlap_hasLaw d G n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) i)
    (old_overlap_hasLaw d G n (SphericalFirstJetPowerBudget.unitOverlap_measurable N) i)
    (Integrable.of_bound hI.aestronglyMeasurable 2 (.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hIb r)))
    (Integrable.of_bound hQ.aestronglyMeasurable 2 (.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hGlobal r)))
  have hPoly := full_polynomial_discrepancy_clipped_le nu hv x hx hxp n F hFm hFb P hPK
  dsimp only at hPoly
  rw [← parameterized_slice_eq_actual nu hv.le x] at hPoly
  have hAnchor := anchored_discrepancy_eq_first d G n (SphericalFirstJetPowerBudget.unitOverlap_measurable N)
    Phi hPhi hp Q hQ hGlobal i
  have hPoly' : |discrepancy n mu rho f
      (fun s ↦ unitOverlap (s i.castSucc) (s (Fin.last (n+1))))
      (fun j s ↦ unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)) Q|≤
      ∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q := by
    rw [hAnchor]; exact hPoly
  have ht := abs_le.mp hTransfer
  have hh := abs_le.mp hPoly'
  change |discrepancy n mu rho f
      (fun s ↦ unitOverlap (s i.castSucc) (s (Fin.last (n+1))))
      (fun j s ↦ unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)) I|≤
      (∑ q ∈ Finset.range (K+1),|P.coeff q| * boundedPowerError nu v x n q)+
        2*(∫ r,|I r-Q r| ∂rho)
  exact abs_le.mpr ⟨by linarith only [ht.1,hh.1],by linarith only [ht.2,hh.2]⟩

private theorem treeCylinder_discrepancy_eq {N depth n : ℕ}
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1)) (l : Fin depth) (i : Fin (n+1))
    (mu : Measure (Fin (n+2) → UnitSpin N)) [IsProbabilityMeasure mu] (rho : Measure ℝ) :
    let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
    let I := (Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ))
    discrepancy n mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s i.castSucc) (s (Fin.last (n+1))))
      (fun j s ↦ unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)) I=
      (∫ s,Phi (initial s)*I (unitOverlap (s i.castSucc) (s (Fin.last (n+1)))) ∂mu)-
        (∫ s,Phi (initial s) ∂mu)*((ballSize t l i : ℝ)-1+(∫ r,I r ∂rho))/((n : ℝ)+1) := by
  classical
  dsimp only
  let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
  let I := (Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ))
  have hPm : Measurable Phi := measurable_const.indicator (treeCylinder_measurable cuts t)
  have hIm : Measurable I := measurable_const.indicator measurableSet_Ici
  have hPb (old) : |Phi old|≤1 := by by_cases h : treeCylinder cuts t old <;> simp [Phi,h]
  have hIb (r : ℝ) : |I r|≤1 := by by_cases h : r∈Ici (cuts l) <;> simp [I,h]
  have hInt (j : Fin n) : Integrable (fun s : Fin (n+2) → UnitSpin N ↦
      Phi (initial s)*I (unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc))) mu := by
    have hPair : Measurable (fun s : Fin (n+2) → UnitSpin N ↦ (s i.castSucc,s (i.succAbove j).castSucc)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hR : Measurable (fun s : Fin (n+2) → UnitSpin N ↦
        unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)) := by
      simpa only [Function.comp_def] using (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair
    apply Integrable.of_bound ((hPm.comp (initial_measurable _)).mul (hIm.comp hR)).aestronglyMeasurable 1
    exact .of_forall (fun s ↦ by
      change |Phi (initial s)*I (unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc))|≤1
      rw [abs_mul]
      exact (mul_le_mul (hPb _) (hIb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hSum : (∑ j : Fin n,∫ s,Phi (initial s)*I
      (unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)) ∂mu)=
      (∫ s,Phi (initial s) ∂mu)*((ballSize t l i : ℝ)-1) := by
    rw [← integral_finsetSum Finset.univ (fun j _ ↦ hInt j)]
    have hFun : (fun s : Fin (n+2) → UnitSpin N ↦ ∑ j : Fin n,Phi (initial s)*I
        (unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)))=
        (fun s ↦ Phi (initial s)*((ballSize t l i : ℝ)-1)) := by
      funext s
      rw [← Finset.mul_sum]
      by_cases h : treeCylinder cuts t (initial s)
      · have hRow : (∑ j : Fin n,I (unitOverlap (s i.castSucc) (s (i.succAbove j).castSucc)))=
            (ballSize t l i : ℝ)-1 := treeCylinder_offdiag_row_sum cuts t (initial s) h l i
        rw [hRow]
      · have hZero : Phi (initial s)=0 := by simp [Phi,h]
        rw [hZero,zero_mul,zero_mul]
    rw [hFun,integral_mul_const]
  unfold discrepancy
  rw [hSum]
  have hDen : (n : ℝ)+1≠0 := by positivity
  field_simp
  ring

theorem fixed_amplitude_tree_ball_gg {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p,|x p|≤2) (hxp : ∀ p,0<x p)
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1)) (l : Fin depth) (i : Fin (n+1))
    (P : Polynomial ℝ) (hPK : P.natDegree≤K)
    (hGlobal : ∀ r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := (parameterizedGibbsKernel nu v).sectR x
    let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
    |(∫ s,Phi (initial s)*(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s i.castSucc) (s (Fin.last (n+1)))) ∂law d G (n+2))-
      (∫ old,Phi old ∂law d G (n+1))*((ballSize t l i : ℝ)-lowerHeight nu v (cuts l) x)/((n : ℝ)+1)|≤
      (∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q)+
        2*pairMean nu v (fun r ↦ |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
          extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x := by
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv.le
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
  let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
  have hPhi : Measurable Phi := measurable_const.indicator (treeCylinder_measurable cuts t)
  have hp (old) : |Phi old|≤1 := by by_cases h : treeCylinder cuts t old <;> simp [Phi,h]
  have H := indicator_discrepancy_bound nu hv x hx hxp n (cuts l) i Phi hPhi hp P hPK hGlobal
  dsimp only at H
  rw [treeCylinder_discrepancy_eq cuts t l i mu rho,prefix_test_mean d G n Phi hPhi] at H
  have hNum : (ballSize t l i : ℝ)-1+
      (∫ r,(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)=
      (ballSize t l i : ℝ)-lowerHeight nu v (cuts l) x := by
    have hComp := lowerHeight_add_upper nu hv.le (cuts l) x
    change lowerHeight nu v (cuts l) x+
      (∫ r,(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)=1 at hComp
    linarith only [hComp]
  rw [hNum] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeBallGG
