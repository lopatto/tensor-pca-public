-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeBallGG
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage

/-! Amplitude means of the literal Tree fresh-ball residual. A measurable amplitude
restriction remains inside both the residual and own-score error integrals, so
disjoint prechosen threshold cells do not incur a family-size factor in their
approximation error.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeBallAverage
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open GGFiniteFirstJet GGFiniteParameterizedJets
open SphericalGGJetFamily SphericalGGTreeCylinder SphericalGGTreeBallGG
open SphericalGGThresholdFirstMomentAverage SphericalPolynomialFirstJetClippedBudget
open FiniteNestedPartition
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Signed physical fresh-ball error, before taking an amplitude mean. -/
def freshBallResidual {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ)
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
    (l : Fin depth) (i : Fin (n+1)) (x : Fin K → ℝ) : ℝ :=
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
  (∫ s,Phi (initial s)*(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ))
      (unitOverlap (s i.castSucc) (s (Fin.last (n+1)))) ∂law d G (n+2))-
    (∫ old,Phi old ∂law d G (n+1))*((ballSize t l i : ℝ)-lowerHeight nu v (cuts l) x)/((n : ℝ)+1)

private theorem actualMean_measurable_bound {N K m : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (f : (Fin m → UnitSpin N) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ s,|f s|≤C) :
    Measurable (fun x : Fin K → ℝ ↦ ∫ s,f s
      ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) m) ∧
      ∀ x : Fin K → ℝ,|∫ s,f s
        ∂law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
          ((parameterizedGibbsKernel nu v).sectR x) m|≤C := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  refine ⟨parameterized_law_integral_measurable _ _ m (fun _ s ↦ f s)
    (hf.comp measurable_snd) (fun _ s ↦ hb s),?_⟩
  intro x
  have H := norm_integral_le_of_norm_le_const
    (μ := law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR x) m) (f := f) (C := C)
    (.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hb s))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

private theorem cylinder_tests {N depth n : ℕ}
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
    (l : Fin depth) (i : Fin (n+1)) :
    let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
    let f := fun s : Fin (n+2) → UnitSpin N ↦ Phi (initial s)*(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ))
      (unitOverlap (s i.castSucc) (s (Fin.last (n+1))))
    Measurable Phi ∧ (∀ old,|Phi old|≤1) ∧ Measurable f ∧ ∀ s,|f s|≤1 := by
  dsimp only
  let Phi := ({old | treeCylinder cuts t old} : Set (Fin (n+1) → UnitSpin N)).indicator (fun _ ↦ (1 : ℝ))
  have hPhi : Measurable Phi := measurable_const.indicator (treeCylinder_measurable cuts t)
  have hPb (old) : |Phi old|≤1 := by by_cases h : treeCylinder cuts t old <;> simp [Phi,h]
  have hI : Measurable ((Ici (cuts l)).indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Ici
  have hIb (r : ℝ) : |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r|≤1 := by
    by_cases h : r∈Ici (cuts l) <;> simp [h]
  have hPair : Measurable (fun s : Fin (n+2) → UnitSpin N ↦ (s i.castSucc,s (Fin.last (n+1)))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hR : Measurable (fun s : Fin (n+2) → UnitSpin N ↦ unitOverlap (s i.castSucc) (s (Fin.last (n+1)))) := by
    simpa only [Function.comp_def] using (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair
  refine ⟨hPhi,hPb,(hPhi.comp (initial_measurable _)).mul (hI.comp hR),?_⟩
  intro s
  rw [abs_mul]
  exact (mul_le_mul (hPb _) (hIb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem freshBallResidual_measurable {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
    (l : Fin depth) (i : Fin (n+1)) :
    Measurable (freshBallResidual (K := K) nu v cuts t l i) := by
  obtain ⟨hPhi,hPb,hf,hfb⟩ := cylinder_tests (N := N) cuts t l i
  exact (actualMean_measurable_bound nu hv _ hf hfb).1.sub
    (((actualMean_measurable_bound nu hv _ hPhi hPb).1.mul
      (measurable_const.sub (lowerHeight_measurable nu hv (cuts l)))).div_const _)

theorem freshBallResidual_abs_le {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
    (l : Fin depth) (i : Fin (n+1)) (x : Fin K → ℝ) :
    |freshBallResidual nu v cuts t l i x|≤1+((ballSize t l i : ℝ)+1)/((n : ℝ)+1) := by
  obtain ⟨hPhi,hPb,hf,hfb⟩ := cylinder_tests (N := N) cuts t l i
  have hOld := (actualMean_measurable_bound nu hv _ hPhi hPb).2 x
  have hFresh := (actualMean_measurable_bound nu hv _ hf hfb).2 x
  have hLower := lowerHeight_mem_Icc nu hv (cuts l) x
  have hSize : 0≤(ballSize t l i : ℝ) := Nat.cast_nonneg _
  have hH : |(ballSize t l i : ℝ)-lowerHeight nu v (cuts l) x|≤(ballSize t l i : ℝ)+1 := by
    exact abs_le.mpr ⟨by linarith only [hLower.2,hSize],by linarith only [hLower.1]⟩
  have hDen : 0<(n : ℝ)+1 := by positivity
  unfold freshBallResidual
  dsimp only
  calc
    _ ≤ _+_ := abs_sub _ _
    _ ≤ 1+((ballSize t l i : ℝ)+1)/((n : ℝ)+1) := by
      apply add_le_add hFresh
      rw [abs_div,abs_mul,abs_of_pos hDen]
      apply div_le_div_of_nonneg_right _ hDen.le
      exact (mul_le_mul hOld hH (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem freshBallResidual_integrable {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
    (l : Fin depth) (i : Fin (n+1)) :
    Integrable (freshBallResidual (K := K) nu v cuts t l i) (positiveCubeLaw K) :=
  Integrable.of_bound (freshBallResidual_measurable nu hv cuts t l i).aestronglyMeasurable
    (1+((ballSize t l i : ℝ)+1)/((n : ℝ)+1))
    (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using freshBallResidual_abs_le nu hv cuts t l i x))

theorem masked_freshBallResidual_mean_le {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (cuts : Fin depth → ℝ) (t : NestedPartition depth (n+1))
    (l : Fin depth) (i : Fin (n+1)) (E : Set (Fin K → ℝ)) (hE : MeasurableSet E)
    (P : Polynomial ℝ) (hPK : P.natDegree≤K)
    (hGlobal : ∀ r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    (∫ x,E.indicator (fun x ↦ |freshBallResidual nu v cuts t l i x|) x ∂positiveCubeLaw K)≤
      (∫ x,E.indicator (fun x ↦ ∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q) x ∂positiveCubeLaw K)+
      2*(∫ x,E.indicator (fun x ↦ pairMean nu v (fun r ↦ |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
        extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K) := by
  let L : (Fin K → ℝ) → ℝ := fun x ↦ pairMean nu v (fun r ↦ |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
    extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x
  have hIb (r : ℝ) : |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r|≤1 := by
    by_cases h : r∈Ici (cuts l) <;> simp [h]
  have hTest (r : ℝ) : abs (abs ((Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
      extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r))≤3 := by
    rw [abs_abs]
    exact (abs_sub _ _).trans (by linarith only [hIb r,hGlobal r])
  have hTestM : Measurable (fun r ↦ |(Ici (cuts l)).indicator (fun _ ↦ (1 : ℝ)) r-
      extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) :=
    (continuous_abs.measurable : Measurable (abs : ℝ→ℝ)).comp
      ((measurable_const.indicator measurableSet_Ici).sub (extendTest_continuous _).measurable)
  have hLm : Measurable L := pairMean_measurable nu hv.le hTestM hTest
  have hLI : Integrable L (positiveCubeLaw K) := Integrable.of_bound hLm.aestronglyMeasurable 3
    (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using pairMean_abs_le nu hv.le hTest x))
  have hPolyI : Integrable (fun x : Fin K → ℝ ↦ ∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q) (positiveCubeLaw K) :=
    integrable_finsetSum (Finset.range (K+1)) (fun q _ ↦ (boundedPowerError_integrable nu hv.le n q).const_mul |P.coeff q|)
  have hResI := ((freshBallResidual_integrable nu hv.le cuts t l i).abs).indicator hE
  have hPoint : ∀ᵐ x ∂positiveCubeLaw K,
      E.indicator (fun x ↦ |freshBallResidual nu v cuts t l i x|) x≤
        E.indicator (fun x ↦ ∑ q ∈ Finset.range (K+1),|P.coeff q| *boundedPowerError nu v x n q) x+2*E.indicator L x := by
    apply (positiveCubeLaw_support K).mono
    intro x hx
    by_cases h : x∈E
    · simp only [Set.indicator_of_mem h]
      have hxp (p : Fin K) : 0<x p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) (hx p).1
      have hxb (p : Fin K) : |x p|≤2 := by rw [abs_of_pos (hxp p)]; linarith only [(hx p).2]
      exact fixed_amplitude_tree_ball_gg nu hv x hxb hxp cuts t l i P hPK hGlobal
    · simp only [Set.indicator_of_notMem h,mul_zero,zero_add,le_refl]
  have H := integral_mono_ae hResI ((hPolyI.indicator hE).add ((hLI.indicator hE).const_mul 2)) hPoint
  simp only [Pi.add_apply] at H
  rw [integral_add (hPolyI.indicator hE) ((hLI.indicator hE).const_mul 2),integral_const_mul] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeBallAverage
