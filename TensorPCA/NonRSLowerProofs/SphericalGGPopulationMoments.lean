-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedPopulationReplicaMoments
public import TensorPCA.NonRSLowerProofs.SphericalGGWeightObservable
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedGibbsTransport
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingNormalization

/-! Exact population deficit moments under the same-amplitude perturbed prior and the
existing finite-GG joint replica law. No empirical sampling, collision approximation
or new joint probability law is introduced.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGPopulationMoments
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open SphericalGGWeightObservable BoundedPopulationReplicaMoments
open FiniteCavityBulkUnitSpinPrior FiniteCavityPerturbedFields FiniteCavityPerturbedGibbsTransport
open CompensationMarkClippingNormalization CompensationMarkClippingMeasure
open GaussianCompactFeatureComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {W : Type*} [MeasurableSpace W]

theorem population_moment_eq_jointLaw {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (gamma : Measure W) [IsProbabilityMeasure gamma] (n : ℕ)
    {Z : W→UnitSpin N→ℝ} (hZ : Measurable (fun p : W×UnitSpin N => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w s,0≤Z w s ∧ Z w s≤a) :
    (∫amp,(∫gP,(∫w,(∫s,Z w s∂parameterizedGibbsKernel (K := K) nu v (amp,gP))^(n+1)∂gamma)
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)=
      ∫q,(∫w,∏i : Fin (n+1),Z w (q.2 i)∂gamma)∂jointLaw (K := K) nu v n := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := (positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
  let G := parameterizedGibbsKernel (K := K) nu v
  have hPop := population_power_joint_integrable d gamma G (n+1) hZ ha hb
  have hOuter := hPop.integral_prod_left
  have H := population_power_eq_joint_replica_product d gamma G (n+1) hZ ha hb
  dsimp only [d] at H hOuter
  rw [integral_prod _ hOuter] at H
  exact H

theorem clipped_population_deficit_mean_eq {V : Type*} [MeasurableSpace V]
    (nu : Measure V) [IsProbabilityMeasure nu] {Y : V→ℝ} (hY : Measurable Y)
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) :
    1-(∫s,max b (min (Y s) cap)∂nu)/cap=
      ∫s,1-max b (min (Y s) cap)/cap∂nu := by
  have hClip : Integrable (fun s => max b (min (Y s) cap)) nu := by
    simpa only [Real.rpow_one] using clipped_power_integrable nu hY
      (alpha := 1) hb hb1 hcap (by norm_num) le_rfl
  exact deficit_mean_eq nu hClip cap

/-- The nonlinear population deficit is tensorized exactly. Its shared cavity noise has
been averaged before the old-spin GG test.
-/
theorem clipped_population_moment_eq_jointLaw {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (gamma : Measure W) [IsProbabilityMeasure gamma] (n : ℕ)
    {Y : W→UnitSpin N→ℝ} (hY : Measurable (fun p : W×UnitSpin N => Y p.1 p.2))
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) :
    (∫amp,(∫gP,(∫w,(1-(∫s,max b (min (Y w s) cap)
      ∂parameterizedGibbsKernel (K := K) nu v (amp,gP))/cap)^(n+1)∂gamma)
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)=
      ∫q,(∫w,∏i : Fin (n+1),(1-max b (min (Y w (q.2 i)) cap)/cap)∂gamma)
        ∂jointLaw (K := K) nu v n := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let Z := fun w s => 1-max b (min (Y w s) cap)/cap
  have hZ : Measurable (fun p : W×UnitSpin N => Z p.1 p.2) :=
    measurable_const.sub ((measurable_const.max (hY.min measurable_const)).div_const cap)
  have ha : 0≤1-b/cap := (deficit_bounds (y := 0) hb hb1 hcap).2.2.1
  have hBound (w : W) (s : UnitSpin N) : 0≤Z w s ∧ Z w s≤1-b/cap :=
    ⟨(deficit_bounds (y := Y w s) hb hb1 hcap).1,(deficit_bounds (y := Y w s) hb hb1 hcap).2.1⟩
  have H := population_moment_eq_jointLaw (K := K) nu hv gamma n hZ ha hBound
  have hMean (amp : Fin K→ℝ) (gP : PerturbationDisorder N K) (w : W) :
      (∫s,Z w s∂parameterizedGibbsKernel nu v (amp,gP))=
        1-(∫s,max b (min (Y w s) cap)∂parameterizedGibbsKernel nu v (amp,gP))/cap := by
    have hYw : Measurable (Y w) := hY.comp (measurable_const.prodMk measurable_id)
    exact (clipped_population_deficit_mean_eq _ hYw hb hb1 hcap).symm
  simp_rw [hMean] at H
  exact H

/-- Pointwise in bulk disorder, the population prior equals the perturbed physical prior
in ASS, with the same amplitude and Gaussian banks.
-/
theorem actual_bulk_clipped_population_moment_eq_jointLaw {N : ℕ} (hN : 0<N)
    (M k K : ℕ) (mu beta : ℝ) {v : ℝ} (hv : 0≤v)
    (gB : GroundState.Disorder N k) (gamma : Measure W) [IsProbabilityMeasure gamma] (n : ℕ)
    {Y : W→Model.Vector N→ℝ} (hY : Measurable (fun p : W×Model.Vector N => Y p.1 p.2))
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) :
    letI := bulkPriorKernel_probability hN M k mu beta gB
    (∫amp,(∫gP,(∫w,(1-(∫x,max b (min (Y w x) cap)
      ∂perturbedBulkGibbs N M k K mu beta v amp (sumJoin (gB,gP)))/cap)^(n+1)∂gamma)
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)=
      ∫q,(∫w,∏i : Fin (n+1),(1-max b (min (Y w (q.2 i).val) cap)/cap)∂gamma)
        ∂jointLaw (K := K) (bulkPriorKernel N M k mu beta gB) v n := by
  letI := bulkPriorKernel_probability hN M k mu beta gB
  have hLift : Measurable (fun p : W×UnitSpin N => Y p.1 p.2.val) :=
    hY.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have H := clipped_population_moment_eq_jointLaw (K := K) (bulkPriorKernel N M k mu beta gB)
    hv gamma n (Y := fun w (s : UnitSpin N) => Y w s.val) hLift hb hb1 hcap
  have hMean (amp : Fin K→ℝ) (gP : PerturbationDisorder N K) (w : W) :
      (∫s,max b (min (Y w s.val) cap)
        ∂parameterizedGibbsKernel (bulkPriorKernel N M k mu beta gB) v (amp,gP))=
      ∫x,max b (min (Y w x) cap)∂perturbedBulkGibbs N M k K mu beta v amp (sumJoin (gB,gP)) := by
    rw [parameterizedGibbsKernel_apply _ hv]
    unfold unitLinear
    exact integral_gibbs_bulkPriorKernel_eq_perturbedBulkGibbs
      hN M k K mu beta v amp gB gP (fun x => max b (min (Y w x) cap))
  simp_rw [hMean] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.SphericalGGPopulationMoments
