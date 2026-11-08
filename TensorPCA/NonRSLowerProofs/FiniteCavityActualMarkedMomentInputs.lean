-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityObservedPopulationMoments
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphereLogStepsCompression

/-! Literal bounded cavity deficits and their population moments on product probability
spaces. The Gaussian cavity mark stays shared by all replicas. Every Fubini
interchange follows from bounded deficit integrability.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityActualMarkedMomentInputs
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable SphericalGGPopulationMoments BoundedPopulationReplicaMoments
open FiniteCavityBulkUnitSpinPrior FiniteCavityPerturbedFields FiniteCavityPerturbedGibbsTransport
open FiniteCavityNumeratorMoments FiniteCavityShellGibbsPartition
open OneStepGaussianTiltEndpoint FiniteCavityGaussianCompatibility
open FiniteCavityCompensationThetaComparison GaussianCompactFeatureComparison
open FiniteCavityObservedPopulationMoments FiniteGaussianSphereLogStepsCompression
open CompensationMarkClippingNormalization
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem numerator_deficit_continuous {M : ℕ} (hM : 0<M) (L : ℝ) :
    Continuous (fun h : Model.Vector M => 1-min (sphericalLaplace M h) L/L) := by
  have H := Real.continuous_exp.comp (log_sphericalLaplace_lipschitz hM).continuous
  have hEq : (fun h : Model.Vector M => Real.exp (Real.log (sphericalLaplace M h)))=
      sphericalLaplace M := funext (fun h => Real.exp_log (sphericalLaplace_pos hM h))
  change Continuous (fun h : Model.Vector M => Real.exp (Real.log (sphericalLaplace M h))) at H
  rw [hEq] at H
  exact continuous_const.sub ((H.min continuous_const).div_const L)

theorem numerator_deficit_mem_Icc {M : ℕ} (hM : 0<M) {L : ℝ} (hL : 1≤L)
    (h : Model.Vector M) : 1-min (sphericalLaplace M h) L/L∈Icc (0 : ℝ) 1 := by
  have H := deficit_bounds (b := 1) (L := L) (y := sphericalLaplace M h)
    (by norm_num) le_rfl hL
  rw [max_eq_right (le_min (OneStepGaussianTiltOuter.one_le_sphericalLaplace hM h) hL)] at H
  exact ⟨H.1,H.2.1.trans H.2.2.2.le⟩

theorem compensation_deficit_continuous (b cap : ℝ) :
    Continuous (fun s : ℝ => 1-max b (min (Real.exp s) cap)/cap) :=
  continuous_const.sub ((continuous_const.max (Real.continuous_exp.min continuous_const)).div_const cap)

theorem compensation_deficit_mem_Icc {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap)
    (s : ℝ) : 1-max b (min (Real.exp s) cap)/cap∈Icc (0 : ℝ) 1 := by
  have H := deficit_bounds (y := Real.exp s) hb hb1 hcap
  exact ⟨H.1,H.2.1.trans H.2.2.2.le⟩

/-- The observed deficit moment is integrable under the background-times-cavity product
law and equals the replica-law test.
-/
theorem actual_bulk_clipped_product_moment_eq_jointLaw {W : Type*} [MeasurableSpace W]
    {N : ℕ} (hN : 0<N) (M k K : ℕ) (mu beta : ℝ) {v : ℝ} (hv : 0≤v)
    (gB : GroundState.Disorder N k) (gamma : Measure W) [IsProbabilityMeasure gamma] (n : ℕ)
    {Y : W→Model.Vector N→ℝ} (hY : Measurable (fun p : W×Model.Vector N => Y p.1 p.2))
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) :
    letI := bulkPriorKernel_probability hN M k mu beta gB
    Integrable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×W =>
      (1-(∫x,max b (min (Y p.2 x) cap)
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))/cap)^(n+1))
      (((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod gamma) ∧
    (∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×W,
      (1-(∫x,max b (min (Y p.2 x) cap)
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))/cap)^(n+1)
      ∂((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod gamma)=
      ∫q,(∫w,∏i : Fin (n+1),(1-max b (min (Y w (q.2 i).val) cap)/cap)∂gamma)
        ∂jointLaw (K := K) (bulkPriorKernel N M k mu beta gB) v n := by
  letI := bulkPriorKernel_probability hN M k mu beta gB
  letI := parameterizedGibbsKernel_markov (K := K) (bulkPriorKernel N M k mu beta gB) hv
  let d := (positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
  let G := parameterizedGibbsKernel (K := K) (bulkPriorKernel N M k mu beta gB) v
  let Z := fun w (s : UnitSpin N) => 1-max b (min (Y w s.val) cap)/cap
  have hLift : Measurable (fun p : W×UnitSpin N => Y p.1 p.2.val) :=
    hY.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hZ : Measurable (fun p : W×UnitSpin N => Z p.1 p.2) :=
    measurable_const.sub ((measurable_const.max (hLift.min measurable_const)).div_const cap)
  have ha : 0≤1-b/cap := (deficit_bounds (y := 0) hb hb1 hcap).2.2.1
  have hBound (w : W) (s : UnitSpin N) : 0≤Z w s ∧ Z w s≤1-b/cap :=
    ⟨(deficit_bounds (y := Y w s.val) hb hb1 hcap).1,
      (deficit_bounds (y := Y w s.val) hb hb1 hcap).2.1⟩
  have hPop := population_power_joint_integrable d gamma G (n+1) hZ ha hBound
  have hMean (amp : Fin K→ℝ) (gP : PerturbationDisorder N K) (w : W) :
      (∫s,Z w s∂G (amp,gP))=1-(∫x,max b (min (Y w x) cap)
        ∂perturbedBulkGibbs N M k K mu beta v amp (sumJoin (gB,gP)))/cap := by
    have hYw : Measurable (fun s : UnitSpin N => Y w s.val) :=
      hLift.comp (measurable_const.prodMk measurable_id)
    have hClip : (∫s,max b (min (Y w s.val) cap)∂G (amp,gP))=
        ∫x,max b (min (Y w x) cap)∂perturbedBulkGibbs N M k K mu beta v amp (sumJoin (gB,gP)) := by
      dsimp only [G]
      rw [parameterizedGibbsKernel_apply _ hv]
      unfold unitLinear
      exact integral_gibbs_bulkPriorKernel_eq_perturbedBulkGibbs
        hN M k K mu beta v amp gB gP (fun x => max b (min (Y w x) cap))
    change (∫s,1-max b (min (Y w s.val) cap)/cap∂G (amp,gP))=_
    rw [←clipped_population_deficit_mean_eq _ hYw hb hb1 hcap,hClip]
  simp_rw [hMean] at hPop
  refine ⟨hPop,?_⟩
  rw [integral_prod _ hPop]
  have hOuter := hPop.integral_prod_left
  dsimp only [d] at hOuter ⊢
  rw [integral_prod _ hOuter]
  exact actual_bulk_clipped_population_moment_eq_jointLaw hN M k K mu beta hv gB gamma n hY hb hb1 hcap

end
end TensorPCA.NonRSLowerProofs.FiniteCavityActualMarkedMomentInputs
