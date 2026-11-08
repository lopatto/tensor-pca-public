-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianReplicaTransportProofs
public import TensorPCA.GaussianReplicaMomentProofs
public import TensorPCA.GaussianMaximumComparisonProofs

/-! Literal single-channel representation of the two-channel Bayesian interpolation, for dimension-free covariance-kernel comparison. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityComparisonProofs
open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs GaussianSideChannelProofs
open GaussianTwoChannelFreeEnergyProofs GaussianReplicaTransportProofs GaussianReplicaMomentProofs GaussianCompactFeatureComparison
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega iota kappa : Type*} [MeasurableSpace Omega] [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]

def joinedSignal (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa) :
    Omega → EuclideanSpace ℝ (iota ⊕ kappa) := fun x ↦ sumJoin (A x,B x)

def joinedOutput (p : EuclideanSpace ℝ kappa × EuclideanSpace ℝ iota) : EuclideanSpace ℝ (iota ⊕ kappa) :=
  sumJoin (p.2,p.1)

theorem measurable_joinedSignal (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) : Measurable (joinedSignal A B) :=
  sumJoin.continuous.measurable.comp (hA.prodMk hB)

theorem continuous_joinedOutput : Continuous (joinedOutput (iota := iota) (kappa := kappa)) :=
  sumJoin.continuous.comp (continuous_snd.prodMk continuous_fst)

theorem inner_sumJoin (v v' : EuclideanSpace ℝ iota) (w w' : EuclideanSpace ℝ kappa) :
    inner ℝ (sumJoin (v,w)) (sumJoin (v',w')) = inner ℝ v v'+inner ℝ w w' := by
  simp only [sumJoin,PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

theorem norm_sumJoin_sq (v : EuclideanSpace ℝ iota) (w : EuclideanSpace ℝ kappa) :
    ‖sumJoin (v,w)‖^2 = ‖v‖^2+‖w‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_sumJoin v v w w

theorem mixtureWeight_join (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (p : EuclideanSpace ℝ kappa × EuclideanSpace ℝ iota) (x : Omega) :
    mixtureWeight (joinedSignal A B x) (joinedOutput p) = mixtureWeight (A x) p.2*mixtureWeight (B x) p.1 := by
  simp only [mixtureWeight,joinedSignal,joinedOutput,inner_sumJoin,norm_sumJoin_sq,← Real.exp_add]
  congr 1
  ring

theorem mixtureLikelihood_join (mu : Measure Omega) (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (p : EuclideanSpace ℝ kappa × EuclideanSpace ℝ iota) :
    mixtureLikelihood mu (joinedSignal A B) (joinedOutput p) = combinedLikelihood mu A B p.2 p.1 := by
  unfold mixtureLikelihood combinedLikelihood
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (mixtureWeight_join A B p)

theorem posteriorKernel_join (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) (p : EuclideanSpace ℝ kappa × EuclideanSpace ℝ iota) :
    posteriorKernel mu (joinedSignal A B) (joinedOutput p) = combinedPosteriorKernel mu A B p := by
  rw [posteriorKernel_apply mu _ (measurable_joinedSignal A B hA hB),combinedPosteriorKernel,
    Kernel.withDensity_apply _ (measurable_combinedPosteriorWeight mu A B hA hB),Kernel.const_apply]
  congr 1
  funext x
  congr 1
  simp only [posteriorWeight,combinedPosteriorWeight,mixtureLikelihood_join,mixtureWeight_join]
  ring

theorem sumJoin_gaussian_map :
    ((stdGaussian (EuclideanSpace ℝ iota)).prod (stdGaussian (EuclideanSpace ℝ kappa))).map sumJoin =
      stdGaussian (EuclideanSpace ℝ (iota ⊕ kappa)) := by
  have hs : (stdGaussian (EuclideanSpace ℝ (iota ⊕ kappa))).map sumSplit =
      (stdGaussian (EuclideanSpace ℝ iota)).prod (stdGaussian (EuclideanSpace ℝ kappa)) := by
    simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using
      (sumSplit_gaussian_map (ι := iota) (κ := kappa))
  have heq : (sumJoin : EuclideanSpace ℝ iota × EuclideanSpace ℝ kappa →L[ℝ] _) ∘ sumSplit = id := by
    funext w
    ext (i | j) <;> rfl
  rw [← hs,Measure.map_map sumJoin.continuous.measurable sumSplit.continuous.measurable,heq,Measure.map_id]

theorem joinedOutput_gaussian_map :
    ((stdGaussian (EuclideanSpace ℝ kappa)).prod (stdGaussian (EuclideanSpace ℝ iota))).map joinedOutput =
      stdGaussian (EuclideanSpace ℝ (iota ⊕ kappa)) := by
  change ((stdGaussian (EuclideanSpace ℝ kappa)).prod (stdGaussian (EuclideanSpace ℝ iota))).map
    (sumJoin ∘ Prod.swap) = _
  rw [← Measure.map_map sumJoin.continuous.measurable measurable_swap,Measure.prod_swap,sumJoin_gaussian_map]

theorem joinedExperiment_gaussian_map (mu : Measure Omega) [IsProbabilityMeasure mu] :
    (((mu.prod (stdGaussian (EuclideanSpace ℝ kappa))).prod (stdGaussian (EuclideanSpace ℝ iota)))).map
      (fun z ↦ (z.1.1,joinedOutput (z.1.2,z.2))) =
      mu.prod (stdGaussian (EuclideanSpace ℝ (iota ⊕ kappa))) := by
  change (((mu.prod (stdGaussian (EuclideanSpace ℝ kappa))).prod (stdGaussian (EuclideanSpace ℝ iota)))).map
    (Prod.map id joinedOutput ∘ MeasurableEquiv.prodAssoc) = _
  rw [← Measure.map_map (measurable_id.prodMap continuous_joinedOutput.measurable) MeasurableEquiv.prodAssoc.measurable,
    (measurePreserving_prodAssoc _ _ _).map_eq,
    ← Measure.map_prod_map _ _ measurable_id continuous_joinedOutput.measurable,Measure.map_id,joinedOutput_gaussian_map]

theorem pairObservationLaw_join (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) :
    (pairObservationLaw mu A B).map joinedOutput = mixtureLaw mu (joinedSignal A B) := by
  have hObs : Measurable (fun z : (Omega × EuclideanSpace ℝ kappa) × EuclideanSpace ℝ iota ↦
      (B z.1.1+z.1.2,A z.1.1+z.2)) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk ((hA.comp measurable_fst.fst).add measurable_snd)
  have hJoint : Measurable (fun z : (Omega × EuclideanSpace ℝ kappa) × EuclideanSpace ℝ iota ↦
      (z.1.1,joinedOutput (z.1.2,z.2))) :=
    measurable_fst.fst.prodMk (continuous_joinedOutput.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  have hNewObs : Measurable (fun z : Omega × EuclideanSpace ℝ (iota ⊕ kappa) ↦ joinedSignal A B z.1+z.2) :=
    ((measurable_joinedSignal A B hA hB).comp measurable_fst).add measurable_snd
  unfold pairObservationLaw mixtureLaw
  rw [Measure.map_map continuous_joinedOutput.measurable hObs,← joinedExperiment_gaussian_map mu,
    Measure.map_map hNewObs hJoint]
  congr 1
  funext z
  change sumJoin (A z.1.1+z.2,B z.1.1+z.1.2) = sumJoin (A z.1.1,B z.1.1)+sumJoin (z.2,z.1.2)
  rw [← map_add]
  rfl

theorem combinedMean_join {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) (C : Omega → V) (p : EuclideanSpace ℝ kappa × EuclideanSpace ℝ iota) :
    combinedMean mu A B C p = posteriorMean mu (joinedSignal A B) C (joinedOutput p) := by
  unfold combinedMean posteriorMean
  rw [posteriorKernel_join mu A B hA hB]

theorem combinedMean_secondMoment_join {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) (C : Omega → V) (hC : StronglyMeasurable C) :
    (∫ p, ‖combinedMean mu A B C p‖^2 ∂pairObservationLaw mu A B) =
      ∫ y, ‖posteriorMean mu (joinedSignal A B) C y‖^2 ∂mixtureLaw mu (joinedSignal A B) := by
  have hm := (GaussianPosteriorCovarianceProofs.stronglyMeasurable_posteriorMean mu (joinedSignal A B) C hC).norm.measurable.pow_const 2
  rw [← pairObservationLaw_join mu A B hA hB,integral_map continuous_joinedOutput.measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p ↦ congrArg (fun v : V ↦ ‖v‖^2) (combinedMean_join mu A B hA hB C p))

end
end TensorPCA.FinitePriorCavityComparisonProofs
