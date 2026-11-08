-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityActualMarkedMomentInputs
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteMarkedMomentApproximation

/-! Population moments under the perturbed bulk prior match one selected hierarchy for
both cavity marks and all requested orders. Its heights are computed from the same
amplitude-dependent Gaussian pair law. Thresholds are chosen before the bulk
dimension and disorder.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityActualMarkedMoments
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable SphericalGGFiniteMarkedMomentApproximation
open FiniteCavityActualMarkedMomentInputs FiniteCavityBulkUnitSpinPrior FiniteCavityPerturbedFields
open FiniteCavityNumeratorMoments FiniteCavityShellGibbsPartition
open OneStepGaussianTiltEndpoint FiniteCavityGaussianCompatibility
open FiniteCavityCompensationThetaComparison GaussianCompactFeatureComparison
open FiniteNestedGaussianMarkedMoments FiniteNestedMarkedMomentMeasurability FiniteGGPositiveGrid
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rooted_weightedMoment_integrable {E S : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S]
    (rho : Measure S) [IsProbabilityMeasure rho] (depth n : ℕ)
    (x : S→Fin depth→ℝ) (hxs : Measurable x) (hx : ∀s j,0<x s j)
    (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z)
    (hb : ∀z,Z z∈Icc (0 : ℝ) 1) (scale : ℝ) :
    Integrable (fun p : S×E => weightedMoment depth n (x p.1) 0 T Z (scale •p.2))
      (rho.prod (stdGaussian E)) := by
  have HM := weightedMoment_params_joint_measurable depth n T hZ x
    (fun _ : S => (0 : ℝ)) hxs measurable_const
  have hInput : Measurable (fun p : S×E => (p.1,scale •p.2)) :=
    measurable_fst.prodMk (measurable_const.smul measurable_snd)
  apply Integrable.of_bound (HM.comp hInput).aestronglyMeasurable 1
  exact ae_of_all _ (fun p => by
    have H := weightedMoment_mem depth n (x p.1) 0 le_rfl (hx p.1) (hxm p.1) (hx1 p.1)
      T hZ zero_le_one hb (scale •p.2)
    change ‖weightedMoment depth n (x p.1) 0 T Z (scale •p.2)‖≤1
    rw [Real.norm_of_nonneg H.1]
    simpa only [one_pow] using H.2)

theorem exists_actual_population_marked_moments (M k n : ℕ) (hM : 0<M)
    {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {LN b cap : ℝ}
    (hLN : 1≤LN) (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap)
    {eps : ℝ} (heps : 0<eps) :
    ∃ depth Q : ℕ,∀K : ℕ,Q≤K → ∃V : ℝ,∃hV : 1≤V,
      ∀ {N : ℕ},0<N → ∀(gB : GroundState.Disorder N k) (v : ℝ),V≤v →
      let y := fun l : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k mu) (grid (depth+1) l)
      let z := fun l : Fin (depth+2) => grid (depth+1) l*y l-beta^2*Scalar.xiSlice k mu (grid (depth+1) l)
      let TN := fun j : Fin (depth+1) => Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ (Model.Vector M)
      let TC := fun j : Fin (depth+1) => Real.sqrt (z j.succ-z j.castSucc) •ContinuousLinearMap.id ℝ (Model.Vector 1)
      ∃x : (Fin K→ℝ)→Fin (depth+1)→ℝ,Measurable x ∧ (∀amp l,0<x amp l) ∧
        (∀amp,StrictMono (x amp)) ∧ (∀amp l,x amp l≤1) ∧ ∀j<n,
      |(∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k,
          (1-(∫s,min (numeratorMark k mu beta p.2 s) LN
            ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))/LN)^(j+1)
          ∂((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
            (stdGaussian (CavityDisorder N M k)))-
        (∫p : (Fin K→ℝ)×Model.Vector M,weightedMoment (depth+1) (j+1) (x p.1) 0 TN
          (fun h => 1-min (sphericalLaplace M h) LN/LN) (Real.sqrt (y 0) •p.2)
          ∂(positiveCubeLaw K).prod (stdGaussian (Model.Vector M)))|≤eps ∧
      |(∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k,
          (1-(∫s,max b (min (Real.exp (inner ℝ
            (limitingCompensatorFeature M (fun l : Fin k => l.val+1)
              (fun l => beta^2*VariationalProofs.sliceCoefficient k mu l) s) p.2)) cap)
            ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))/cap)^(j+1)
          ∂((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
            (stdGaussian (GroundState.Disorder N k)))-
        (∫p : (Fin K→ℝ)×Model.Vector 1,weightedMoment (depth+1) (j+1) (x p.1) 0 TC
          (fun h => 1-max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap)/cap) (Real.sqrt (z 0) •p.2)
          ∂(positiveCubeLaw K).prod (stdGaussian (Model.Vector 1)))|≤eps := by
  let markN := fun h : Model.Vector M => 1-min (sphericalLaplace M h) LN/LN
  let markC := fun s : ℝ => 1-max b (min (Real.exp s) cap)/cap
  have hNCont : Continuous markN := numerator_deficit_continuous hM LN
  have hNBound : ∀h,markN h∈Icc (0 : ℝ) 1 := numerator_deficit_mem_Icc hM hLN
  have hCCont : Continuous markC := compensation_deficit_continuous b cap
  have hCBound : ∀s,markC s∈Icc (0 : ℝ) 1 := compensation_deficit_mem_Icc hb hb1 hcap
  obtain ⟨D,hD,Q,hModel⟩ := exists_uniform_actual_marked_moments (n+1) M k
    (Nat.zero_lt_succ n) hmu beta markN hNCont hNBound markC hCCont hCBound heps
  obtain ⟨depth,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
  refine ⟨depth,Q,?_⟩
  intro K hK
  obtain ⟨V,hV,hAll⟩ := hModel K hK
  refine ⟨V,hV,?_⟩
  intro N hN gB v hv
  letI := bulkPriorKernel_probability hN M k mu beta gB
  have hv0 : 0≤v := zero_le_one.trans (hV.trans hv)
  obtain ⟨x,hxs,hx,hxm,hx1,hMom⟩ := hAll hN (bulkPriorKernel N M k mu beta gB) v hv
  dsimp only
  refine ⟨x,hxs,hx,hxm,hx1,?_⟩
  intro j hj
  have H := hMom ⟨j,by omega⟩
  dsimp only at H
  have hTheta (r : ℝ) : beta^2*(r*deriv (Scalar.xiSlice k mu) r-Scalar.xiSlice k mu r)=
      r*(beta^2*deriv (Scalar.xiSlice k mu) r)-beta^2*Scalar.xiSlice k mu r := by ring
  simp_rw [hTheta] at H
  let y := fun l : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k mu) (grid (depth+1) l)
  let z := fun l : Fin (depth+2) => grid (depth+1) l*y l-beta^2*Scalar.xiSlice k mu (grid (depth+1) l)
  let TN := fun l : Fin (depth+1) => Real.sqrt (y l.succ-y l.castSucc) •ContinuousLinearMap.id ℝ (Model.Vector M)
  let TC := fun l : Fin (depth+1) => Real.sqrt (z l.succ-z l.castSucc) •ContinuousLinearMap.id ℝ (Model.Vector 1)
  have HN := actual_bulk_clipped_product_moment_eq_jointLaw hN M k K mu beta hv0 gB
    (stdGaussian (CavityDisorder N M k)) j (Y := numeratorMark k mu beta)
    (numeratorMark_joint_measurable N M k mu beta) (b := 1) (by norm_num) le_rfl hLN
  have hMax (g : CavityDisorder N M k) (s : Model.Vector N) :
      max 1 (min (numeratorMark k mu beta g s) LN)=min (numeratorMark k mu beta g s) LN :=
    max_eq_right (le_min (numeratorMark_one_le hM k mu beta g s) hLN)
  simp_rw [hMax] at HN
  have HNobs := HN.2
  simp_rw [numeratorMark_eq_sphericalLaplace] at HNobs
  have hF := (thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable
  have hY : Measurable (fun p : GroundState.Disorder N k×Model.Vector N => Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun l : Fin k => l.val+1)
        (fun l => beta^2*VariationalProofs.sliceCoefficient k mu l) p.2) p.1)) :=
    (continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)).exp
  have HC := actual_bulk_clipped_product_moment_eq_jointLaw hN M k K mu beta hv0 gB
    (stdGaussian (GroundState.Disorder N k)) j
    (Y := fun g (s : Model.Vector N) => Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun l : Fin k => l.val+1)
        (fun l => beta^2*VariationalProofs.sliceCoefficient k mu l) s) g))
    hY hb hb1 hcap
  have hIN := rooted_weightedMoment_integrable (positiveCubeLaw K) (depth+1) (j+1)
    x hxs hx hxm hx1 TN hNCont.measurable hNBound (Real.sqrt (y 0))
  have hCVector : Continuous (fun h : Model.Vector 1 => markC (Real.sqrt (M : ℝ)*h 0)) :=
    hCCont.comp (show Continuous (fun h : Model.Vector 1 => Real.sqrt (M : ℝ)*h 0) by fun_prop)
  have hIC := rooted_weightedMoment_integrable (positiveCubeLaw K) (depth+1) (j+1)
    x hxs hx hxm hx1 TC hCVector.measurable
    (fun h : Model.Vector 1 => hCBound (Real.sqrt (M : ℝ)*h 0)) (Real.sqrt (z 0))
  have hRootN := integral_prod _ hIN
  have hRootC := integral_prod _ hIC
  have HNum := H.1
  have HComp := H.2
  dsimp only [markN,markC] at HNum HComp hRootN hRootC
  rw [←HNobs,←hRootN] at HNum
  rw [←HC.2,←hRootC] at HComp
  constructor
  · simpa only [numeratorMark_eq_sphericalLaplace] using HNum
  · exact HComp

end
end TensorPCA.NonRSLowerProofs.FiniteCavityActualMarkedMoments
