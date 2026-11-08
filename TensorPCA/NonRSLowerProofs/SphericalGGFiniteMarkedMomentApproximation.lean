-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGCompensatorMarkedMoments
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeLawPhysicalFamily
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteMomentMesh

/-! Simultaneous finite marked-moment matching. One mesh, one coherent family and one
height vector determined by the same amplitude pair law serve both physical marks
and every requested replica count. GG, coarsening and negativity error budgets are
fixed before the physical model is chosen.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteMarkedMomentApproximation
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open SphericalFirstJetPowerBudget
open SphericalGGWeightObservable SphericalGGTreeHeights SphericalGGSelectedOwnHeights
open SphericalGGObservedMarkedMoments SphericalGGCompensatorMarkedMoments
open SphericalGGTreeLawPhysicalFamily SphericalGGFiniteMomentMesh
open FiniteGGPositiveGrid FiniteGGProductCutMasks FiniteGGParameterScorePartition FiniteGGBoundaryBands
open FiniteGGPrechosenPolynomialFamily FiniteGGMonotoneBoundaryCuts
open FiniteNestedGaussianMarkedMoments FiniteCavityIdealField FiniteCavityShellGibbsPartition
open FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility GaussianCompactFeatureComparison
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_uniform_actual_marked_moments (R M k : ℕ) (hR : 0<R) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (markN : Model.Vector M→ℝ) (hMarkN : Continuous markN) (hBoundN : ∀z,markN z∈Icc (0 : ℝ) 1)
    (markC : ℝ→ℝ) (hMarkC : Continuous markC) (hBoundC : ∀z,markC z∈Icc (0 : ℝ) 1)
    {eps : ℝ} (heps : 0<eps) :
    ∃ depth : ℕ,0<depth ∧ ∃ Q : ℕ,∀K : ℕ,Q≤K → ∃ V : ℝ,∃ hV : 1≤V,
      ∀ {N : ℕ},0<N → ∀ (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
        (v : ℝ) (hv : V≤v),
      let hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
      letI := parameterizedGibbsKernel_markov (K := K) nu hv0
      let yN := fun l : Fin (depth+1) ↦ beta^2*deriv (Scalar.xiSlice k mu) (grid depth l)
      let yC := fun l : Fin (depth+1) ↦ beta^2*(grid depth l*deriv (Scalar.xiSlice k mu) (grid depth l)-Scalar.xiSlice k mu (grid depth l))
      ∃ x : (Fin K→ℝ)→Fin depth→ℝ,Measurable x ∧ (∀amp l,0<x amp l) ∧
        (∀amp,StrictMono (x amp)) ∧ (∀amp l,x amp l≤1) ∧ ∀r : Fin R,
      |(∫q,(∫g : CavityDisorder N M k,∏i : Fin (r.val+1),markN (blockField k mu beta g (q.2 i).val)
          ∂stdGaussian (CavityDisorder N M k)) ∂jointLaw (K := K) nu v r.val)-
        (∫amp,∫g : Model.Vector M,weightedMoment depth (r.val+1) (x amp) 0
          (fun j : Fin depth ↦ Real.sqrt (yN j.succ-yN j.castSucc) •ContinuousLinearMap.id ℝ _)
          markN (Real.sqrt (yN 0) •g) ∂stdGaussian (Model.Vector M) ∂positiveCubeLaw K)|≤eps ∧
      |(∫q,(∫g : GroundState.Disorder N k,∏i : Fin (r.val+1),markC (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (q.2 i).val) g)
          ∂stdGaussian (GroundState.Disorder N k)) ∂jointLaw (K := K) nu v r.val)-
        (∫amp,∫g : Model.Vector 1,weightedMoment depth (r.val+1) (x amp) 0
          (fun j : Fin depth ↦ Real.sqrt (yC j.succ-yC j.castSucc) •ContinuousLinearMap.id ℝ _)
          (fun z : Model.Vector 1 ↦ markC (Real.sqrt (M : ℝ)*z 0)) (Real.sqrt (yC 0) •g)
          ∂stdGaussian (Model.Vector 1) ∂positiveCubeLaw K)|≤eps := by
  classical
  have hQuarter : 0<eps/4 := by positivity
  have hQuarterSum {a b c : ℝ} (ha : a≤eps/4) (hb : b≤eps/4) (hc : c≤eps/4) :
      eps/4+a+b+c≤eps := by linarith only [ha,hb,hc]
  choose deltaN hDN hNMain using (fun r : Fin R ↦
    exists_selected_numerator_strict_moment r.val M k hmu beta markN hMarkN hBoundN hQuarter)
  choose deltaC hDC hCMain using (fun r : Fin R ↦
    exists_selected_compensator_strict_moment r.val M k hmu beta markC hMarkC hBoundC hQuarter)
  obtain ⟨depth,hd,neg,hNeg,hNeg1,hMesh⟩ := exists_common_grid_mesh R hR deltaN deltaC hDN hDC
  have hLeft (l : Fin depth) : -1<cutLeft depth l := by linarith only [(cut_interval hd l).1]
  have hInterval (l : Fin depth) : cutLeft depth l<cutRight depth l := (cut_interval hd l).2.1
  have hRight (l : Fin depth) : cutRight depth l≤1 := (cut_interval hd l).2.2.le
  have hSep (i j : Fin depth) (hij : i<j) : cutRight depth i≤cutLeft depth j := cut_intervals_separated hd i j hij
  obtain ⟨tau,htau,htau1,eta,hEta,hEta1,_,J,hJ,hBudget,P,Q,hDegree,hApprox,hGlobal,hFamily⟩ :=
    exists_uniform_physical_tree_law_family R depth hR (cutLeft depth) (cutRight depth)
      hLeft hInterval hRight hSep hQuarter hQuarter hQuarter (by norm_num : (0 : ℝ)<1) hNeg
  refine ⟨depth,hd,Q,?_⟩
  intro K hK
  obtain ⟨V,hV,hModel⟩ := hFamily K hK
  refine ⟨V,hV,?_⟩
  intro N hN nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hv0
  dsimp only
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := parameterizedGibbsKernel (K := K) nu v
  let good := fun l ↦ goodParameter d G unitOverlap (cutLeft depth l) (cutRight depth l) J (P l) eta
  let cell := cutCell good
  let cuts := fun (index : Fin depth→Fin J) l ↦ threshold (cutLeft depth l) (cutRight depth l) J (index l)
  have hCuts (index) : Monotone (cuts index) :=
    (threshold_vector_strictMono (cutLeft depth) (cutRight depth) hInterval hSep index).monotone
  have hCutsGrid (index) (l) : cuts index l∈Ioo (cutLeft depth l) (cutRight depth l) :=
    threshold_mem (hInterval l) J (index l)
  obtain ⟨hCell,hDis,hCover,_,_,_⟩ := product_parameter_partition d G (unitOverlap_measurable N)
    unitOverlap_mem_Icc (cutLeft depth) (cutRight depth) (fun _ ↦ eta) hInterval hJ
    (fun _ ↦ hBudget) P hApprox hGlobal
  let x := selectedOwnHeights nu v cell cuts tau
  have hxs : Measurable x := selectedOwnHeights_measurable nu hv0 cell cuts tau hCell
  have hx : ∀amp l,0<x amp l := selectedOwnHeights_positive nu hv0 cell cuts htau htau1 hDis hCover
  have hxm : ∀amp,StrictMono (x amp) := selectedOwnHeights_strictMono nu hv0 cell cuts htau htau1 hCuts hDis hCover
  have hx1 : ∀amp l,x amp l≤1 := selectedOwnHeights_le_one nu hv0 cell cuts htau htau1 hDis hCover
  refine ⟨x,hxs,hx,hxm,hx1,?_⟩
  intro r
  have hSmall := hModel nu v hv (r.val+1) (by omega : 0<r.val+1) (by omega : r.val+1≤R)
  have HN := hNMain r hd cuts hCuts hCutsGrid nu v hv0 cell hCell hDis hCover
    tau htau htau1 neg hNeg.le (hMesh r).1
  have HC := hCMain r hN hd cuts hCuts hCutsGrid nu v hv0 cell hCell hDis hCover
    tau htau htau1 neg hNeg.le (hMesh r).2
  dsimp only at HN HC hSmall
  simp only [Nat.add_sub_cancel,unitOverlap] at hSmall
  dsimp only [x,cell,cuts,good,d,G] at HN HC hSmall ⊢
  have hCost := hQuarterSum hSmall.2.1 hSmall.2.2 hSmall.1
  exact ⟨HN.trans hCost,HC.trans hCost⟩

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteMarkedMomentApproximation
