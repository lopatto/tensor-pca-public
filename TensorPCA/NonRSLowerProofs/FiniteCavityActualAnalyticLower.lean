-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteMarkedCavityAnalyticReduction
public import TensorPCA.NonRSLowerProofs.FiniteCavityActualPopulationClipping

/-! The fixed-bulk population lower criterion for the ASS means, Gaussian banks and
amplitude cube. Analytic evaluation and log integrability are proved here; two
finite marked-moment errors enter the physical GG/tree argument.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityActualAnalyticLower
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation GaussianCompactFeatureComparison
open FiniteCS FiniteCSGaussianDepthMoment FiniteGaussianQuadraticStep
open FiniteMarkedCavityAnalyticReduction FiniteCavityActualPopulationClipping
open FiniteCavityNumeratorMoments FiniteCavityGaussianCompatibility FiniteCavityPerturbedFields
open FiniteNestedGaussianMarkedMoments OneStepGaussianTiltEndpoint
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem fixed_bulk_lower_of_moment_errors (k : ℕ) (hk : 1≤k) {beta m error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1) (he : 0<error) :
    ∀ᶠ M : ℕ in atTop,0<M ∧ ∃ LN b cap : ℝ,1≤LN ∧ 0<b ∧ b≤1 ∧ 1≤cap ∧
      ∃ n : ℕ,∃ delta : ℝ,0<delta ∧
      ∀(N K : ℕ) (hN : 0<N) (strength : ℝ) (gB : GroundState.Disorder N k)
        (depth : ℕ) (x : (Fin K→ℝ)→Fin (depth+1)→ℝ) (q : Fin (depth+2)→ℝ),
        Measurable x → (∀s j,0<x s j) → (∀s,StrictMono (x s)) → (∀s j,x s j≤1) →
        0≤q 0 → Monotone q → q (Fin.last (depth+1))=1 →
        let y := fun i : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k m) (q i)
        let z := fun i : Fin (depth+2) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
        let TN := fun j : Fin (depth+1) => shift M (increments y j)
        let TC := fun j : Fin (depth+1) => shift 1 (increments z j)
        let d := (positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        let muN := d.prod (stdGaussian (CavityDisorder N M k))
        let muC := d.prod (stdGaussian (GroundState.Disorder N k))
        let AN := fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k =>
          ∫s,min (numeratorMark k m beta p.2 s) LN
            ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))
        let AC := fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k =>
          ∫s,max b (min (Real.exp (inner ℝ
            (limitingCompensatorFeature M (fun j : Fin k => (j : ℕ)+1)
              (fun j => beta^2*VariationalProofs.sliceCoefficient k m j) s) p.2)) cap)
            ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))
        (∀j<n,|(∫p,(1-AN p/LN)^(j+1) ∂muN)-
          (∫p : (Fin K→ℝ)×Model.Vector M,weightedMoment (depth+1) (j+1) (x p.1) 0 TN
            (fun h => 1-min (sphericalLaplace M h) LN/LN) (Real.sqrt (y 0) •p.2)
              ∂(positiveCubeLaw K).prod (stdGaussian (Model.Vector M)))|≤delta) →
        (∀j<n,|(∫p,(1-AC p/cap)^(j+1) ∂muC)-
          (∫p : (Fin K→ℝ)×Model.Vector 1,weightedMoment (depth+1) (j+1) (x p.1) 0 TC
            (fun h => 1-max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap)/cap) (Real.sqrt (z 0) •p.2)
              ∂(positiveCubeLaw K).prod (stdGaussian (Model.Vector 1)))|≤delta) →
        beta*(rawValue k beta m).toReal/2-error≤
          ((∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k,
            Real.log (∫s,numeratorMark k m beta p.2 s
              ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))) ∂muN)-
           (∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k,
            Real.log (∫s,Real.exp (inner ℝ
              (limitingCompensatorFeature M (fun j : Fin k => (j : ℕ)+1)
                (fun j => beta^2*VariationalProofs.sliceCoefficient k m j) s) p.2)
              ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))) ∂muC))/(M : ℝ) := by
  have HT := lower_of_finite_moment_errors k hk hbeta hm0 hm1 he
  filter_upwards [HT] with M HM
  obtain ⟨hM,LN,b,cap,hLN,hb,hb1,hcap,n,delta,hd,hCriterion⟩ := HM
  refine ⟨hM,LN,b,cap,hLN,hb,hb1,hcap,n,delta,hd,?_⟩
  intro N K hN strength gB depth x q hxs hx hxm hx1 hq0 hqm hqend
  dsimp only
  intro hMomN hMomC
  let d := (positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
  let muN := d.prod (stdGaussian (CavityDisorder N M k))
  let muC := d.prod (stdGaussian (GroundState.Disorder N k))
  let AN := fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k =>
    ∫s,min (numeratorMark k m beta p.2 s) LN ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))
  let AC := fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k =>
    ∫s,max b (min (Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k => (j : ℕ)+1)
        (fun j => beta^2*VariationalProofs.sliceCoefficient k m j) s) p.2)) cap)
      ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))
  obtain ⟨hAN,hBN,hAC,hBC⟩ := actual_clipped_means_facts (N := N) (M := M) (k := k) (K := K) (mu := m)
    hN hM beta strength gB hLN hb hb1 hcap
  have H := hCriterion (Fin K→ℝ)
    (((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k)
    (((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k)
    (positiveCubeLaw K) muN muC depth x q AN AC hxs hx hxm hx1 hq0 hqm hqend hAN hAC
    (ae_of_all _ hBN) (ae_of_all _ hBC) hMomN hMomC
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  have HC := actual_population_clipping_control (N := N) (M := M) (k := k) (K := K) (mu := m)
    hN hM beta strength gB hm hLN hb hb1 hcap
  let CN := ∫p,Real.log (AN p) ∂muN
  let CC := ∫p,Real.log (AC p) ∂muC
  let RN := ∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k,
    Real.log (∫s,numeratorMark k m beta p.2 s
      ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))) ∂muN
  let RC := ∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k,
    Real.log (∫s,Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k => (j : ℕ)+1)
        (fun j => beta^2*VariationalProofs.sliceCoefficient k m j) s) p.2)
      ∂perturbedBulkGibbs N M k K m beta strength p.1.1 (sumJoin (gB,p.1.2))) ∂muC
  let W := 2*Real.exp (9*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1))/2)/cap+
    2*b*Real.exp (2*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1)))
  have HClip : beta*(rawValue k beta m).toReal/2-error+W/(M : ℝ)≤(CN-CC)/(M : ℝ) := H.2.2
  have HNum : 0≤RN-CN := HC.2.2.2.2.1
  have HComp : RC-CC≤W := HC.2.2.2.2.2
  have HRaw : CN-CC-W≤RN-RC := by linarith only [HNum,HComp]
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have HD : (CN-CC)/(M : ℝ)-W/(M : ℝ)≤(RN-RC)/(M : ℝ) := by
    simpa only [sub_div] using div_le_div_of_nonneg_right HRaw hMr.le
  change beta*(rawValue k beta m).toReal/2-error≤(RN-RC)/(M : ℝ)
  linarith only [HClip,HD]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityActualAnalyticLower
