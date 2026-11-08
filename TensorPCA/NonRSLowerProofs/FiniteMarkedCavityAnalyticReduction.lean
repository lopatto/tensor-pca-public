-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteMarkedCavityAnalyticBudget
public import TensorPCA.NonRSLowerProofs.FiniteGaussianClippedCavityAveraging
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedRootedMoments

/-! Analytic reduction from errors in finitely many unconditional marked moments of the
hierarchy. Cavity size is chosen uniformly over hierarchies. Cutoffs, moment order
and tolerance precede the section space, one varying height family and the observed
population means. The conclusion reserves the population compensation clipping cost.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteMarkedCavityAnalyticReduction
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCS FiniteCSGaussianDepthMoment FiniteGaussianQuadraticStep FiniteGaussianQuadraticLogSteps
open FiniteGaussianClippedCavityAveraging FiniteMarkedCavityAnalyticBudget
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianClippedRootedMoments
open FiniteGaussianLinearLogSteps OneStepGaussianTiltEndpoint FiniteGaussianLogStepsCompression
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

theorem lower_of_finite_moment_errors (k : ℕ) (hk : 1≤k) {beta m error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1) (herror : 0<error) :
    ∀ᶠ M : ℕ in atTop,0<M ∧ ∃ LN b cap : ℝ,1≤LN ∧ 0<b ∧ b≤1 ∧ 1≤cap ∧
      ∃ n : ℕ,∃ delta : ℝ,0<delta ∧
      ∀(S : Type u) (VN : Type v) (VC : Type w) [MeasurableSpace S] [MeasurableSpace VN] [MeasurableSpace VC]
        (rho : Measure S) [IsProbabilityMeasure rho]
        (muN : Measure VN) [IsProbabilityMeasure muN] (muC : Measure VC) [IsProbabilityMeasure muC]
        (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (q : Fin (depth+2)→ℝ) (AN : VN→ℝ) (AC : VC→ℝ),
        Measurable x → (∀s j,0<x s j) → (∀s,StrictMono (x s)) → (∀s j,x s j≤1) →
        0≤q 0 → Monotone q → q (Fin.last (depth+1))=1 →
        Measurable AN → Measurable AC →
        (∀ᵐp∂muN,1≤AN p ∧ AN p≤LN) → (∀ᵐp∂muC,b≤AC p ∧ AC p≤cap) →
        let y := fun i : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k m) (q i)
        let z := fun i : Fin (depth+2) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
        let TN := fun j : Fin (depth+1) => shift M (increments y j)
        let TC := fun j : Fin (depth+1) => shift 1 (increments z j)
        (∀j<n,|(∫p,(1-AN p/LN)^(j+1) ∂muN)-
          (∫p : S×Model.Vector M,weightedMoment (depth+1) (j+1) (x p.1) 0 TN
            (fun h => 1-min (sphericalLaplace M h) LN/LN) (Real.sqrt (y 0) •p.2)
              ∂rho.prod (stdGaussian (Model.Vector M)))|≤delta) →
        (∀j<n,|(∫p,(1-AC p/cap)^(j+1) ∂muC)-
          (∫p : S×Model.Vector 1,weightedMoment (depth+1) (j+1) (x p.1) 0 TC
            (fun h => 1-max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap)/cap) (Real.sqrt (z 0) •p.2)
              ∂rho.prod (stdGaussian (Model.Vector 1)))|≤delta) →
        Integrable (fun p => Real.log (AN p)) muN ∧ Integrable (fun p => Real.log (AC p)) muC ∧
        beta*(rawValue k beta m).toReal/2-error+
          (2*Real.exp (9*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1))/2)/cap+
            2*b*Real.exp (2*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1))))/(M : ℝ)≤
          ((∫p,Real.log (AN p) ∂muN)-(∫p,Real.log (AC p) ∂muC))/(M : ℝ) := by
  have HT := clipped_cavity_lower_averaged k hk hbeta hm0 hm1 (half_pos herror)
  let YN := beta^2*deriv (Scalar.xiSlice k m) 1
  let YC := beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1)
  filter_upwards [HT] with M HM
  have hMr : (0 : ℝ)<M := by exact_mod_cast HM.1
  obtain ⟨LN,b,cap,hLN,hb,hb1,hcap,n,delta,hd,ha,ha1,hBudget⟩ :=
    exists_joint_budget M YN YC (show 0<(M : ℝ)*error/2 by positivity)
  let a := max (1-1/LN) (1-b/cap)
  refine ⟨HM.1,LN,b,cap,hLN,hb,hb1,hcap,n,delta,hd,?_⟩
  intro S VN VC _ _ _ rho _ muN _ muC _ depth x q AN AC hxs hx hxm hx1 hq0 hqm hqend hAN hAC hbAN hbAC
  dsimp only
  intro hMomN hMomC
  let y := fun i : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k m) (q i)
  let z := fun i : Fin (depth+2) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
  let TN := fun j : Fin (depth+1) => shift M (increments y j)
  let TC := fun j : Fin (depth+1) => shift 1 (increments z j)
  have HN := numerator_rooted_log_close HM.1 depth x hxs hx hxm hx1 TN hLN ha ha1 (le_max_left _ _)
    rho (Real.sqrt (y 0)) muN hAN hbAN n hMomN
  have hMomC' : ∀j<n,|(∫p,(1-AC p/cap)^(j+1) ∂muC)-
      (∫p : S×Model.Vector 1,weightedMoment (depth+1) (j+1) (x p.1) 0 TC
        (fun h => 1-max b (min (Real.exp (inner ℝ (scalarCoefficient M) h)) cap)/cap) (Real.sqrt (z 0) •p.2)
        ∂rho.prod (stdGaussian (Model.Vector 1)))|≤delta := by
    intro j hj
    simpa only [scalarCoefficient_inner] using hMomC j hj
  have HC := compensation_rooted_log_close depth x hxs hx hxm hx1 TC (scalarCoefficient M) hb hb1 hcap ha ha1 (le_max_right _ _)
    rho (Real.sqrt (z 0)) muC hAC hbAC n hMomC'
  let ON := ∫p,Real.log (AN p) ∂muN
  let OC := ∫p,Real.log (AC p) ∂muC
  let RN := ∫p : S×Model.Vector M,gaussianLogSteps (quadraticSteps M (x p.1) (increments y))
    (fun h => min (Real.log (sphericalLaplace M h)) (Real.log LN)) (Real.sqrt (y 0) •p.2) ∂rho.prod (stdGaussian (Model.Vector M))
  let RC := ∫p : S×Model.Vector 1,gaussianLogSteps (quadraticSteps 1 (x p.1) (increments z))
    (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt (z 0) •p.2) ∂rho.prod (stdGaussian (Model.Vector 1))
  let U := Real.exp (2*(M : ℝ)*YN)/LN
  let V := (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*YC)
  let W := 2*Real.exp (9*((M : ℝ)*YC)/2)/cap+2*b*Real.exp (2*((M : ℝ)*YC))
  let E := 2*(a^(n+1)/(1-a))+(n : ℝ)*delta
  have hN : |ON-RN|≤E := HN.2.2
  have hC : |OC-RC|≤E := by simpa only [scalarCoefficient_inner,TC,quadraticSteps,OC,RC,E,a] using HC.2.2
  have HRaw := HM.2 S rho depth x q LN b cap hxs hx hxm hx1 hq0 hqm hqend hLN hb hb1 hcap
  have HLower : beta*(rawValue k beta m).toReal/2-error/2-(U+V)/(M : ℝ)≤(RN-RC)/(M : ℝ) := by
    simpa only [sub_div] using HRaw.2.2
  have hMomentCost : RN-RC-2*E≤ON-OC := by
    have hNN := (abs_le.mp hN).1
    have hCC := (abs_le.mp hC).2
    linarith
  have HMom := div_le_div_of_nonneg_right hMomentCost hMr.le
  simp only [sub_div] at HMom
  have hBud : U+V+W+2*E≤(M : ℝ)*error/2 := hBudget
  have HCost : (U+V)/(M : ℝ)+W/(M : ℝ)+(2*E)/(M : ℝ)≤error/2 := by
    rw [←add_div,←add_div]
    apply (div_le_iff₀ hMr).mpr
    nlinarith only [hBud]
  refine ⟨HN.1,HC.1,?_⟩
  have HF : beta*(rawValue k beta m).toReal/2-error+W/(M : ℝ)≤(ON-OC)/(M : ℝ) :=
    by
      simp only [sub_div] at HLower ⊢
      linarith only [HLower,HMom,HCost]
  simpa only [W,YC,mul_assoc] using HF

end
end TensorPCA.NonRSLowerProofs.FiniteMarkedCavityAnalyticReduction
