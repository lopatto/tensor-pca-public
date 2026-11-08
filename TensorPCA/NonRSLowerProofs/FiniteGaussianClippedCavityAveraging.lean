-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyClippedCavityLower
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedVariableHeights

/-! Average the clipped cavity lower bound using one section-dependent height family.
Only bounded clipped towers are averaged; joint measurability and integrability
follow from the marked root series.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianClippedCavityAveraging
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCS FiniteCSGaussianDepthMoment FiniteGaussianHierarchyClippedCavityLower
open FiniteNestedGaussianMarkedTransforms FiniteNestedGaussianMarkedValues
open FiniteNestedGaussianMarkedVariableHeights FiniteNestedGaussianSphericalClipping
open FiniteNestedGaussianCompensationClipping FiniteGaussianQuadraticLogSteps FiniteGaussianQuadraticStep
open FiniteGaussianLogStepsCompression OneStepGaussianTiltEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem rooted_clipped_integrable {N : ℕ} {S : Type u} [MeasurableSpace S]
    (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→Model.Vector N→L[ℝ]Model.Vector N) {Z : Model.Vector N→ℝ}
    (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (ha1 : a<1) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (B : S×Model.Vector N→ℝ) (C scale : ℝ)
    (hBridge : ∀p,rootLog depth (x p.1) T Z 1 p.2=B p-C)
    (rho : Measure S) [IsProbabilityMeasure rho] :
    Integrable (fun p : S×Model.Vector N => B (p.1,scale •p.2)) (rho.prod (stdGaussian (Model.Vector N))) := by
  have hm := rootLog_params_measurable depth x hxs hx hxm hx1 T hZ ha ha1 hb
  have hInput : Measurable (fun p : S×Model.Vector N => (p.1,scale •p.2)) := by fun_prop
  have hi : Integrable (fun p : S×Model.Vector N => rootLog depth (x p.1) T Z 1 (scale •p.2))
      (rho.prod (stdGaussian (Model.Vector N))) := by
    apply Integrable.of_bound (hm.comp hInput).aestronglyMeasurable (a/(1-a))
    exact ae_of_all _ (fun p => by
      have H := root_polynomial_error_le depth (x p.1) (hx p.1) (hxm p.1) (hx1 p.1) T hZ ha ha1 hb (scale •p.2) 0
      simpa only [Function.comp_apply,Finset.sum_range_zero,zero_sub,abs_neg,neg_neg,Nat.zero_add,pow_one,Real.norm_eq_abs] using H)
  apply (hi.add (integrable_const C)).congr
  exact ae_of_all _ (fun p => by
    have H := hBridge (p.1,scale •p.2)
    dsimp only at H
    simp only [Pi.add_apply]
    linarith only [H])

theorem clipped_cavity_lower_averaged (k : ℕ) (hk : 1≤k) {beta m error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1) (herror : 0<error) :
    ∀ᶠ M : ℕ in atTop,0<M ∧ ∀(S : Type u) [MeasurableSpace S]
      (rho : Measure S) [IsProbabilityMeasure rho] (depth : ℕ)
      (x : S→Fin (depth+1)→ℝ) (q : Fin (depth+2)→ℝ) (LN b cap : ℝ),
      Measurable x → (∀s j,0<x s j) → (∀s,StrictMono (x s)) → (∀s j,x s j≤1) →
      0≤q 0 → Monotone q → q (Fin.last (depth+1))=1 →
      1≤LN → 0<b → b≤1 → 1≤cap →
      let y := fun i : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k m) (q i)
      let z := fun i : Fin (depth+2) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
      let A := fun p : S×Model.Vector M => gaussianLogSteps (quadraticSteps M (x p.1) (increments y))
        (fun h => min (Real.log (sphericalLaplace M h)) (Real.log LN)) (Real.sqrt (y 0) •p.2)
      let B := fun p : S×Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 (x p.1) (increments z))
        (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt (z 0) •p.2)
      Integrable A (rho.prod (stdGaussian (Model.Vector M))) ∧
      Integrable B (rho.prod (stdGaussian (Model.Vector 1))) ∧
      beta*(rawValue k beta m).toReal/2-error-
        (Real.exp (2*(M : ℝ)*(beta^2*deriv (Scalar.xiSlice k m) 1))/LN+
          (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*(beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1))))/(M : ℝ)≤
        (∫p,A p ∂rho.prod (stdGaussian (Model.Vector M)))/(M : ℝ)-
          (∫p,B p ∂rho.prod (stdGaussian (Model.Vector 1)))/(M : ℝ) := by
  have HT := clipped_cavity_lower k hk hbeta hm0 hm1 herror
  filter_upwards [HT] with M HM
  refine ⟨HM.1,?_⟩
  intro S _ rho _ depth x q LN b cap hxs hx hxm hx1 hq0 hqm hqend hLN hb hb1 hc
  let y := fun i : Fin (depth+2) => beta^2*deriv (Scalar.xiSlice k m) (q i)
  let z := fun i : Fin (depth+2) => q i*y i-beta^2*Scalar.xiSlice k m (q i)
  let TN := fun j : Fin (depth+1) => shift M (increments y j)
  let TC := fun j : Fin (depth+1) => shift 1 (increments z j)
  let A := fun p : S×Model.Vector M => gaussianLogSteps (quadraticSteps M (x p.1) (increments y))
    (fun h => min (Real.log (sphericalLaplace M h)) (Real.log LN)) (Real.sqrt (y 0) •p.2)
  let B := fun p : S×Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 (x p.1) (increments z))
    (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt (z 0) •p.2)
  have hZN : Measurable (fun h : Model.Vector M => 1-min (sphericalLaplace M h) LN/LN) := by
    exact measurable_const.sub (((sphericalLaplace_measurable M).min measurable_const).div_const LN)
  have haN := (spherical_deficit_bounds HM.1 hLN (0 : Model.Vector M)).2.2
  have hbN (h : Model.Vector M) := spherical_deficit_bounds HM.1 hLN h
  have hIA : Integrable A (rho.prod (stdGaussian (Model.Vector M))) := by
    exact rooted_clipped_integrable depth x hxs hx hxm hx1 TN hZN haN.1 haN.2
      (fun h => ⟨(hbN h).1,(hbN h).2.1⟩) _ (Real.log LN) (Real.sqrt (y 0))
      (fun p => rootLog_spherical_deficit_eq_clipped_logSteps HM.1 depth (x p.1) TN (hx p.1) hLN p.2) rho
  have hZC : Measurable (fun h : Model.Vector 1 => 1-max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap)/cap) := by fun_prop
  have haC := (compensation_deficit_bounds (s := 0) hb hb1 hc).2.2
  have hbC (h : Model.Vector 1) := compensation_deficit_bounds (s := Real.sqrt (M : ℝ)*h 0) hb hb1 hc
  have hIB : Integrable B (rho.prod (stdGaussian (Model.Vector 1))) := by
    exact rooted_clipped_integrable depth x hxs hx hxm hx1 TC hZC haC.1 haC.2
      (fun h => ⟨(hbC h).1,(hbC h).2.1⟩) _ (Real.log cap) (Real.sqrt (z 0))
      (fun p => scalar_compensation_rootLog_eq_clipped_logSteps M depth (x p.1) TC (hx p.1) hb hb1 hc p.2) rho
  let L := beta*(rawValue k beta m).toReal/2-error-
    (Real.exp (2*(M : ℝ)*(beta^2*deriv (Scalar.xiSlice k m) 1))/LN+
      (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*(beta^2*(deriv (Scalar.xiSlice k m) 1-Scalar.xiSlice k m 1))))/(M : ℝ)
  have hPoint (s : S) : L≤(∫g,A (s,g) ∂stdGaussian (Model.Vector M))/(M : ℝ)-
      (∫g,B (s,g) ∂stdGaussian (Model.Vector 1))/(M : ℝ) :=
    HM.2 (depth+1) (x s) q LN b cap (hx s) (hxm s).monotone (hx1 s) hq0 hqm hqend hLN hb hb1 hc
  have HI := integral_mono (integrable_const L)
    ((hIA.integral_prod_left.div_const (M : ℝ)).sub (hIB.integral_prod_left.div_const (M : ℝ))) hPoint
  simp only [integral_const,probReal_univ,one_smul,Pi.sub_apply,Pi.div_apply] at HI
  rw [integral_sub (hIA.integral_prod_left.div_const _) (hIB.integral_prod_left.div_const _),integral_div,integral_div] at HI
  rw [←integral_prod A hIA,←integral_prod B hIB] at HI
  exact ⟨hIA,hIB,HI⟩

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianClippedCavityAveraging
