-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedVariableHeights
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianSphericalClipping
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianCompensationClipping

/-! Clipped numerator and compensation means with section-dependent heights. Two
normalization shifts cancel under probability measures. Unconditional moment errors
enter as hypotheses, and averaging retains the same varying height family.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedVariableHeights
open MeasureTheory ProbabilityTheory
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianMarkedTransforms
open FiniteNestedGaussianMarkedVariableHeights BoundedMarkedLogSeries
open FiniteNestedGaussianSphericalClipping FiniteNestedGaussianCompensationClipping
open FiniteGaussianLogStepsCompression OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open scoped RealInnerProductSpace
noncomputable section
variable {N : ℕ} {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

private theorem normalized_log_comparison (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→Model.Vector N→L[ℝ]Model.Vector N) {Z : Model.Vector N→ℝ}
    (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (ha1 : a<1) (hbZ : ∀z,0≤Z z ∧ Z z≤a)
    (eta : Measure (S×Model.Vector N)) [IsProbabilityMeasure eta] (mu : Measure V) [IsProbabilityMeasure mu]
    {A : V→ℝ} (hA : Measurable A) {cap : ℝ} (hc : 0<cap)
    (hbA : ∀ᵐv∂mu,0≤1-A v/cap ∧ 1-A v/cap≤a)
    (B : S×Model.Vector N→ℝ)
    (hBridge : ∀p,rootLog depth (x p.1) T Z 1 p.2=B p-Real.log cap)
    (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T Z p.2 ∂eta)|≤delta) :
    Integrable (fun v => Real.log (A v)) mu ∧ Integrable B eta ∧
      |(∫v,Real.log (A v) ∂mu)-(∫p,B p ∂eta)|≤2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  let D : V→ℝ := fun v => 1-A v/cap
  have hD : Measurable D := measurable_const.sub (hA.div_const cap)
  have hiD := bounded_mark_log_integrable mu hD ha ha1 hbA
  have hAD : ∀ᵐv∂mu,Real.log (A v)=Real.log cap+Real.log (1-D v) := by
    filter_upwards [hbA] with v hv
    have hPos : 0<A v/cap := by linarith [hv.2]
    have hp : 0<A v := (div_pos_iff_of_pos_right hc).mp hPos
    rw [show 1-D v=A v/cap by dsimp [D]; ring,Real.log_div hp.ne' hc.ne']
    ring
  have hiA : Integrable (fun v => Real.log (A v)) mu :=
    ((integrable_const (Real.log cap)).add hiD).congr (hAD.mono (fun _ h => h.symm))
  have hiRoot := rootLog_params_integrable depth x hxs hx hxm hx1 T hZ ha ha1 hbZ eta
  have hBR (p : S×Model.Vector N) : B p=rootLog depth (x p.1) T Z 1 p.2+Real.log cap := by linarith [hBridge p]
  have hiB : Integrable B eta := (hiRoot.add (integrable_const _)).congr (ae_of_all _ (fun p => (hBR p).symm))
  have hEA : (∫v,Real.log (A v) ∂mu)=Real.log cap+(∫v,Real.log (1-D v) ∂mu) := by
    rw [integral_congr_ae hAD,integral_add (integrable_const _) hiD,integral_const,probReal_univ,one_smul]
  have hEB : (∫p,B p ∂eta)=(∫p,rootLog depth (x p.1) T Z 1 p.2 ∂eta)+Real.log cap := by
    rw [integral_congr_ae (ae_of_all _ hBR),integral_add hiRoot (integrable_const _),integral_const,probReal_univ,one_smul]
  have H := FiniteNestedGaussianMarkedVariableHeights.expected_log_close_of_nested_moments
    depth x hxs hx hxm hx1 T hZ ha ha1 hbZ eta mu hD hbA n hmoment
  refine ⟨hiA,hiB,?_⟩
  rw [hEA,hEB]
  convert H using 1 <;> congr 1 <;> ring

theorem numerator_clipped_log_close {M : ℕ} (hM : 0<M) (depth : ℕ)
    (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→Model.Vector M→L[ℝ]Model.Vector M)
    {cap a : ℝ} (hc : 1≤cap) (ha : 0≤a) (ha1 : a<1) (hca : 1-1/cap≤a)
    (eta : Measure (S×Model.Vector M)) [IsProbabilityMeasure eta] (mu : Measure V) [IsProbabilityMeasure mu]
    {A : V→ℝ} (hA : Measurable A) (hbA : ∀ᵐv∂mu,1≤A v ∧ A v≤cap) (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T
        (fun z => 1-min (sphericalLaplace M z) cap/cap) p.2 ∂eta)|≤delta) :
    Integrable (fun v => Real.log (A v)) mu ∧
    Integrable (fun p : S×Model.Vector M => gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
      (fun z => min (Real.log (sphericalLaplace M z)) (Real.log cap)) p.2) eta ∧
    |(∫v,Real.log (A v) ∂mu)-
      (∫p : S×Model.Vector M,gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
        (fun z => min (Real.log (sphericalLaplace M z)) (Real.log cap)) p.2 ∂eta)|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  have hc0 : 0<cap := zero_lt_one.trans_le hc
  have hZ : Measurable (fun z : Model.Vector M => 1-min (sphericalLaplace M z) cap/cap) :=
    measurable_const.sub (((sphericalLaplace_measurable M).min measurable_const).div_const cap)
  have hbZ (z : Model.Vector M) : 0≤1-min (sphericalLaplace M z) cap/cap ∧ 1-min (sphericalLaplace M z) cap/cap≤a :=
    ⟨(spherical_deficit_bounds hM hc z).1,(spherical_deficit_bounds hM hc z).2.1.trans hca⟩
  have hDA : ∀ᵐv∂mu,0≤1-A v/cap ∧ 1-A v/cap≤a := by
    filter_upwards [hbA] with v hv
    have H := (div_le_one hc0).mpr hv.2
    have HB := div_le_div_of_nonneg_right hv.1 hc0.le
    exact ⟨by linarith,by linarith⟩
  exact normalized_log_comparison depth x hxs hx hxm hx1 T hZ ha ha1 hbZ eta mu hA hc0 hDA _
    (fun p => rootLog_spherical_deficit_eq_clipped_logSteps hM depth (x p.1) T (hx p.1) hc p.2) n hmoment

theorem compensation_clipped_log_close (depth : ℕ) (x : S→Fin (depth+1)→ℝ) (hxs : Measurable x)
    (hx : ∀s j,0<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (T : Fin (depth+1)→Model.Vector N→L[ℝ]Model.Vector N) (lambda : Model.Vector N)
    {b cap a : ℝ} (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap)
    (ha : 0≤a) (ha1 : a<1) (hca : 1-b/cap≤a)
    (eta : Measure (S×Model.Vector N)) [IsProbabilityMeasure eta] (mu : Measure V) [IsProbabilityMeasure mu]
    {A : V→ℝ} (hA : Measurable A) (hbA : ∀ᵐv∂mu,b≤A v ∧ A v≤cap) (n : ℕ) {delta : ℝ}
    (hmoment : ∀j<n,|(∫v,(1-A v/cap)^(j+1) ∂mu)-
      (∫p,weightedMoment (depth+1) (j+1) (x p.1) 0 T
        (fun z => 1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap) p.2 ∂eta)|≤delta) :
    Integrable (fun v => Real.log (A v)) mu ∧
    Integrable (fun p : S×Model.Vector N => gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
      (fun z => Real.log (max b (min (Real.exp (inner ℝ lambda z)) cap))) p.2) eta ∧
    |(∫v,Real.log (A v) ∂mu)-
      (∫p : S×Model.Vector N,gaussianLogSteps (List.ofFn (fun j : Fin (depth+1) => (x p.1 j,T j)))
        (fun z => Real.log (max b (min (Real.exp (inner ℝ lambda z)) cap))) p.2 ∂eta)|≤
      2*(a^(n+1)/(1-a))+(n : ℝ)*delta := by
  have hc0 : 0<cap := zero_lt_one.trans_le hc
  have hZ : Measurable (fun z : Model.Vector N => 1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap) := by fun_prop
  have hbZ (z : Model.Vector N) : 0≤1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap ∧
      1-max b (min (Real.exp (inner ℝ lambda z)) cap)/cap≤a :=
    ⟨(compensation_deficit_bounds (s := inner ℝ lambda z) hb hb1 hc).1,
      (compensation_deficit_bounds (s := inner ℝ lambda z) hb hb1 hc).2.1.trans hca⟩
  have hDA : ∀ᵐv∂mu,0≤1-A v/cap ∧ 1-A v/cap≤a := by
    filter_upwards [hbA] with v hv
    have H := (div_le_one hc0).mpr hv.2
    have HB := div_le_div_of_nonneg_right hv.1 hc0.le
    exact ⟨by linarith,by linarith⟩
  exact normalized_log_comparison depth x hxs hx hxm hx1 T hZ ha ha1 hbZ eta mu hA hc0 hDA _
    (fun p => rootLog_compensation_deficit_eq_clipped_logSteps depth (x p.1) T (hx p.1) lambda hb hb1 hc p.2) n hmoment

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianClippedVariableHeights
