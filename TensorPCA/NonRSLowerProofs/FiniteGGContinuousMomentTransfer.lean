-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Uniform finite-moment transfer for continuous tests on [0,1]. Polynomial degree and
tolerance are selected before the measurable model and signed integrable weights.
Only their L1 bounds enter the estimate.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGContinuousMomentTransfer
open MeasureTheory Set
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
abbrev Tests := C(Icc (0 : ℝ) 1,ℝ)
def powerTest (n : ℕ) : Tests := ⟨fun r ↦ (r : ℝ)^n,continuous_subtype_val.pow n⟩

 theorem polynomial_test_expansion (P : Polynomial ℝ) :
    P.toContinuousMapOn (Icc (0 : ℝ) 1)=
      ∑n ∈ Finset.range (P.natDegree+1),P.coeff n • powerTest n := by
  apply ContinuousMap.ext
  intro r
  change P.eval (r : ℝ)=(ContinuousMap.evalCLM ℝ r)
    (∑n ∈ Finset.range (P.natDegree+1),P.coeff n • powerTest n)
  rw [map_sum]
  simp only [map_smul,ContinuousMap.evalCLM_apply,smul_eq_mul]
  exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _) (r : ℝ)

 theorem continuous_test_bound_of_polynomial (T : Tests→L[ℝ] ℝ) (f : Tests)
    (P : Polynomial ℝ) {L eta delta : ℝ} (hL : 0≤L)
    (hT : ‖T‖≤L) (hApprox : ‖P.toContinuousMapOn (Icc (0 : ℝ) 1)-f‖≤eta)
    (hMom : ∀n,n≤P.natDegree→|T (powerTest n)|≤delta) :
    |T f|≤L*eta+delta*(∑n ∈ Finset.range (P.natDegree+1),|P.coeff n|) := by
  have hErr : |T f-T (P.toContinuousMapOn (Icc (0 : ℝ) 1))|≤L*eta := by
    rw [←map_sub,←Real.norm_eq_abs]
    apply (T.le_opNorm _).trans
    apply mul_le_mul hT _ (norm_nonneg _) hL
    rwa [norm_sub_rev]
  have hPoly : |T (P.toContinuousMapOn (Icc (0 : ℝ) 1))|≤
      delta*(∑n ∈ Finset.range (P.natDegree+1),|P.coeff n|) := by
    rw [polynomial_test_expansion,map_sum]
    simp only [map_smul,smul_eq_mul]
    calc
      _≤∑n ∈ Finset.range (P.natDegree+1),|P.coeff n*T (powerTest n)| := Finset.abs_sum_le_sum_abs _ _
      _≤∑n ∈ Finset.range (P.natDegree+1),|P.coeff n| *delta := Finset.sum_le_sum (fun n hn ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hMom n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))) (abs_nonneg _))
      _=_ := by rw [←Finset.sum_mul]; ring
  have H := abs_sub_le (T f) (T (P.toContinuousMapOn (Icc (0 : ℝ) 1))) 0
  simp only [sub_zero] at H
  exact H.trans (add_le_add hErr hPoly)

 theorem exists_finite_power_control (f : Tests) {L eps : ℝ} (hL : 0≤L) (heps : 0<eps) :
    ∃D : ℕ,∃delta : ℝ,0<delta ∧ ∀T : Tests→L[ℝ] ℝ,‖T‖≤L→
      (∀n,n≤D→|T (powerTest n)|≤delta)→|T f|≤eps := by
  let eta := eps/(2*(L+1))
  have hEta : 0<eta := by dsimp [eta]; positivity
  obtain ⟨P,hP⟩ := exists_polynomial_near_continuousMap 0 1 f eta hEta
  let C := ∑n ∈ Finset.range (P.natDegree+1),|P.coeff n|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  let delta := eps/(2*(C+1))
  have hDelta : 0<delta := by dsimp [delta]; positivity
  refine ⟨P.natDegree,delta,hDelta,?_⟩
  intro T hT hMom
  have H := continuous_test_bound_of_polynomial T f P hL hT hP.le hMom
  have h1 : L*eta≤eps/2 := by
    dsimp only [eta]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(L+1))).mpr
    nlinarith
  have h2 : delta*C≤eps/2 := by
    dsimp only [delta]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(C+1))).mpr
    nlinarith
  exact H.trans (by change L*eta+delta*C≤eps; linarith only [h1,h2])

private theorem weighted_test_integrable {S : Type u} [MeasurableSpace S] (mu : Measure S)
    (X : S→Icc (0 : ℝ) 1) (hX : Measurable X) {A : S→ℝ} (hA : Integrable A mu) (f : Tests) :
    Integrable (fun s ↦ A s*f (X s)) mu :=
  hA.mul_bdd (f.continuous.measurable.comp hX).aestronglyMeasurable
    (.of_forall (fun s ↦ f.norm_coe_le_norm (X s)))

private theorem weighted_test_abs_bound {S : Type u} [MeasurableSpace S] (mu : Measure S)
    (X : S→Icc (0 : ℝ) 1) (hX : Measurable X) {A : S→ℝ} (hA : Integrable A mu) (f : Tests) :
    |∫s,A s*f (X s) ∂mu|≤(∫s,|A s| ∂mu)*‖f‖ := by
  have hi := weighted_test_integrable mu X hX hA f
  calc
    _≤∫s,|A s*f (X s)| ∂mu := abs_integral_le_integral_abs
    _≤∫s,|A s| *‖f‖ ∂mu := integral_mono hi.abs (hA.abs.mul_const ‖f‖) (fun s ↦ by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (X s)) (abs_nonneg _))
    _=_ := integral_mul_const _ _

private def weightedExpectation {S : Type u} [MeasurableSpace S] (mu : Measure S)
    (X : S→Icc (0 : ℝ) 1) (hX : Measurable X) (A : S→ℝ) (hA : Integrable A mu) : Tests→L[ℝ] ℝ :=
  (show Tests→ₗ[ℝ] ℝ from
    { toFun := fun f ↦ ∫s,A s*f (X s) ∂mu
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply,mul_add]
        exact integral_add (weighted_test_integrable mu X hX hA f) (weighted_test_integrable mu X hX hA g)
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
        have he : (fun s ↦ A s*(c*f (X s)))=(fun s ↦ c*(A s*f (X s))) := by funext s; ring
        rw [he,integral_const_mul] }).mkContinuous (∫s,|A s| ∂mu)
      (fun f ↦ by
        change |∫s,A s*f (X s) ∂mu|≤(∫s,|A s| ∂mu)*‖f‖
        exact weighted_test_abs_bound mu X hX hA f)

private theorem weightedExpectation_norm_le {S : Type u} [MeasurableSpace S] (mu : Measure S)
    (X : S→Icc (0 : ℝ) 1) (hX : Measurable X) (A : S→ℝ) (hA : Integrable A mu) :
    ‖weightedExpectation mu X hX A hA‖≤∫s,|A s| ∂mu := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ ↦ abs_nonneg _))
  intro f
  exact weighted_test_abs_bound mu X hX hA f

 theorem exists_uniform_weighted_moment_transfer (f : Tests) {L0 L1 eps : ℝ}
    (hL0 : 0≤L0) (hL1 : 0≤L1) (heps : 0<eps) :
    ∃D : ℕ,∃delta : ℝ,0<delta ∧
    ∀(S : Type u) [MeasurableSpace S] (mu : Measure S)
      (X Y : S→Icc (0 : ℝ) 1),Measurable X→Measurable Y→
      ∀(A B : S→ℝ),Integrable A mu→Integrable B mu→
      (∫s,|A s| ∂mu)≤L0→(∫s,|B s| ∂mu)≤L1→
      (∀n,n≤D→|(∫s,A s*(X s : ℝ)^n ∂mu)-(∫s,B s*(Y s : ℝ)^n ∂mu)|≤delta)→
      Integrable (fun s ↦ A s*f (X s)) mu ∧ Integrable (fun s ↦ B s*f (Y s)) mu ∧
      |(∫s,A s*f (X s) ∂mu)-(∫s,B s*f (Y s) ∂mu)|≤eps := by
  obtain ⟨D,delta,hDelta,hTransfer⟩ := exists_finite_power_control f (add_nonneg hL0 hL1) heps
  refine ⟨D,delta,hDelta,?_⟩
  intro S mS mu X Y hX hY A B hA hB hLA hLB hMom
  refine ⟨weighted_test_integrable mu X hX hA f,weighted_test_integrable mu Y hY hB f,?_⟩
  let T := weightedExpectation mu X hX A hA-weightedExpectation mu Y hY B hB
  have hT : ‖T‖≤L0+L1 := by
    change ‖weightedExpectation mu X hX A hA-weightedExpectation mu Y hY B hB‖≤L0+L1
    exact (norm_sub_le (weightedExpectation mu X hX A hA) (weightedExpectation mu Y hY B hB)).trans (add_le_add
      ((weightedExpectation_norm_le mu X hX A hA).trans hLA)
      ((weightedExpectation_norm_le mu Y hY B hB).trans hLB))
  have H := hTransfer T hT (fun n hn ↦ hMom n hn)
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteGGContinuousMomentTransfer
