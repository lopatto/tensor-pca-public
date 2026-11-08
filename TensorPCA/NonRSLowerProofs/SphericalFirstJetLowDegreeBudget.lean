-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetCubeBudget

/-! Low-degree deviation bounds, uniform in the total perturbation cutoff, and
simultaneous coefficient selection before the replica observables are chosen.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalFirstJetLowDegreeBudget
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianPerturbationDeviation
open SphericalFirstJetCubeBudget SphericalPolynomialFirstJetBudget
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The numerical threshold depends on the tested degree Q, not the total
cutoff K. Its scalar choices follow the checked CubeBudget argument. -/
theorem exists_uniform_lowDegreeError_threshold (Q : ℕ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ), V≤v → ∀ (p : Fin K), p.val+1≤Q → ∀ (m : ℕ),
        (∫ x, boundedDegreeError nu v x m p ∂positiveCubeLaw K)≤eps := by
  let A : ℝ := 4/(1/4 : ℝ)^Q
  have hA : 0<A := by dsimp only [A]; positivity
  let y : ℝ := min 1 (eps/(16*A))
  have hy : 0<y := by dsimp only [y]; exact lt_min (by norm_num) (by positivity)
  have hy1 : y≤1 := min_le_left _ _
  have hyE : y≤eps/(16*A) := min_le_right _ _
  have hAy : 8*A*y≤eps/2 := by
    have ht := (le_div_iff₀ (by positivity : 0<16*A)).mp hyE
    nlinarith
  let c : ℝ := 1+36*Real.exp (1/2)/y
  have hc : 0<c := by dsimp only [c]; positivity
  let V : ℝ := max 1 (2*A*c/eps)
  refine ⟨V,le_max_left _ _,?_⟩
  intro N K nu _ v hV p hpQ m
  have hv1 : 1≤v := (le_max_left _ _).trans hV
  have hv : 0<v := lt_of_lt_of_le (by norm_num) hv1
  have hvc : 2*A*c/eps≤v := (le_max_right _ _).trans hV
  have hvc' : 2*A*c≤v*eps := (div_le_iff₀ heps).mp hvc
  have hcv : A*(c/v)≤eps/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    calc
      A*(c/v)*2=(2*A*c)/v := by ring
      _ ≤ eps := (div_le_iff₀ hv).mpr (by nlinarith)
  have hp : (1/4 : ℝ)^Q≤(1/4 : ℝ)^(p.val+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hpQ
  have hcoeff : 4/(1/4 : ℝ)^(p.val+1)≤A :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
  have hbr : 0≤8*y+c/v := by positivity
  have hbound := cube_boundedDegreeError_integral_le nu hv p m hv hy hy1
  have heq : (4/(v^2*(1/4 : ℝ)^(p.val+1)))*
      ((v^2+v^2)/(2*v)+8*v^2*y+36*Real.exp (1/2)*v/y)=
      (4/(1/4 : ℝ)^(p.val+1))*(8*y+c/v) := by
    dsimp only [c]
    field_simp [hv.ne',hy.ne',show (1/4 : ℝ)^(p.val+1)≠0 by positivity]
    ring
  rw [heq] at hbound
  calc
    _ ≤ (4/(1/4 : ℝ)^(p.val+1))*(8*y+c/v) := hbound
    _ ≤ A*(8*y+c/v) := mul_le_mul_of_nonneg_right hcoeff hbr
    _ = 8*A*y+A*(c/v) := by ring
    _ ≤ eps := by linarith

theorem boundedDegreeError_le_zero_replica {N K : ℕ}
    (nu : Measure (UnitSpin N)) {v : ℝ} (hv : 0<v) (x : Fin K → ℝ)
    (m : ℕ) (p : Fin K) (hxp : 0<x p) :
    boundedDegreeError nu v x m p≤boundedDegreeError nu v x 0 p := by
  have ha : 0<v^2*(1/4 : ℝ)^(p.val+1) := by positivity
  have hn := NonRSUpperProofs.GaussianPerturbationDeviation.totalDeviation_nonneg nu
    (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) (x p)
  have hraw : degreeError nu v x m p≤degreeError nu v x 0 p := by
    unfold degreeError
    simp only [Nat.cast_zero,zero_add,one_mul]
    apply div_le_div_of_nonneg_left hn (by positivity)
    have hm : (0 : ℝ)≤(m : ℝ) := Nat.cast_nonneg m
    nlinarith [mul_nonneg hm (mul_nonneg hxp.le ha.le)]
  exact max_le_max le_rfl (min_le_min_left 2 hraw)

/-- One coefficient vector simultaneously controls every replica count and represented
degree through Q; it is selected before the spin tests.
-/
theorem exists_uniform_lowDegree_amplitudes (Q : ℕ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N K : ℕ} (hQK : Q≤K)
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ), V≤v →
      ∃ x : Fin K → ℝ, (∀ p, x p∈Icc (1/2 : ℝ) 1) ∧
        ∀ (m : ℕ) (p : Fin K), p.val+1≤Q → boundedDegreeError nu v x m p<eps := by
  have hdelta : 0<eps/((Q : ℝ)+1) := by positivity
  obtain ⟨V,hV1,hV⟩ := exists_uniform_lowDegreeError_threshold Q hdelta
  refine ⟨V,hV1,?_⟩
  intro N K hQK nu _ v hvV
  have hv : 0<v := lt_of_lt_of_le zero_lt_one (hV1.trans hvV)
  let F : (Fin K → ℝ) → ℝ := fun x ↦
    ∑ q : Fin Q, boundedDegreeError nu v x 0 (Fin.castLE hQK q)
  have hi : Integrable F (positiveCubeLaw K) :=
    integrable_finsetSum Finset.univ (fun q _ ↦ boundedDegreeError_integrable nu hv.le 0 (Fin.castLE hQK q))
  have hmean : (∫ x, F x ∂positiveCubeLaw K)≤(Q : ℝ)*(eps/((Q : ℝ)+1)) := by
    rw [show (∫ x, F x ∂positiveCubeLaw K)=
      ∑ q : Fin Q, ∫ x, boundedDegreeError nu v x 0 (Fin.castLE hQK q) ∂positiveCubeLaw K from
        integral_finsetSum Finset.univ (fun q _ ↦ boundedDegreeError_integrable nu hv.le 0 (Fin.castLE hQK q))]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (fun q (_ : q∈(Finset.univ : Finset (Fin Q))) ↦
        hV nu v hvV (Fin.castLE hQK q) (by have hq := q.isLt; simp only [Fin.coe_castLE]; omega) 0)
  have hmeanlt : (∫ x, F x ∂positiveCubeLaw K)<eps := by
    apply hmean.trans_lt
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0<(Q : ℝ)+1)).mpr
    nlinarith
  have hex : ∃ x : Fin K → ℝ, (∀ p, x p∈Icc (1/2 : ℝ) 1) ∧ F x<eps := by
    by_contra h
    push_neg at h
    have hae : ∀ᵐ x ∂positiveCubeLaw K, eps≤F x :=
      (positiveCubeLaw_support K).mono (fun x hx ↦ h x hx)
    have H := integral_mono_ae (integrable_const eps) hi hae
    have H' : eps≤∫ x, F x ∂positiveCubeLaw K := by simpa using H
    exact (not_lt_of_ge H') hmeanlt
  obtain ⟨x,hx,hF⟩ := hex
  refine ⟨x,hx,?_⟩
  intro m p hpQ
  let q : Fin Q := ⟨p.val,by omega⟩
  have hpq : Fin.castLE hQK q=p := Fin.ext rfl
  have hsum : boundedDegreeError nu v x 0 p≤F x := by
    rw [← hpq]
    exact Finset.single_le_sum (fun j _ ↦ boundedDegreeError_nonneg nu v x 0 (Fin.castLE hQK j)) (Finset.mem_univ q)
  exact (boundedDegreeError_le_zero_replica nu hv x m p (by linarith [(hx p).1])).trans_lt (hsum.trans_lt hF)

end
end TensorPCA.NonRSLowerProofs.SphericalFirstJetLowDegreeBudget
