-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetDeviationMeasurable
public import TensorPCA.NonRSUpperProofs.SphericalPositiveParameterCube

/-! Positive-cube averages of selected-coordinate deviation bounds. The bounded clipping
is global; its comparison with the raw deviation is used only at positive
amplitudes. No old-spin test is restricted to a star.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalFirstJetCubeBudget
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinInterpolation
open NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianPerturbationParameter NonRSUpperProofs.GaussianPerturbationDeviation
open NonRSUpperProofs.GaussianPerturbationIntegrated NonRSUpperProofs.GaussianPerturbationSelfAveraging
open SphericalPolynomialFirstJetBudget SphericalFirstJetDeviationMeasurable
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A globally bounded, nonnegative deviation error. On the positive cube it is the
minimum of two and the selected-coordinate GG budget.
-/
def boundedDegreeError {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m : ℕ) (p : Fin K) : ℝ :=
  max 0 (min 2 (degreeError nu v x m p))

theorem boundedDegreeError_nonneg {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m : ℕ) (p : Fin K) : 0≤boundedDegreeError nu v x m p :=
  le_max_left _ _

theorem boundedDegreeError_le_two {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m : ℕ) (p : Fin K) : boundedDegreeError nu v x m p≤2 :=
  max_le (by norm_num) (min_le_left _ _)

theorem boundedDegreeError_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (m : ℕ) (p : Fin K) :
    Measurable (fun x : Fin K → ℝ ↦ boundedDegreeError nu v x m p) :=
  measurable_const.max (measurable_const.min (degreeError_measurable nu hv m p))

theorem boundedDegreeError_integrable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (m : ℕ) (p : Fin K) :
    Integrable (fun x : Fin K → ℝ ↦ boundedDegreeError nu v x m p) (positiveCubeLaw K) := by
  apply Integrable.of_bound (boundedDegreeError_measurable nu hv m p).aestronglyMeasurable 2
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs,abs_of_nonneg (boundedDegreeError_nonneg nu v x m p)]
    exact boundedDegreeError_le_two nu v x m p)

theorem coordinate_boundedDegreeError_integral_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (p : Fin K) (m : ℕ)
    {r y : ℝ} (hr : 0<r) (hy : 0<y) (hy1 : y≤1) :
    (∫ t, boundedDegreeError nu v (Function.update x p t) m p ∂positiveParameterLaw)≤
      (4/(v^2*(1/4 : ℝ)^(p.val+1)))*
        ((v^2+r^2)/(2*r)+8*v^2*y+36*Real.exp (1/2)*v/y) := by
  classical
  let L := unitLinear (N := N) (coefficients v (Function.update x p 1))
  let a : ℝ := v^2*(1/4 : ℝ)^(p.val+1)
  have ha : 0<a := by dsimp only [a]; positivity
  have hL : Measurable L := unitLinear_measurable _
  have hB : ∀ᵐ z ∂nu, ‖L z‖≤2*v :=
    Eventually.of_forall (unitLinear_norm_bound hv.le _ (update_one_abs_le_two x hx p))
  have hDiag : ∀ᵐ z ∂nu, (∑ i, if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable L i z)^2 else 0)≤v^2 := Eventually.of_forall (fun z ↦ by
    change (∑ i, if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable (linear (coefficients v (Function.update x p 1))) i z.val)^2 else 0)≤v^2
    exact active_diagonal_le_v_sq v (Function.update x p 1) p (Function.update_self p 1 x) z.val z.property)
  have hBudget := totalDeviation_positive_integral_le nu L hL (by positivity : 0<2*v) hB
    (sq_nonneg v) (degreeLabel p) hDiag hr hy hy1
  have hiDev : Integrable (totalDeviation nu L (degreeLabel p)) positiveParameterLaw := by
    rw [positiveParameterLaw]
    apply Integrable.smul_measure
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1/2 : ℝ)≤1)).mp
        (totalDeviation_intervalIntegrable nu L hL (by positivity) hB (degreeLabel p) (1/2) 1)
    · norm_num
  let F : ℝ → ℝ := fun t ↦ boundedDegreeError nu v (Function.update x p t) m p
  have hm : Measurable F := by
    have hu : Measurable (fun t : ℝ ↦ Function.update x p t) := by
      simpa only [Function.comp_def,id_eq] using
        (NonRSUpperProofs.FiniteCubeFubini.update_joint_measurable K p).comp (measurable_const.prodMk measurable_id)
    simpa only [F,Function.comp_def] using (boundedDegreeError_measurable nu hv.le m p).comp hu
  have hi : Integrable F positiveParameterLaw := by
    apply Integrable.of_bound hm.aestronglyMeasurable 2
    exact Eventually.of_forall (fun t ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (boundedDegreeError_nonneg nu v _ m p)]
      exact boundedDegreeError_le_two nu v _ m p)
  have hpoint : ∀ᵐ t ∂positiveParameterLaw, F t≤(2/a)*totalDeviation nu L (degreeLabel p) t := by
    filter_upwards [positiveParameterLaw_support] with t ht
    have htpos : 0<t := by linarith [ht.1]
    have hnt : (1/2 : ℝ)≤((m : ℝ)+1)*t := by
      nlinarith [show (0 : ℝ)≤(m : ℝ) from Nat.cast_nonneg m,ht.1]
    have hδ : 0≤totalDeviation nu L (degreeLabel p) t := totalDeviation_nonneg _ _ _ _
    have hden : 0<((m : ℝ)+1)*t*a := by positivity
    have heq : degreeError nu v (Function.update x p t) m p=
        totalDeviation nu L (degreeLabel p) t/(((m : ℝ)+1)*t*a) := by
      simp only [degreeError,Function.update_idem,Function.update_self,totalDeviation,L,a]
    have hraw : 0≤degreeError nu v (Function.update x p t) m p := by rw [heq]; positivity
    have hclip : F t≤degreeError nu v (Function.update x p t) m p :=
      max_le hraw (min_le_right _ _)
    have hd : totalDeviation nu L (degreeLabel p) t/(((m : ℝ)+1)*t*a)≤
        (2/a)*totalDeviation nu L (degreeLabel p) t := by
      apply (div_le_iff₀ hden).mpr
      have heq' : ((2/a)*totalDeviation nu L (degreeLabel p) t)*(((m : ℝ)+1)*t*a)=
          (2*((m : ℝ)+1)*t)*totalDeviation nu L (degreeLabel p) t := by field_simp [ha.ne']
      rw [heq']
      nlinarith
    exact hclip.trans (by rw [heq]; exact hd)
  have hIntegral := integral_mono_ae hi (hiDev.const_mul (2/a)) hpoint
  rw [integral_const_mul] at hIntegral
  have hscaled := mul_le_mul_of_nonneg_left hBudget (by positivity : 0≤2/a)
  calc
    _ ≤ (2/a)*(∫ t, totalDeviation nu L (degreeLabel p) t ∂positiveParameterLaw) := hIntegral
    _ ≤ (2/a)*(2*((v^2+r^2)/(2*r)+8*v^2*y+18*Real.exp (1/2)*(2*v)/y)) := hscaled
    _ = _ := by dsimp only [a]; ring

theorem cube_boundedDegreeError_integral_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (p : Fin K) (m : ℕ) {r y : ℝ} (hr : 0<r) (hy : 0<y) (hy1 : y≤1) :
    (∫ x, boundedDegreeError nu v x m p ∂positiveCubeLaw K)≤
      (4/(v^2*(1/4 : ℝ)^(p.val+1)))*
        ((v^2+r^2)/(2*r)+8*v^2*y+36*Real.exp (1/2)*v/y) := by
  apply NonRSUpperProofs.FiniteCubeFubini.integral_le_of_coordinate_bound positiveParameterLaw p
    (fun x ↦ boundedDegreeError nu v x m p) (boundedDegreeError_measurable nu hv.le m p)
    (fun x ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (boundedDegreeError_nonneg nu v x m p)]
      exact boundedDegreeError_le_two nu v x m p)
  filter_upwards [positiveCubeLaw_abs_le_two K] with x hx
  exact coordinate_boundedDegreeError_integral_le nu hv x hx p m hr hy hy1

/-- The threshold is chosen uniformly over dimension, fixed prior, replica count and
represented power. It controls the error over all bounded observables, rather than
only star tests, using the SphericalUniformPowerBudget estimate.
-/
theorem exists_uniform_boundedDegreeError_threshold (K : ℕ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ), V≤v → ∀ (p : Fin K) (m : ℕ),
        (∫ x, boundedDegreeError nu v x m p ∂positiveCubeLaw K)≤eps := by
  let A : ℝ := 4/(1/4 : ℝ)^K
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
  intro N nu _ v hV p m
  have hv1 : 1≤v := (le_max_left _ _).trans hV
  have hv : 0<v := lt_of_lt_of_le (by norm_num) hv1
  have hvc : 2*A*c/eps≤v := (le_max_right _ _).trans hV
  have hvc' : 2*A*c≤v*eps := (div_le_iff₀ heps).mp hvc
  have hcv : A*(c/v)≤eps/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    calc
      A*(c/v)*2=(2*A*c)/v := by ring
      _ ≤ eps := (div_le_iff₀ hv).mpr (by nlinarith)
  have hpK : p.val+1≤K := by omega
  have hp : (1/4 : ℝ)^K≤(1/4 : ℝ)^(p.val+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hpK
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

end
end TensorPCA.NonRSLowerProofs.SphericalFirstJetCubeBudget
