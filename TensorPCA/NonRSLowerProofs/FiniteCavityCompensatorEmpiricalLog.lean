-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorEmpiricalInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The empirical log error of Gaussian exponential marks. Both inverse moments are
derived from Jensen, then Cauchy controls the logarithmic error.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
open MeasureTheory ProbabilityTheory Filter Set
open GGFiniteEmpiricalNormalizer FiniteCavityJointEmpiricalMoments
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem abs_log_sub_le_inv_add {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    |Real.log x-Real.log y|≤|x-y| *(x⁻¹+y⁻¹) := by
  have step {a b : ℝ} (ha : 0<a) (hb : 0<b) (hab : b≤a) :
      |Real.log a-Real.log b|≤|a-b| *(a⁻¹+b⁻¹) := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hab)),abs_of_nonneg (sub_nonneg.mpr hab)]
    calc
      _=Real.log (a/b) := (Real.log_div ha.ne' hb.ne').symm
      _≤a/b-1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
      _=(a-b)*b⁻¹ := by field_simp
      _≤(a-b)*(a⁻¹+b⁻¹) := by nlinarith [mul_nonneg (sub_nonneg.mpr hab) (inv_nonneg.mpr ha.le)]
  rcases le_total y x with h|h
  · exact step hx hy h
  · simpa only [abs_sub_comm,add_comm] using step hy hx h

private theorem cauchy_abs_mul {A : Type*} [MeasurableSpace A] (P : Measure A)
    {X Y : A→ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hY0 : ∀p,0≤Y p) :
    (∫p,|X p| *Y p ∂P)≤Real.sqrt (∫p,(X p)^2 ∂P)*Real.sqrt (∫p,(Y p)^2 ∂P) := by
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := P) (f := fun p ↦ |X p|) (g := Y)
    (.of_forall (fun _ ↦ abs_nonneg _)) (.of_forall hY0)
    (by simpa only [ENNReal.ofReal_ofNat,Real.norm_eq_abs] using hX.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hY)
  simpa only [Real.rpow_two,sq_abs,←Real.sqrt_eq_rpow] using H

variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

 theorem expMark_empirical_log_integrable_and_bound {K : ℕ} (hK : 0<K)
    (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E} (hF : Measurable F)
    {L : ℝ} (hL : 0≤L) (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    Integrable (fun p : E×(Fin K→V) ↦
      Real.log (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)-
      Real.log (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu))
      ((stdGaussian E).prod (Measure.pi (fun _ : Fin K ↦ nu))) ∧
    (∫p : E×(Fin K→V),|Real.log (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)-
      Real.log (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu)|
      ∂(stdGaussian E).prod (Measure.pi (fun _ : Fin K ↦ nu)))≤2*Real.exp (2*L^2)/Real.sqrt (K : ℝ) := by
  let S := Measure.pi (fun _ : Fin K ↦ nu)
  let P := (stdGaussian E).prod S
  let A := fun p : E×(Fin K→V) ↦ (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu)⁻¹
  let B := fun p : E×(Fin K→V) ↦ (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)⁻¹
  let X := fun p : E×(Fin K→V) ↦ empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2-
    (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu)
  let Z := fun p : E×(Fin K→V) ↦ Real.log (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)-
    Real.log (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu)
  have hMark := expMark_joint_measurable hF
  have hSec := expMark_memLp nu hF hFL
  have hSq := expMark_joint_sq_integrable nu hF hL hFL
  have hXI : Integrable (fun p ↦ (X p)^2) P :=
    error_sq_integrable hK (stdGaussian E) nu (F := fun (g : E) (x : V) ↦ Real.exp (inner ℝ (F x) g)) hMark hSec hSq
  have hXM : Measurable X := error_measurable K (F := fun (g : E) (x : V) ↦ Real.exp (inner ℝ (F x) g)) hMark nu
  have hX : MemLp X 2 P := (memLp_two_iff_integrable_sq hXM.aestronglyMeasurable).mpr hXI
  have hA : MemLp A 2 P := (population_inv_memLp nu hF hFL).comp_fst S
  have hB : MemLp B 2 P := empirical_inv_memLp hK nu hF hL hFL
  have hA0 (p : E×(Fin K→V)) : 0≤A p := inv_nonneg.mpr (population_pos nu hF hFL p.1).le
  have hB0 (p : E×(Fin K→V)) : 0≤B p := inv_nonneg.mpr (empirical_exp_pos hK F p.1 p.2).le
  have hPoint (p : E×(Fin K→V)) : |Z p|≤|X p| *A p+|X p| *B p := by
    have H := abs_log_sub_le_inv_add (empirical_exp_pos hK F p.1 p.2) (population_pos nu hF hFL p.1)
    change |Z p|≤|X p| *(B p+A p) at H
    simpa only [mul_add,add_comm] using H
  have hAbsX : MemLp (fun p ↦ |X p|) 2 P := by simpa only [Real.norm_eq_abs] using hX.norm
  have hXA : Integrable (fun p ↦ |X p| *A p) P := hAbsX.integrable_mul hA
  have hXB : Integrable (fun p ↦ |X p| *B p) P := hAbsX.integrable_mul hB
  have hZm : Measurable Z := (empirical_exp_measurable K hF).log.sub
    ((population_measurable nu hF).comp measurable_fst).log
  have hZI : Integrable Z P := (hXA.add hXB).mono' hZm.aestronglyMeasurable
    (.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs,Pi.add_apply] using hPoint p))
  refine ⟨hZI,?_⟩
  have hLog := integral_mono hZI.abs (hXA.add hXB) hPoint
  simp only [Pi.add_apply] at hLog
  rw [integral_add hXA hXB] at hLog
  have hX2 : (∫p,(X p)^2 ∂P)≤Real.exp (2*L^2)/(K : ℝ) :=
    (error_sq_integral_le hK (stdGaussian E) nu (F := fun (g : E) (x : V) ↦ Real.exp (inner ℝ (F x) g)) hMark hSec hSq).trans
      (div_le_div_of_nonneg_right (expMark_joint_sq_integral_le nu hF hL hFL) (Nat.cast_nonneg K))
  have hA2 : (∫p,(A p)^2 ∂P)≤Real.exp (2*L^2) := by
    have he : (∫p,(A p)^2 ∂P)=(∫g : E,((∫x,Real.exp (inner ℝ (F x) g) ∂nu)⁻¹)^2 ∂stdGaussian E) := by
      simpa only [probReal_univ,one_smul] using (integral_fun_fst (μ := stdGaussian E) (ν := S)
        (fun g : E ↦ ((∫x,Real.exp (inner ℝ (F x) g) ∂nu)⁻¹)^2))
    rw [he]
    exact population_inv_sq_integral_le nu hF hL hFL
  have hB2 : (∫p,(B p)^2 ∂P)≤Real.exp (2*L^2) := empirical_inv_sq_integral_le hK nu hF hL hFL
  have hRoot : Real.sqrt (Real.exp (2*L^2))=Real.exp (L^2) := by rw [←Real.exp_half]; congr 1; ring
  have hAroot := Real.sqrt_le_sqrt hA2
  have hBroot := Real.sqrt_le_sqrt hB2
  rw [hRoot] at hAroot hBroot
  have hXroot : Real.sqrt (∫p,(X p)^2 ∂P)≤Real.exp (L^2)/Real.sqrt (K : ℝ) := by
    have H := Real.sqrt_le_sqrt hX2
    rwa [Real.sqrt_div (Real.exp_pos _).le,hRoot] at H
  have hCA := (cauchy_abs_mul P hX hA hA0).trans
    (mul_le_mul hXroot hAroot (Real.sqrt_nonneg _) (by positivity))
  have hCB := (cauchy_abs_mul P hX hB hB0).trans
    (mul_le_mul hXroot hBroot (Real.sqrt_nonneg _) (by positivity))
  have he : Real.exp (L^2)/Real.sqrt (K : ℝ)*Real.exp (L^2)=Real.exp (2*L^2)/Real.sqrt (K : ℝ) := by
    rw [div_mul_eq_mul_div,←Real.exp_add]
    congr 2
    ring
  rw [he] at hCA hCB
  change (∫p,|Z p| ∂P)≤2*Real.exp (2*L^2)/Real.sqrt (K : ℝ)
  exact hLog.trans ((add_le_add hCA hCB).trans_eq (by ring))

end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
