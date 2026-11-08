-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianShellChernoff
public import TensorPCA.SpherePolarProofs
public import TensorPCA.Geometry
public import Mathlib.MeasureTheory.Integral.Prod
/-! Polar comparison of a restricted Gaussian integral with the canonical spherical
partition. Radius/direction independence follows from Gaussian reconstruction in
Model.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianShellPolar
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianShellChernoff
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem radius_difference_le {r R eps : ℝ} (hr : 0 ≤ r) (hR : 0 < R)
    (hshell : |r^2-R^2| ≤ eps*R^2) : |r-R| ≤ eps*R := by
  have hprod : |r-R| *(r+R) ≤ eps*R^2 := by
    rw [← abs_of_nonneg (add_nonneg hr hR.le), ← abs_mul]
    convert hshell using 1 <;> congr 1 <;> ring
  apply (mul_le_mul_iff_left₀ hR).mp
  calc
    |r-R| *R ≤ |r-R| *(r+R) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ ≤ eps*R^2 := hprod
    _ = (eps*R)*R := by ring

private theorem field_at_shell_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h u : E} {r R eps C : ℝ} (hu : ‖u‖ = 1) (hr : 0 ≤ r) (hR : 0 < R)
    (heps : 0 ≤ eps) (hh : ‖h‖ ≤ C*R) (hshell : |r^2-R^2| ≤ eps*R^2) :
    inner ℝ h (r • u) ≤ inner ℝ h (R • u)+eps*C*R^2 := by
  have hd := radius_difference_le hr hR hshell
  have hn : ‖r • u-R • u‖ = |r-R| := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, hu, mul_one]
  have hi := (le_abs_self (inner ℝ h (r • u-R • u))).trans (abs_real_inner_le_norm _ _)
  rw [inner_sub_right, hn] at hi
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg h)
  have hm' := mul_le_mul_of_nonneg_right hh (mul_nonneg heps hR.le)
  nlinarith

private theorem scaled_polar_map {N : ℕ} (hN : 0 < N) (B : ℝ) :
    (((Model.spherePrior N).prod ((stdGaussian (Model.Vector N)).map norm)).map
      (fun p : Model.Vector N × ℝ ↦ ((Real.sqrt B)⁻¹*p.2) • p.1)) =
        scaledGaussian (E := Model.Vector N) B := by
  unfold scaledGaussian
  have H := congrArg (fun nu : Measure (Model.Vector N) ↦
    nu.map (fun g ↦ (Real.sqrt B)⁻¹ • g))
    (SpherePolarProofs.spherePrior_gaussian_radial_reconstruction hN).map_eq
  rw [Measure.map_map
    (by fun_prop : Measurable (fun g : Model.Vector N ↦ (Real.sqrt B)⁻¹ • g))
    (by fun_prop : Measurable (fun p : Model.Vector N × ℝ ↦ p.2 • p.1))] at H
  simpa only [Function.comp_def, smul_smul] using H

private theorem integral_scaled_polar {N : ℕ} (hN : 0 < N) (B : ℝ)
    (f : Model.Vector N → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂scaledGaussian B) =
      ∫ p : Model.Vector N × ℝ, f (((Real.sqrt B)⁻¹*p.2) • p.1)
        ∂(Model.spherePrior N).prod ((stdGaussian (Model.Vector N)).map norm) := by
  rw [← scaled_polar_map hN B]
  exact integral_map (by fun_prop : Measurable (fun p : Model.Vector N × ℝ ↦
    ((Real.sqrt B)⁻¹*p.2) • p.1)).aemeasurable hf.aestronglyMeasurable

theorem polar_shell_comparison {N : ℕ} (hN : 0 < N) {B eps C : ℝ}
    (hB : 0 < B) (heps : 0 ≤ eps) (hC : 0 ≤ C) (h : Model.Vector N)
    (hh : ‖h‖ ≤ C*Real.sqrt (N : ℝ)) :
    (∫ x in {x : Model.Vector N | |‖x‖^2-(N : ℝ)| ≤ eps*(N : ℝ)},
      Real.exp (inner ℝ h x) ∂scaledGaussian B) ≤
      (scaledGaussian (E := Model.Vector N) B).real
        {x | |‖x‖^2-(N : ℝ)| ≤ eps*(N : ℝ)} *
        Real.exp (eps*C*(N : ℝ)) *
          (∫ u, Real.exp (inner ℝ h (Real.sqrt (N : ℝ) • u)) ∂Model.spherePrior N) := by
  let mu := Model.spherePrior N
  let rho := (stdGaussian (Model.Vector N)).map norm
  let a := (Real.sqrt B)⁻¹
  let R := Real.sqrt (N : ℝ)
  let S : Set (Model.Vector N) := {x | |‖x‖^2-(N : ℝ)| ≤ eps*(N : ℝ)}
  let T : Model.Vector N × ℝ → Model.Vector N := fun p ↦ (a*p.2) • p.1
  let D : Set ℝ := {r | |(a*r)^2-(N : ℝ)| ≤ eps*(N : ℝ)}
  let A : Model.Vector N → ℝ := fun u ↦ Real.exp (inner ℝ h (R • u))
  let J : ℝ → ℝ := D.indicator (fun _ ↦ 1)
  let H : Model.Vector N → ℝ := S.indicator (fun x ↦ Real.exp (inner ℝ h x))
  let K := Real.exp (eps*C*(N : ℝ))
  have hR : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hRsq : R^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hB)
  haveI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact (Measure.isProbabilityMeasure_map_iff measurable_norm.aemeasurable).mpr inferInstance
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hD : MeasurableSet D := measurableSet_le (by fun_prop) measurable_const
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hH : Measurable H := (by fun_prop : Measurable (fun x : Model.Vector N ↦
    Real.exp (inner ℝ h x))).indicator hS
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hU : ∀ᵐ p : Model.Vector N × ℝ ∂mu.prod rho, ‖p.1‖ = 1 :=
    (Measure.quasiMeasurePreserving_fst).ae (Geometry.spherePrior_norm_ae hN)
  have hrho : ∀ᵐ r ∂rho, 0 ≤ r := by
    apply (ae_map_iff measurable_norm.aemeasurable measurableSet_Ici).mpr
    exact ae_of_all _ norm_nonneg
  have hRad : ∀ᵐ p : Model.Vector N × ℝ ∂mu.prod rho, 0 ≤ p.2 :=
    (Measure.quasiMeasurePreserving_snd).ae hrho
  have hShell (p : Model.Vector N × ℝ) (hu : ‖p.1‖ = 1) : T p ∈ S ↔ p.2 ∈ D := by
    change |‖(a*p.2) • p.1‖^2-(N : ℝ)| ≤ eps*(N : ℝ) ↔
      |(a*p.2)^2-(N : ℝ)| ≤ eps*(N : ℝ)
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  have hAInt : Integrable A mu := by
    apply (integrable_const (Real.exp (‖h‖*R))).mono' hA.aestronglyMeasurable
    filter_upwards [Geometry.spherePrior_norm_ae hN] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have H := (le_abs_self (inner ℝ h (R • u))).trans (abs_real_inner_le_norm _ _)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hu, mul_one] using H
  have hJInt : Integrable J rho := (integrable_const (1 : ℝ)).indicator hD
  have hMajorInt : Integrable (fun p : Model.Vector N × ℝ ↦ K*(A p.1*J p.2))
      (mu.prod rho) := (hAInt.mul_prod hJInt).const_mul K
  have hH0 (x : Model.Vector N) : 0 ≤ H x := by
    by_cases hx : x ∈ S <;> simp [H, hx, (Real.exp_pos _).le]
  have hMajor : ∀ᵐ p : Model.Vector N × ℝ ∂mu.prod rho,
      H (T p) ≤ K*(A p.1*J p.2) := by
    filter_upwards [hU, hRad] with p hu hr
    by_cases hd : p.2 ∈ D
    · have hshell : T p ∈ S := (hShell p hu).mpr hd
      have hd' : |(a*p.2)^2-R^2| ≤ eps*R^2 := by simpa only [D, mem_setOf_eq, hRsq] using hd
      have hfield := field_at_shell_le hu (mul_nonneg ha.le hr) hR heps hh hd'
      dsimp [H, J]
      rw [Set.indicator_of_mem hshell, Set.indicator_of_mem hd]
      dsimp [K, A, T]
      rw [mul_one, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simpa only [hRsq, add_comm] using hfield
    · have hshell : T p ∉ S := fun hx ↦ hd ((hShell p hu).mp hx)
      simp [H, J, Set.indicator_of_notMem hshell, Set.indicator_of_notMem hd]
  have hPullInt : Integrable (fun p ↦ H (T p)) (mu.prod rho) := by
    apply hMajorInt.mono' (hH.comp hT).aestronglyMeasurable
    filter_upwards [hMajor] with p hp
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hH0 (T p))] using hp
  have hMass : (scaledGaussian (E := Model.Vector N) B).real S = rho.real D := by
    calc
      _ = ∫ x : Model.Vector N, S.indicator (fun _ ↦ (1 : ℝ)) x ∂scaledGaussian B := by
        rw [integral_indicator hS, setIntegral_const]
        simp
      _ = ∫ p : Model.Vector N × ℝ, S.indicator (fun _ ↦ (1 : ℝ)) (T p) ∂mu.prod rho :=
        integral_scaled_polar hN B _ (measurable_const.indicator hS)
      _ = ∫ p : Model.Vector N × ℝ, J p.2 ∂mu.prod rho := by
        apply integral_congr_ae
        filter_upwards [hU] with p hu
        by_cases hd : p.2 ∈ D
        · simp [J, hd, (hShell p hu).mpr hd]
        · have hshell : T p ∉ S := fun hx ↦ hd ((hShell p hu).mp hx)
          simp [J, hd, hshell]
      _ = rho.real D := by
        rw [integral_fun_snd]
        dsimp [J]
        rw [integral_indicator hD, setIntegral_const]
        simp
  have hIntegral : (∫ x in S, Real.exp (inner ℝ h x) ∂scaledGaussian B) =
      ∫ p : Model.Vector N × ℝ, H (T p) ∂mu.prod rho := by
    rw [← integral_indicator hS]
    exact integral_scaled_polar hN B H hH
  change (∫ x in S, Real.exp (inner ℝ h x) ∂scaledGaussian B) ≤
    (scaledGaussian (E := Model.Vector N) B).real S*K*(∫ u, A u ∂mu)
  rw [hIntegral]
  apply (integral_mono_ae hPullInt hMajorInt hMajor).trans_eq
  rw [integral_const_mul, integral_prod_mul]
  dsimp [J]
  rw [integral_indicator hD, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [hMass]
  ring


end
end TensorPCA.NonRSLowerProofs.OneStepGaussianShellPolar
