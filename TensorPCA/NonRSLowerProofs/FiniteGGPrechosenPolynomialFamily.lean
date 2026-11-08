-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGBoundaryBands
public import TensorPCA.NonRSUpperProofs.GaussianGGFunctional

/-! A finite polynomial score family selected before every probability law.
The globally bounded score is the existing canonical projected extension;
no global boundedness of a nonconstant raw polynomial is asserted. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGPrechosenPolynomialFamily
open MeasureTheory Set
open FiniteGGBoundaryBands
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rampTest (a b : ℝ) (J : ℕ) (j : Fin J) : C(Icc (-1 : ℝ) 1,ℝ) :=
  ⟨fun r ↦ ramp a b J j r,(ramp_continuous a b J j).comp continuous_subtype_val⟩

 theorem polynomial_pointwise_approx {a b : ℝ} {J : ℕ} (j : Fin J) (P : Polynomial ℝ) {delta : ℝ}
    (hApprox : ‖P.toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤delta)
    {r : ℝ} (hr : r∈Icc (-1 : ℝ) 1) : |P.eval r-ramp a b J j r|≤delta := by
  have H := (P.toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j).norm_coe_le_norm ⟨r,hr⟩
  rw [Real.norm_eq_abs] at H
  exact H.trans hApprox

 theorem projected_polynomial_bound {a b : ℝ} {J : ℕ} (j : Fin J) (P : Polynomial ℝ) {delta : ℝ}
    (hApprox : ‖P.toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤delta) (r : ℝ) :
    |extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤1+delta := by
  have hRamp : ‖rampTest a b J j‖≤1 := by
    apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ)≤1)).mpr
    intro q
    change ‖ramp a b J j q‖≤1
    rw [Real.norm_of_nonneg (ramp_mem a b J j q).1]
    exact (ramp_mem a b J j q).2
  have hNorm : ‖P.toContinuousMapOn (Icc (-1 : ℝ) 1)‖≤delta+1 := by
    calc
      _=‖(P.toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j)+rampTest a b J j‖ := by rw [sub_add_cancel]
      _≤_ := norm_add_le _ _
      _≤delta+1 := add_le_add hApprox hRamp
  have H := (extendTest_norm_le (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r).trans hNorm
  simpa only [Real.norm_eq_abs,add_comm] using H

 theorem projected_polynomial_indicator_error {a b : ℝ} (hab : a<b) {J : ℕ}
    (j : Fin J) (P : Polynomial ℝ) {delta : ℝ}
    (hApprox : ‖P.toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤delta)
    {r : ℝ} (hr : r∈Icc (-1 : ℝ) 1) :
    |extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r-
      (Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r|≤
      delta+(band a b J j).indicator (fun _ ↦ (1 : ℝ)) r := by
  rw [extendTest_eq_of_mem _ hr]
  have H := abs_sub_le (P.eval r) (ramp a b J j r)
    ((Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r)
  exact H.trans (add_le_add (polynomial_pointwise_approx j P hApprox hr) (ramp_indicator_error_le_band hab J j r))

 theorem projected_polynomial_indicator_L1 {a b : ℝ} (hab : a<b) {J : ℕ}
    (j : Fin J) (P : Polynomial ℝ) {delta : ℝ}
    (hApprox : ‖P.toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤delta)
    (rho : Measure ℝ) [IsProbabilityMeasure rho] (hSupport : ∀ᵐr ∂rho,r∈Icc (-1 : ℝ) 1) :
    (∫r,|extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)) r-
      (Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r| ∂rho)≤delta+rho.real (band a b J j) := by
  have hPoly := extendTest_integrable rho (P.toContinuousMapOn (Icc (-1 : ℝ) 1))
  have hInd : Integrable ((Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ))) rho :=
    (integrable_const (μ := rho) (1 : ℝ)).indicator measurableSet_Ici
  have hBand := (integrable_const (μ := rho) (1 : ℝ)).indicator (show MeasurableSet (band a b J j) from measurableSet_Icc)
  have H := integral_mono_ae (hPoly.sub hInd).abs ((integrable_const delta).add hBand)
    (hSupport.mono (fun r hr ↦ projected_polynomial_indicator_error hab j P hApprox hr))
  simp only [Pi.add_apply] at H
  rw [integral_add (integrable_const delta) hBand,integral_const,probReal_univ,one_smul,
    integral_indicator_const 1 (show MeasurableSet (band a b J j) from measurableSet_Icc)] at H
  simpa only [smul_eq_mul,mul_one,Pi.sub_apply] using H

 theorem exists_prechosen_polynomial_family {a b eta : ℝ} (ha : -1<a) (hab : a<b) (hb : b<1)
    (hEta : 0<eta) (hEta1 : eta≤1) :
    ∃J : ℕ,0<J ∧ 0<radius a b J ∧ 1/(J : ℝ)≤eta/2 ∧
    ∃P : Fin J→Polynomial ℝ,∃Q : ℕ,
      (∀j,threshold a b J j∈Ioo a b ∧ band a b J j⊆Ioo a b ∧ band a b J j⊆Ioo (-1 : ℝ) 1) ∧
      (∀i j : Fin J,i≠j→Disjoint (band a b J i) (band a b J j)) ∧
      (∀j,(P j).natDegree≤Q) ∧
      (∀j,‖(P j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest a b J j‖≤eta/2) ∧
      (∀j r,|extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) ∧
      ∀(rho : Measure ℝ) [IsProbabilityMeasure rho],(∀ᵐr ∂rho,r∈Icc (-1 : ℝ) 1)→
        ∃j : Fin J,rho.real (band a b J j)≤eta/2 ∧
          (∫r,|extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r-
            (Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r| ∂rho)≤eta := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt (show 0<eta/2 by positivity)
  let J := N+1
  have hJ : 0<J := Nat.succ_pos N
  have hBudget : 1/(J : ℝ)≤eta/2 := by
    simpa only [J,Nat.cast_add,Nat.cast_one] using hN.le
  have hPolys (j : Fin J) := exists_polynomial_near_continuousMap (-1) 1 (rampTest a b J j) (eta/2) (by positivity)
  choose P hP using hPolys
  let Q := Finset.univ.sup (fun j : Fin J ↦ (P j).natDegree)
  have hQ (j : Fin J) : (P j).natDegree≤Q := Finset.le_sup (f := fun j : Fin J ↦ (P j).natDegree) (Finset.mem_univ j)
  refine ⟨J,hJ,radius_pos hab J,hBudget,P,Q,?_,(fun i j hij ↦ bands_disjoint hab J hij),hQ,fun j ↦ (hP j).le,?_,?_⟩
  · intro j
    refine ⟨threshold_mem hab J j,band_subset_interval hab J j,?_⟩
    intro r hr
    have H := band_subset_interval hab J j hr
    exact ⟨ha.trans H.1,H.2.trans hb⟩
  · intro j r
    exact (projected_polynomial_bound j (P j) (hP j).le r).trans (by linarith)
  · intro rho hRho hSupport
    obtain ⟨j,hj⟩ := exists_small_band hab hJ rho
    have hSmall := hj.trans hBudget
    refine ⟨j,hSmall,?_⟩
    exact (projected_polynomial_indicator_L1 hab j (P j) (hP j).le rho hSupport).trans (by linarith)

end
end TensorPCA.NonRSLowerProofs.FiniteGGPrechosenPolynomialFamily
