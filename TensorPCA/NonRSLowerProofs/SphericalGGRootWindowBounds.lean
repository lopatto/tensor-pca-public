-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGIndicatorTilt

/-! Indicator root-density bounds on a below-threshold old event, without a GG identity
or overlap-positivity hypothesis.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGRootWindowBounds
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGThresholdWeights SphericalGGIndicatorTilt
open SphericalGGBoundedScoreWeights FiniteGGWindowScalar
open scoped BigOperators
noncomputable section

theorem scoreIntegrand_nonneg {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (u kappa t : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))
    (hPhi : 0≤Phi p.1.1 p.2) :
    0≤scoreIntegrand nu v n (thresholdScore n u) Phi (fun _ ↦ thresholdMembership n u) (window kappa) t p := by
  unfold scoreIntegrand GGFiniteJointScoreStability.integrand
  apply mul_nonneg _ (window_mem_Icc kappa _).1
  apply div_nonneg (mul_nonneg hPhi (Real.exp_nonneg _))
  apply pow_nonneg
  exact integral_nonneg (fun _ ↦ Real.exp_nonneg _)

theorem scoreIntegrand_le_small_membership {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (u : ℝ) {kappa t gap : ℝ} (hKappa : 0<kappa) (ht : 0≤t)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))
    (hPhi0 : 0≤Phi p.1.1 p.2) (hPhi1 : Phi p.1.1 p.2≤1)
    (hBelow : ∀ l : Fin n,unitOverlap (p.2 (Fin.last n)) (p.2 l.castSucc)<u)
    (hGamma : pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) p.1.1≤1-gap) :
    scoreIntegrand nu v n (thresholdScore n u) Phi (fun _ ↦ thresholdMembership n u) (window kappa) t p≤
      Real.exp (t*(1-gap))*({q | membershipMass nu v n u q≤7*Real.exp (-t)}.indicator (fun _ ↦ (1 : ℝ))) p := by
  let W := membershipMass nu v n u p
  let Z := 1-W+Real.exp t*W
  let E := Real.exp (t*pairMean nu v ((Ici u).indicator (fun _ ↦ (1 : ℝ))) p.1.1)
  let H := window kappa (indicatorTiltMass t W)
  have hW : W∈Icc (0 : ℝ) 1 := membershipMass_mem nu hv n u p
  have hZ : 1≤Z := by
    have he := mul_le_mul_of_nonneg_right (Real.one_le_exp ht) hW.1
    dsimp only [Z]
    linarith only [he]
  have hZpos : 0<Z := zero_lt_one.trans_le hZ
  have hPow : 1≤Z^(n+1) := one_le_pow₀ hZ
  have hH : H∈Icc (0 : ℝ) 1 := window_mem_Icc kappa _
  have hE : E≤Real.exp (t*(1-gap)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hGamma ht)
  rw [scoreIntegrand_eq_of_below nu hv n u kappa t Phi p hBelow]
  change (Phi p.1.1 p.2*E/Z^(n+1))*H≤_
  by_cases hSmall : W≤7*Real.exp (-t)
  · have hMem : p∈{q | membershipMass nu v n u q≤7*Real.exp (-t)} := hSmall
    rw [indicator_of_mem hMem,mul_one]
    have hR0 : 0≤Phi p.1.1 p.2*E/Z^(n+1) := div_nonneg (mul_nonneg hPhi0 (Real.exp_nonneg _)) (pow_nonneg hZpos.le _)
    calc
      _ ≤ (Phi p.1.1 p.2*E/Z^(n+1))*1 := mul_le_mul_of_nonneg_left hH.2 hR0
      _ = Phi p.1.1 p.2*E/Z^(n+1) := mul_one _
      _ ≤ Phi p.1.1 p.2*E := div_le_self (mul_nonneg hPhi0 (Real.exp_nonneg _)) hPow
      _ ≤ E := (mul_le_mul_of_nonneg_right hPhi1 (Real.exp_nonneg _)).trans_eq (one_mul _)
      _ ≤ _ := hE
  · have hNot : p∉{q | membershipMass nu v n u q≤7*Real.exp (-t)} := hSmall
    rw [indicator_of_notMem hNot,mul_zero]
    have hZero : H=0 := by
      by_contra hz
      have hPos : 0<H := lt_of_le_of_ne hH.1 (Ne.symm hz)
      have hTilt := (window_pos_imp_bounds hKappa hPos).2.le
      exact hSmall (original_mass_le_of_tilted_le ht hW hTilt)
    rw [hZero,mul_zero]

theorem scoreIntegrand_zero_of_zero {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (u kappa t : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))
    (hPhi : Phi p.1.1 p.2=0) :
    scoreIntegrand nu v n (thresholdScore n u) Phi (fun _ ↦ thresholdMembership n u) (window kappa) t p=0 := by
  simp only [scoreIntegrand,GGFiniteJointScoreStability.integrand,hPhi,zero_mul,zero_div]

end
end TensorPCA.NonRSLowerProofs.SphericalGGRootWindowBounds
