-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerBudget
public import TensorPCA.NonRSUpperProofs.SphericalPerturbationCoordinateSlice

/-! Finite polynomial first-jet budgets for one full-amplitude unit-spin Gibbs field.
All selected-coordinate estimates are transported to that same field before
polynomial linearity or anchor summation.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetBudget
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinInterpolation
open NonRSUpperProofs.GaussianReplicaCalculus NonRSUpperProofs.GaussianReplicaKernel
open NonRSUpperProofs.GaussianGGIndicatorTransfer NonRSUpperProofs.GaussianGGPolynomialTests
open NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianPerturbationParameter NonRSUpperProofs.GaussianPerturbationDeviation
open NonRSUpperProofs.GaussianPerturbationIntegrated NonRSUpperProofs.GaussianPerturbationSelfAveraging
open GGFiniteFirstJet GGFiniteFirstJetBounds SphericalFirstJetPowerBudget
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem unitLinear_active_full {N K : ℕ} (v : ℝ) (x : Fin K → ℝ) (p : Fin K) :
    parameterLinear (unitLinear (N := N) (coefficients v (Function.update x p 1)))
      (degreeLabel p) (x p)=unitLinear (coefficients v x) := by
  ext z w
  rw [unitLinear_active_slice]
  simp only [Function.update_eq_self]

private theorem update_one_bound {K : ℕ} (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (p : Fin K) :
    ∀ q, |Function.update x p 1 q|≤2 := by
  classical
  intro q
  by_cases h : q=p
  · subst q
    norm_num
  · simpa only [Function.update_of_ne h] using hx q

/-- The selected-coordinate deviation budget, evaluated at the full amplitude of that
coordinate. Its background has that coordinate one.
-/
def degreeError {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m : ℕ) (p : Fin K) : ℝ :=
  (meanThermalDeviation nu (unitLinear (coefficients v (Function.update x p 1)))
      (degreeLabel p) (x p)+
    energyFluctuation nu (unitLinear (coefficients v (Function.update x p 1)))
      (degreeLabel p) (x p))/
    (((m : ℝ)+1)*(x p)*(v^2*(1/4 : ℝ)^(p.val+1)))

/-- Degree zero has zero discrepancy. Degrees outside the finite tensor
cutoff are bookkeeping zeros and are never asserted to satisfy a GG bound. -/
def powerError {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m q : ℕ) : ℝ :=
  if hq : 0<q ∧ q≤K then degreeError nu v x m ⟨q-1,by omega⟩ else 0

theorem full_power_discrepancy_error_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (hxp : ∀ p, 0<x p)
    (m : ℕ) (p : Fin K) (Phi : (Fin (m+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1) :
    let L := unitLinear (N := N) (coefficients v x)
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    |discrepancy m mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (extendTest (powerTest (p.val+1)))|≤
      degreeError nu v x m p := by
  classical
  have H := unit_power_discrepancy_error_le nu hv (Function.update x p 1)
    (update_one_bound x hx p) p (by simp) (x p) (hxp p) m Phi hPhi hPb
  rw [unitLinear_active_full] at H
  exact H

theorem full_polynomial_discrepancy_error_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (hxp : ∀ p, 0<x p)
    (m : ℕ) (Phi : (Fin (m+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    (P : Polynomial ℝ) (hPK : P.natDegree≤K) :
    let L := unitLinear (N := N) (coefficients v x)
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    |discrepancy m mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc))
      (extendTest (P.toContinuousMapOn (Icc (-1 : ℝ) 1)))|≤
      ∑ q ∈ Finset.range (K+1), |P.coeff q| *powerError nu v x m q := by
  dsimp only
  let L := unitLinear (N := N) (coefficients v x)
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := gibbsKernel nu L
  letI : IsMarkovKernel G := gibbsKernel_markov nu L (unitLinear_measurable _)
    (by positivity : 0≤2*v) (Eventually.of_forall (unitLinear_norm_bound hv.le x hx))
  let mu := law d G (m+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
  have hFresh : HasLaw (fun s : Fin (m+2) → UnitSpin N ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      rho mu := by
    simpa only [Fin.castSucc_zero] using GGFiniteFirstJet.fresh_overlap_hasLaw d G m (unitOverlap_measurable N) 0
  have hOld (l : Fin m) : HasLaw (fun s : Fin (m+2) → UnitSpin N ↦ unitOverlap (s 0) (s l.succ.castSucc))
      rho mu := by
    simpa only [Fin.castSucc_zero,Fin.zero_succAbove] using GGFiniteFirstJet.old_overlap_hasLaw d G m (unitOverlap_measurable N) 0 l
  letI : IsProbabilityMeasure rho := hFresh.isProbabilityMeasure_iff.mp inferInstance
  let f : (Fin (m+2) → UnitSpin N) → ℝ := fun s ↦ Phi (initial s)
  have hf : AEStronglyMeasurable f mu := (hPhi.comp (initial_measurable (m+1))).aestronglyMeasurable
  have hb : ∀ᵐ s ∂mu, |f s|≤1 := Eventually.of_forall (fun s ↦ hPb (initial s))
  let D := functional m mu rho f _ _ hf hb hFresh hOld
  have hpower : ∀ q ∈ Finset.range (K+1), |D (powerTest q)|≤powerError nu v x m q := by
    intro q hq
    have hqK : q≤K := by have hh := Finset.mem_range.mp hq; omega
    by_cases hq0 : q=0
    · subst q
      change |discrepancy m mu rho f
        (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
        (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (fun _ ↦ 1)|≤_
      rw [discrepancy_one]
      simp [powerError]
    · let p : Fin K := ⟨q-1,by omega⟩
      have hpq : p.val+1=q := by dsimp only [p]; omega
      have H := full_power_discrepancy_error_le nu hv x hx hxp m p Phi hPhi hPb
      rw [hpq] at H
      change |discrepancy m mu rho f _ _ (extendTest (powerTest q))|≤_ at H
      simpa only [D,functional_apply,powerError,dif_pos (show 0<q ∧ q≤K from ⟨Nat.pos_of_ne_zero hq0,hqK⟩)] using H
  exact polynomial_discrepancy_le D P hPK (powerError nu v x m) hpower

theorem polynomial_firstJet_error_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (hxp : ∀ p, 0<x p)
    (m : ℕ) (Phi : (Fin (m+1) → UnitSpin N) → ℝ)
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hPb : ∀ s, |Phi s|≤C)
    (P : Fin (m+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K) :
    let L := unitLinear (N := N) (coefficients v x)
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    let psi : Fin (m+1) → ℝ → ℝ := fun j ↦ extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1))
    let means := fun j ↦ ∫ r, psi j r ∂rho
    |∫ s, Phi (initial s)*firstJetInsertion m unitOverlap psi means s ∂mu|≤
      ((m : ℝ)+1)*C*(∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *powerError nu v x m q) := by
  dsimp only
  let L := unitLinear (N := N) (coefficients v x)
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := gibbsKernel nu L
  letI : IsMarkovKernel G := gibbsKernel_markov nu L (unitLinear_measurable _)
    (by positivity : 0≤2*v) (Eventually.of_forall (unitLinear_norm_bound hv.le x hx))
  exact firstJet_expectation_abs_le_of_first_anchor_budget d G m (unitOverlap_measurable N)
    Phi hPhi hC hPb (fun j ↦ extendTest ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)))
    (fun j ↦ (extendTest_continuous _).measurable)
    (fun j ↦ ‖(P j).toContinuousMapOn (Icc (-1 : ℝ) 1)‖)
    (fun j r ↦ by simpa only [Real.norm_eq_abs] using extendTest_norm_le ((P j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r)
    (fun j ↦ ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *powerError nu v x m q)
    (fun j Q hQ hQb ↦ full_polynomial_discrepancy_error_le nu hv x hx hxp m Q hQ hQb (P j) (hPK j))

end
end TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetBudget
