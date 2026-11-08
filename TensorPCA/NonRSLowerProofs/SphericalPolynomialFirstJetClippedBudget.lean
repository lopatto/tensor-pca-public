-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerSelection

/-! Pointwise bounded-error polynomial first-jet control under the full-amplitude Gibbs
law. The bounded right-hand side can be integrated over the cube, without
integrating a raw unbounded deviation error.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetClippedBudget
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinInterpolation
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.GaussianGGPolynomialTests NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalPolynomialFirstJetBudget
open SphericalFirstJetCubeBudget
open GGFiniteFirstJet GGFiniteFirstJetBounds
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Degree zero and unrepresented degrees have their existing bookkeeping zero;
represented positive degrees have the bounded deviation error.
-/
def boundedPowerError {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m q : ℕ) : ℝ := max 0 (min 2 (powerError nu v x m q))

theorem boundedPowerError_nonneg {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m q : ℕ) : 0≤boundedPowerError nu v x m q := le_max_left _ _

theorem boundedPowerError_le_two {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m q : ℕ) : boundedPowerError nu v x m q≤2 :=
  max_le (by norm_num) (min_le_left _ _)

theorem boundedPowerError_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (m q : ℕ) :
    Measurable (fun x : Fin K → ℝ ↦ boundedPowerError nu v x m q) := by
  unfold boundedPowerError powerError
  split_ifs with hq
  · exact measurable_const.max (measurable_const.min
      (SphericalFirstJetDeviationMeasurable.degreeError_measurable nu hv m ⟨q-1,by omega⟩))
  · exact measurable_const

theorem boundedPowerError_eq_degreeError {N K : ℕ} (nu : Measure (UnitSpin N)) (v : ℝ)
    (x : Fin K → ℝ) (m : ℕ) (p : Fin K) :
    boundedPowerError nu v x m (p.val+1)=boundedDegreeError nu v x m p := by
  simp [boundedPowerError,powerError,boundedDegreeError,show 0<p.val+1 ∧ p.val+1≤K by omega]

theorem boundedPowerError_integrable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (m q : ℕ) :
    Integrable (fun x : Fin K → ℝ ↦ boundedPowerError nu v x m q) (positiveCubeLaw K) := by
  apply Integrable.of_bound (boundedPowerError_measurable nu hv m q).aestronglyMeasurable 2
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs,abs_of_nonneg (boundedPowerError_nonneg nu v x m q)]
    exact boundedPowerError_le_two nu v x m q)

theorem full_polynomial_discrepancy_clipped_le {N K : ℕ}
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
      ∑ q ∈ Finset.range (K+1), |P.coeff q| *boundedPowerError nu v x m q := by
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
  have hpower : ∀ q ∈ Finset.range (K+1), |D (powerTest q)|≤boundedPowerError nu v x m q := by
    intro q hq
    have hqK : q≤K := by have hh := Finset.mem_range.mp hq; omega
    by_cases hq0 : q=0
    · subst q
      change |discrepancy m mu rho f
        (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
        (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (fun _ ↦ 1)|≤_
      rw [discrepancy_one]
      simp [boundedPowerError,powerError]
    · let p : Fin K := ⟨q-1,by omega⟩
      have hpq : p.val+1=q := by dsimp only [p]; omega
      have H := SphericalFirstJetPowerSelection.full_power_discrepancy_le_boundedDegreeError nu hv x hx hxp m p Phi hPhi hPb
      rw [hpq] at H
      change |discrepancy m mu rho f _ _ (extendTest (powerTest q))|≤_ at H
      simpa only [D,functional_apply,boundedPowerError,powerError,boundedDegreeError,dif_pos (show 0<q ∧ q≤K from ⟨Nat.pos_of_ne_zero hq0,hqK⟩)] using H
  exact polynomial_discrepancy_le D P hPK (boundedPowerError nu v x m) hpower

theorem polynomial_firstJet_clipped_error_le {N K : ℕ}
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
      ((m : ℝ)+1)*C*(∑ j, ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q) := by
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
    (fun j ↦ ∑ q ∈ Finset.range (K+1), |(P j).coeff q| *boundedPowerError nu v x m q)
    (fun j Q hQ hQb ↦ full_polynomial_discrepancy_clipped_le nu hv x hx hxp m Q hQ hQb (P j) (hPK j))

end
end TensorPCA.NonRSLowerProofs.SphericalPolynomialFirstJetClippedBudget
