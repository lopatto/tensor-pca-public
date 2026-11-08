-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetLowDegreeBudget

/-! Simultaneous intrinsic power-GG budgets for one selected full perturbation field. No
background-prior averaging is performed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerSelection
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinInterpolation
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.GaussianGGPolynomialTests NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalPolynomialFirstJetBudget
open SphericalFirstJetCubeBudget SphericalFirstJetLowDegreeBudget
open GGFiniteFirstJet GGFiniteFirstJetBounds
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem full_power_discrepancy_abs_le_two {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (m q : ℕ)
    (Phi : (Fin (m+1) → UnitSpin N) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1) :
    let L := unitLinear (N := N) (coefficients v x)
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    |discrepancy m mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (extendTest (powerTest q))|≤2 := by
  dsimp only
  let L := unitLinear (N := N) (coefficients v x)
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := gibbsKernel nu L
  letI : IsMarkovKernel G := gibbsKernel_markov nu L (unitLinear_measurable _)
    (by positivity : 0≤2*v) (Eventually.of_forall (unitLinear_norm_bound hv.le x hx))
  let mu := law d G (m+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
  have hFresh : HasLaw (fun s : Fin (m+2) → UnitSpin N ↦ unitOverlap (s 0) (s (Fin.last (m+1)))) rho mu := by
    simpa only [Fin.castSucc_zero] using GGFiniteFirstJet.fresh_overlap_hasLaw d G m (unitOverlap_measurable N) 0
  have hOld (l : Fin m) : HasLaw (fun s : Fin (m+2) → UnitSpin N ↦ unitOverlap (s 0) (s l.succ.castSucc)) rho mu := by
    simpa only [Fin.castSucc_zero,Fin.zero_succAbove] using GGFiniteFirstJet.old_overlap_hasLaw d G m (unitOverlap_measurable N) 0 l
  letI : IsProbabilityMeasure rho := hFresh.isProbabilityMeasure_iff.mp inferInstance
  have hi : Integrable (extendTest (powerTest q)) rho :=
    Integrable.of_bound (extendTest_continuous (powerTest q)).measurable.aestronglyMeasurable 1
      (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using power_extension_abs_le q r))
  have hmean : (∫ r, |extendTest (powerTest q) r| ∂rho)≤1 := by
    have H := integral_mono_ae hi.abs (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun r ↦ power_extension_abs_le q r))
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using H
  have H := discrepancy_abs_le_l1 m mu rho (fun s ↦ Phi (initial s)) _ _
    (hPhi.comp (initial_measurable (m+1))).aestronglyMeasurable
    (Eventually.of_forall (fun s ↦ hPb (initial s))) hFresh hOld hi
  exact H.trans (by nlinarith)

theorem full_power_discrepancy_le_boundedDegreeError {N K : ℕ}
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
      boundedDegreeError nu v x m p :=
  (le_min (full_power_discrepancy_abs_le_two nu hv x hx m (p.val+1) Phi hPhi hPb)
    (full_power_discrepancy_error_le nu hv x hx hxp m p Phi hPhi hPb)).trans (le_max_right _ _)

/-- The amplitudes are selected before every bounded measurable old-spin
observable and replica count; all tests share one full Gaussian pair law. -/
theorem exists_uniform_intrinsic_powerGG_amplitudes (Q : ℕ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N K : ℕ} (hQK : Q≤K)
      (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ), V≤v →
      ∃ x : Fin K → ℝ, (∀ p, x p∈Icc (1/2 : ℝ) 1) ∧
        let L := unitLinear (N := N) (coefficients v x)
        let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
        let G := gibbsKernel nu L
        let mu := fun m ↦ law d G (m+2)
        let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
        ∀ (m : ℕ) (p : Fin K), p.val+1≤Q →
          ∀ Phi : (Fin (m+1) → UnitSpin N) → ℝ, Measurable Phi → (∀ s, |Phi s|≤1) →
            |discrepancy m (mu m) rho (fun s ↦ Phi (initial s))
              (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
              (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (extendTest (powerTest (p.val+1)))|<eps := by
  obtain ⟨V,hV1,hV⟩ := exists_uniform_lowDegree_amplitudes Q heps
  refine ⟨V,hV1,?_⟩
  intro N K hQK nu _ v hvV
  obtain ⟨x,hx,hbudget⟩ := hV hQK nu v hvV
  have hv : 0<v := lt_of_lt_of_le zero_lt_one (hV1.trans hvV)
  have hx2 (p : Fin K) : |x p|≤2 := by rw [abs_of_nonneg (by linarith [(hx p).1])]; linarith [(hx p).2]
  have hxp (p : Fin K) : 0<x p := by linarith [(hx p).1]
  refine ⟨x,hx,?_⟩
  dsimp only
  intro m p hp Phi hPhi hPb
  exact (full_power_discrepancy_le_boundedDegreeError nu hv x hx2 hxp m p Phi hPhi hPb).trans_lt (hbudget m p hp)

end
end TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerSelection
