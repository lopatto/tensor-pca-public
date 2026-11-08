-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.SphericalPowerGG
public import TensorPCA.NonRSUpperProofs.GaussianGGFunctional
public import TensorPCA.NonRSLowerProofs.GGFiniteFirstJetBounds

/-! Intrinsic finite power-GG budgets for unit-spin replicas. Raw powers are replaced
globally by the canonical interval projection and their agreement on the unit-spin
pair law is proved explicitly.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerBudget
open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinInterpolation
open NonRSUpperProofs.GaussianReplicaCalculus NonRSUpperProofs.GaussianReplicaKernel
open NonRSUpperProofs.GaussianGGIndicatorTransfer NonRSUpperProofs.GaussianGGPolynomialTests
open NonRSUpperProofs.SphericalPositivePerturbation
open NonRSUpperProofs.GaussianPerturbationParameter NonRSUpperProofs.GaussianPerturbationDeviation
open NonRSUpperProofs.GaussianPerturbationIntegrated NonRSUpperProofs.GaussianPerturbationSelfAveraging
open GGFiniteFirstJet GGFiniteFirstJetPermutation GGFiniteFirstJetBounds
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem power_extension_abs_le (q : ℕ) (r : ℝ) : |extendTest (powerTest q) r|≤1 := by
  let z := projIcc (-1 : ℝ) 1 (by norm_num) r
  change |(z : ℝ)^q|≤1
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨z.property.1,z.property.2⟩)

theorem power_extension_eq {r : ℝ} (hr : r∈Icc (-1 : ℝ) 1) (q : ℕ) :
    extendTest (powerTest q) r=r^q := by
  rw [extendTest_eq_of_mem (powerTest q) hr]
  rfl

theorem unitOverlap_mem_Icc {N : ℕ} (z y : UnitSpin N) : unitOverlap z y∈Icc (-1 : ℝ) 1 := by
  have H := abs_real_inner_le_norm z.val y.val
  rw [z.property,y.property,mul_one] at H
  exact abs_le.mp H

theorem unitOverlap_measurable (N : ℕ) :
    Measurable (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2) := by
  unfold unitOverlap
  fun_prop

theorem power_extension_unitOverlap {N : ℕ} (z y : UnitSpin N) (q : ℕ) :
    extendTest (powerTest q) (unitOverlap z y)=(unitOverlap z y)^q :=
  power_extension_eq (unitOverlap_mem_Icc z y) q

theorem unit_pairLaw_support {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (d : Measure Ω) (G : Kernel Ω (UnitSpin N)) [IsMarkovKernel G] :
    ∀ᵐ r ∂(((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)),
      r∈Icc (-1 : ℝ) 1 := by
  apply (ae_map_iff (unitOverlap_measurable N).aemeasurable measurableSet_Icc).mpr
  exact Eventually.of_forall (fun p ↦ unitOverlap_mem_Icc p.1 p.2)

private theorem replica_unitOverlap_measurable (N k : ℕ) (i j : Fin k) :
    Measurable (fun s : Fin k → UnitSpin N ↦ unitOverlap (s i) (s j)) := by
  simpa only [Function.comp_def] using (unitOverlap_measurable N).comp
    (show Measurable (fun s : Fin k → UnitSpin N ↦ (s i,s j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j))

private theorem unit_overlap_power_abs_le {N : ℕ} (q : ℕ) (z y : UnitSpin N) :
    |(unitOverlap z y)^q|≤1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr (unitOverlap_mem_Icc z y))

/-- Intrinsic old-spin tests are retained literally; no ambient extension
of the arbitrary test `Phi` is assumed. -/
theorem unit_powerGG_eq_discrepancy {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (L : UnitSpin N → EuclideanSpace ℝ I →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hB : ∀ᵐ z ∂nu, ‖L z‖≤K) (m q : ℕ)
    (Phi : (Fin (m+1) → UnitSpin N) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1) :
    let d := SYK.standardGaussianMeasureOnEuclidean I
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)
    powerGG nu L unitOverlap m q Phi=
      discrepancy m mu rho (fun s ↦ Phi (initial s))
        (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
        (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (fun r ↦ r^q) := by
  dsimp only
  let d := SYK.standardGaussianMeasureOnEuclidean I
  let G := gibbsKernel nu L
  letI : IsMarkovKernel G := gibbsKernel_markov nu L hL hK hB
  let mu := law d G (m+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)
  let newTest : (Fin (m+2) → UnitSpin N) → ℝ := fun s ↦
    Phi (initial s)*(unitOverlap (s 0) (s (Fin.last (m+1))))^q
  have hnew : Measurable newTest :=
    (hPhi.comp (initial_measurable (m+1))).mul ((replica_unitOverlap_measurable N (m+2) 0 (Fin.last (m+1))).pow_const q)
  have hnewB (s : Fin (m+2) → UnitSpin N) : ‖newTest s‖≤1 := by
    change |Phi (initial s)*(unitOverlap (s 0) (s (Fin.last (m+1))))^q|≤1
    rw [abs_mul]
    exact (mul_le_mul (hPb _) (unit_overlap_power_abs_le q _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hnewMean := meanReplica_eq_integral_law nu L hL hK hB (m+2) newTest hnew hnewB
  have hPhiMean := meanReplica_eq_integral_law nu L hL hK hB (m+1) Phi hPhi
    (fun s ↦ by simpa only [Real.norm_eq_abs] using hPb s)
  have hPrefix := (initial_hasLaw d G (m+1)).integral_comp hPhi.aestronglyMeasurable
  let pairTest : (Fin 2 → UnitSpin N) → ℝ := fun s ↦ (unitOverlap (s 0) (s 1))^q
  have hpairm : Measurable pairTest := (replica_unitOverlap_measurable N 2 0 1).pow_const q
  have hpairB (s : Fin 2 → UnitSpin N) : ‖pairTest s‖≤1 := by
    simpa only [pairTest,Real.norm_eq_abs] using unit_overlap_power_abs_le q (s 0) (s 1)
  have hpairMean := meanReplica_eq_integral_law nu L hL hK hB 2 pairTest hpairm hpairB
  have hPairLaw := (GGFiniteFirstJet.overlap_hasLaw d G (unitOverlap_measurable N)
    (0 : Fin 2) 1 (by decide)).integral_comp (measurable_id.pow_const q).aestronglyMeasurable
  change (∫ s, pairTest s ∂law d G 2)=∫ r, r^q ∂rho at hPairLaw
  let oldTest (l : Fin m) : (Fin (m+1) → UnitSpin N) → ℝ := fun s ↦
    Phi s*(unitOverlap (s 0) (s l.succ))^q
  have holdm (l : Fin m) : Measurable (oldTest l) :=
    hPhi.mul ((replica_unitOverlap_measurable N (m+1) 0 l.succ).pow_const q)
  have holdB (l : Fin m) (s : Fin (m+1) → UnitSpin N) : ‖oldTest l s‖≤1 := by
    change |Phi s*(unitOverlap (s 0) (s l.succ))^q|≤1
    rw [abs_mul]
    exact (mul_le_mul (hPb s) (unit_overlap_power_abs_le q _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have holdMean (l : Fin m) := meanReplica_eq_integral_law nu L hL hK hB (m+1)
    (oldTest l) (holdm l) (holdB l)
  have holdPrefix (l : Fin m) := (initial_hasLaw d G (m+1)).integral_comp (holdm l).aestronglyMeasurable
  dsimp only [d,G,rho,Function.comp_def] at hPairLaw hPrefix holdPrefix
  unfold powerGG covarianceGG discrepancy
  change meanReplica nu L (m+2) newTest-
    meanReplica nu L (m+1) Phi*meanReplica nu L 2 pairTest/((m : ℝ)+1)-
    (∑ l : Fin m, meanReplica nu L (m+1) (oldTest l))/((m : ℝ)+1)=_
  rw [hnewMean,hPhiMean,hpairMean]
  simp_rw [holdMean]
  rw [hPairLaw,← hPrefix]
  simp_rw [← holdPrefix]
  rfl

theorem unit_discrepancy_power_extension {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (L : UnitSpin N → EuclideanSpace ℝ I →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hB : ∀ᵐ z ∂nu, ‖L z‖≤K) (m q : ℕ)
    (Phi : (Fin (m+1) → UnitSpin N) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1) :
    let d := SYK.standardGaussianMeasureOnEuclidean I
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)
    discrepancy m mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (extendTest (powerTest q))=
      powerGG nu L unitOverlap m q Phi := by
  dsimp only
  let d := SYK.standardGaussianMeasureOnEuclidean I
  let G := gibbsKernel nu L
  letI : IsMarkovKernel G := gibbsKernel_markov nu L hL hK hB
  have hFresh : HasLaw (fun s : Fin (m+2) → UnitSpin N ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      (((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)) (law d G (m+2)) := by
    simpa only [Fin.castSucc_zero] using GGFiniteFirstJet.fresh_overlap_hasLaw d G m (unitOverlap_measurable N) 0
  have hOld (l : Fin m) : HasLaw (fun s : Fin (m+2) → UnitSpin N ↦ unitOverlap (s 0) (s l.succ.castSucc))
      (((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)) (law d G (m+2)) := by
    simpa only [Fin.castSucc_zero,Fin.zero_succAbove] using GGFiniteFirstJet.old_overlap_hasLaw d G m (unitOverlap_measurable N) 0 l
  have H := discrepancy_congr_on_interval m (law d G (m+2))
    (((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2))
    (fun s ↦ Phi (initial s)) _ _ hFresh hOld (unit_pairLaw_support d G)
    (fun r hr ↦ power_extension_eq hr q)
  exact H.trans (unit_powerGG_eq_discrepancy nu L hL hK hB m q Phi hPhi hPb).symm

/-- The existing spherical perturbation estimate supplies a first-anchor budget for the
globally bounded canonical power extension.
-/
theorem unit_power_discrepancy_error_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (p : Fin K) (hp : x p=1)
    (t : ℝ) (ht : 0<t) (m : ℕ)
    (Phi : (Fin (m+1) → UnitSpin N) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1) :
    let L := parameterLinear (unitLinear (N := N) (coefficients v x)) (degreeLabel p) t
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    |discrepancy m mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ unitOverlap (s 0) (s (Fin.last (m+1))))
      (fun l s ↦ unitOverlap (s 0) (s l.succ.castSucc)) (extendTest (powerTest (p.val+1)))|≤
      (meanThermalDeviation nu (unitLinear (coefficients v x)) (degreeLabel p) t+
        energyFluctuation nu (unitLinear (coefficients v x)) (degreeLabel p) t)/
        (((m : ℝ)+1)*t*(v^2*(1/4 : ℝ)^(p.val+1))) := by
  dsimp only
  have hL := parameterLinear_measurable (unitLinear (N := N) (coefficients v x))
    (unitLinear_measurable _) (degreeLabel p) t
  have hB : ∀ᵐ z ∂nu,
      ‖parameterLinear (unitLinear (coefficients v x)) (degreeLabel p) t z‖≤(1+|t|)*(2*v) :=
    Eventually.of_forall (parameterLinear_pointwise_bound _ (degreeLabel p) (by positivity)
      (unitLinear_norm_bound hv.le x hx) t)
  rw [unit_discrepancy_power_extension nu _ hL (by positivity) hB m (p.val+1) Phi hPhi hPb]
  exact unit_powerGG_error_le nu hv x hx p hp t ht m Phi hPhi hPb

theorem unit_power_firstJet_error_le {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀ p, |x p|≤2) (p : Fin K) (hp : x p=1)
    (t : ℝ) (ht : 0<t) (m : ℕ)
    (Phi : (Fin (m+1) → UnitSpin N) → ℝ) (hPhi : Measurable Phi)
    {C : ℝ} (hC : 0≤C) (hPb : ∀ s, |Phi s|≤C) :
    let L := parameterLinear (unitLinear (N := N) (coefficients v x)) (degreeLabel p) t
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let G := gibbsKernel nu L
    let mu := law d G (m+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun z : UnitSpin N×UnitSpin N ↦ unitOverlap z.1 z.2)
    let psi : Fin (m+1) → ℝ → ℝ := fun _ ↦ extendTest (powerTest (p.val+1))
    let means := fun j ↦ ∫ r, psi j r ∂rho
    |∫ s, Phi (initial s)*firstJetInsertion m unitOverlap psi means s ∂mu|≤
      ((m : ℝ)+1)*C*(((m : ℝ)+1)*
        ((meanThermalDeviation nu (unitLinear (coefficients v x)) (degreeLabel p) t+
          energyFluctuation nu (unitLinear (coefficients v x)) (degreeLabel p) t)/
          (((m : ℝ)+1)*t*(v^2*(1/4 : ℝ)^(p.val+1))))) := by
  dsimp only
  let L := parameterLinear (unitLinear (N := N) (coefficients v x)) (degreeLabel p) t
  have hL := parameterLinear_measurable (unitLinear (N := N) (coefficients v x))
    (unitLinear_measurable _) (degreeLabel p) t
  have hB : ∀ᵐ z ∂nu, ‖L z‖≤(1+|t|)*(2*v) :=
    Eventually.of_forall (parameterLinear_pointwise_bound _ (degreeLabel p) (by positivity)
      (unitLinear_norm_bound hv.le x hx) t)
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := gibbsKernel nu L
  letI : IsMarkovKernel G := gibbsKernel_markov nu L hL (by positivity) hB
  have H := firstJet_expectation_abs_le_of_first_anchor_budget d G m (unitOverlap_measurable N)
    Phi hPhi hC hPb (fun _ ↦ extendTest (powerTest (p.val+1)))
    (fun _ ↦ (extendTest_continuous (powerTest (p.val+1))).measurable)
    (fun _ ↦ (1 : ℝ)) (fun _ r ↦ power_extension_abs_le (p.val+1) r)
    (fun _ ↦ (meanThermalDeviation nu (unitLinear (coefficients v x)) (degreeLabel p) t+
      energyFluctuation nu (unitLinear (coefficients v x)) (degreeLabel p) t)/
      (((m : ℝ)+1)*t*(v^2*(1/4 : ℝ)^(p.val+1))))
    (fun _ P hPm hPb1 ↦ unit_power_discrepancy_error_le nu hv x hx p hp t ht m P hPm hPb1)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using H

end
end TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerBudget
