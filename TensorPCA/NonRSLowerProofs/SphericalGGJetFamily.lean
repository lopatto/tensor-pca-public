-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteParameterizedJets
public import TensorPCA.NonRSLowerProofs.GGFiniteJetL1TaylorPropagation
public import TensorPCA.NonRSLowerProofs.SphericalFirstJetPowerBudget

/-! Full-amplitude spherical GG jets with amplitude-conditional pair means. The spin
probability is fixed, and disorder is averaged under the perturbation Gaussian at
that amplitude.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGJetFamily
open MeasureTheory ProbabilityTheory Filter
open GaussianSpinInterpolation
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open GGFiniteFirstJet GGFiniteReweightingDerivative GGFiniteReweightingJets GGFiniteParameterizedJets
open SphericalFirstJetPowerBudget
open scoped BigOperators RealInnerProductSpace
noncomputable section

def pairMean {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (psi : ℝ → ℝ) (x : Fin K → ℝ) : ℝ :=
  ∫ r, psi r ∂(((((parameterizedGibbsKernel nu v).sectR x) ×ₖ
    ((parameterizedGibbsKernel nu v).sectR x)) ∘ₘ
      SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)).map
        (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2))

def jet {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (k n : ℕ) (psi : Fin (n+1) → ℝ → ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ) (x : Fin K → ℝ) (t : ℝ) : ℝ :=
  reweightingJet (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((parameterizedGibbsKernel nu v).sectR x) unitOverlap k n psi
      (fun j ↦ pairMean nu v (psi j) x) (Phi x) t

theorem pairMean_zero {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (x : Fin K → ℝ) : pairMean nu v (fun _ ↦ 0) x=0 := by
  simp only [pairMean,integral_zero]

theorem pairMean_snoc_zero {N K n : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (psi : Fin (n+1) → ℝ → ℝ) (x : Fin K → ℝ) :
    (fun j : Fin (n+2) ↦ pairMean nu v ((Fin.snoc psi (fun _ ↦ 0) : Fin (n+2) → ℝ → ℝ) j) x)=
      Fin.snoc (fun j ↦ pairMean nu v (psi j) x) 0 := by
  funext j
  refine Fin.lastCases ?_ (fun l ↦ ?_) j
  · simp only [Fin.snoc_last,pairMean_zero]
  · simp only [Fin.snoc_castSucc]

theorem jet_succ {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (k n : ℕ) (psi : Fin (n+1) → ℝ → ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ) (x : Fin K → ℝ) (t : ℝ) :
    jet nu v (k+1) n psi Phi x t=
      jet nu v k (n+1) (Fin.snoc psi (fun _ ↦ 0))
        (fun x s ↦ Phi x (initial s)*firstJetInsertion n unitOverlap psi
          (fun j ↦ pairMean nu v (psi j) x) s) x t := by
  simp only [jet,reweightingJet,pairMean_snoc_zero]

private theorem unitLinear_bounded {N K : ℕ} (a : Fin K → ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀ z : UnitSpin N, ‖unitLinear a z‖≤B := by
  refine ⟨Real.sqrt (∑ p, (a p)^2),Real.sqrt_nonneg _,?_⟩
  intro z
  rw [unitLinear,linear,innerSL_apply_norm]
  exact feature_norm_le a (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (Finset.sum_nonneg (fun p _ ↦ sq_nonneg (a p)))]) z.val z.property

theorem parameterized_slice_eq_actual {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v) (x : Fin K → ℝ) :
    (parameterizedGibbsKernel nu v).sectR x=gibbsKernel nu (unitLinear (coefficients v x)) := by
  obtain ⟨B,hB,hb⟩ := unitLinear_bounded (N := N) (coefficients v x)
  apply Kernel.ext
  intro w
  rw [Kernel.sectR_apply,parameterizedGibbsKernel_apply nu hv,
    gibbsKernel_apply nu _ (unitLinear_measurable _) hB (Eventually.of_forall hb)]

theorem pairMean_eq_actual {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (psi : ℝ → ℝ) (x : Fin K → ℝ) :
    pairMean nu v psi x=
      ∫ r, psi r ∂((((gibbsKernel nu (unitLinear (coefficients v x))) ×ₖ
        (gibbsKernel nu (unitLinear (coefficients v x)))) ∘ₘ
          SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)).map
            (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)) := by
  simp only [pairMean,parameterized_slice_eq_actual nu hv]

theorem pairMean_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) {psi : ℝ → ℝ} (hpsi : Measurable psi) {B : ℝ} (hb : ∀ r, |psi r|≤B) :
    Measurable (fun x : Fin K → ℝ ↦ pairMean nu v psi x) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact conditional_pair_mean_measurable _ _ (unitOverlap_measurable N) hpsi hb

theorem pairMean_abs_le {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) {psi : ℝ → ℝ} {B : ℝ} (hb : ∀ r, |psi r|≤B) (x : Fin K → ℝ) :
    |pairMean nu v psi x|≤B := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have H := norm_integral_le_of_norm_le_const
    (μ := ((((parameterizedGibbsKernel nu v).sectR x) ×ₖ ((parameterizedGibbsKernel nu v).sectR x)) ∘ₘ
      SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)).map
        (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2))
    (f := psi) (C := B) (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hb r))
  simpa only [pairMean,Real.norm_eq_abs,probReal_univ,mul_one] using H

theorem jet_parameter_measurable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (k n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {t : (Fin K → ℝ) → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ jet nu v k n psi Phi x (t x)) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact parameterized_jet_measurable _ _ k n (unitOverlap_measurable N) hpsi
    (fun j ↦ pairMean_measurable nu hv (hpsi j) (hb j)) hPhi ht

theorem jet_hasDerivAt {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (k n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : ∀ x, Measurable (Phi x)) {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (x : Fin K → ℝ) (t : ℝ) :
    HasDerivAt (jet nu v k n psi Phi x) (jet nu v (k+1) n psi Phi x t) t := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact reweightingJet_hasDerivAt _ _ k n (unitOverlap_measurable N) hpsi
    (fun j ↦ pairMean nu v (psi j) x) B hb (fun j ↦ pairMean_abs_le nu hv (hb j) x)
      (hPhi x) hC (hp x) t

theorem jet_abs_le {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (k n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : ∀ x, Measurable (Phi x)) {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (x : Fin K → ℝ) (T t : ℝ) (ht : |t|≤T) :
    |jet nu v k n psi Phi x t|≤
      C*Real.exp (2*((n : ℝ)+1)*T*(∑ j, B j))*(2*(∑ j, B j))^k*((n+1).ascFactorial k : ℝ) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  exact reweightingJet_abs_le _ _ k n (unitOverlap_measurable N) hpsi
    (fun j ↦ pairMean nu v (psi j) x) B hb (fun j ↦ pairMean_abs_le nu hv (hb j) x)
      (hPhi x) hC (hp x) T t ht

private theorem expectation_zero_eq_law {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) {C : ℝ} (hp : ∀ old, |Phi old|≤C) :
    reweightingExpectation n d G overlap psi means Phi 0=∫ old, Phi old ∂law d G (n+1) := by
  have hi : Integrable Phi (law d G (n+1)) := Integrable.of_bound hPhi.aestronglyMeasurable C
    (Eventually.of_forall (fun old ↦ by simpa only [Real.norm_eq_abs] using hp old))
  rw [law,Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  simp only [reweightingExpectation,reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,
    zero_mul,Real.exp_zero,integral_const,probReal_univ,one_smul,one_pow,mul_one,div_one,
    Kernel.const_apply,iid_apply]

theorem jet_one_zero_eq_actual {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : ∀ x, Measurable (Phi x)) {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (x : Fin K → ℝ) :
    jet nu v 1 n psi Phi x 0=
      let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
      let G := gibbsKernel nu (unitLinear (coefficients v x))
      let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)
      ∫ s, Phi x (initial s)*firstJetInsertion n unitOverlap psi (fun j ↦ ∫ r, psi j r ∂rho) s
        ∂law d G (n+2) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  rw [jet_succ nu v 0 n psi Phi x 0]
  change reweightingExpectation (n+1) _ _ _ _ _ _ 0=_
  dsimp only
  have hF : Measurable (fun s : Fin (n+2) → UnitSpin N ↦
      Phi x (initial s)*firstJetInsertion n unitOverlap psi (fun j ↦ pairMean nu v (psi j) x) s) := by
    convert (((hPhi x).comp (initial_measurable _)).mul
      (firstJetInsertion_measurable n (unitOverlap_measurable N) hpsi
        (fun j ↦ pairMean nu v (psi j) x))) using 1
    rfl
  rw [expectation_zero_eq_law _ _ (n+1) unitOverlap _ _
    hF
    (inserted_test_bound n unitOverlap psi (fun j ↦ pairMean nu v (psi j) x) B hb
      (fun j ↦ pairMean_abs_le nu hv (hb j) x) hC (hp x))]
  simp only [parameterized_slice_eq_actual nu hv,pairMean_eq_actual nu hv]

end
end TensorPCA.NonRSLowerProofs.SphericalGGJetFamily
