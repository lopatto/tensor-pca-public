-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteReweightingJets
public import TensorPCA.NonRSUpperProofs.SphericalPerturbationGibbsKernel

/-! Joint parameter measurability for conditional pair means and literal finite GG jets.
Parameters are never averaged into the pair mean.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteParameterizedJets
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet
open GGFiniteReweightingDerivative GGFiniteReweightingJets
open scoped BigOperators
noncomputable section
variable {X Ω V : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]

theorem conditional_pair_mean_measurable (d : Measure Ω) [IsProbabilityMeasure d]
    (K : Kernel (X×Ω) V) [IsMarkovKernel K] {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : ℝ → ℝ} (hpsi : Measurable psi) {B : ℝ} (hb : ∀ r, |psi r|≤B) :
    Measurable (fun x : X ↦ ∫ r, psi r
      ∂((((K.sectR x) ×ₖ (K.sectR x)) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2))) := by
  have he (x : X) : (∫ r, psi r
      ∂((((K.sectR x) ×ₖ (K.sectR x)) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)))=
        ∫ w, ∫ p : V×V, psi (overlap p.1 p.2) ∂(K (x,w)).prod (K (x,w)) ∂d := by
    rw [integral_map hR.aemeasurable hpsi.aestronglyMeasurable]
    have hi : Integrable (fun p : V×V ↦ psi (overlap p.1 p.2))
        (((K.sectR x) ×ₖ (K.sectR x)) ∘ₘ d) :=
      Integrable.of_bound (hpsi.comp hR).aestronglyMeasurable B
        (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hb (overlap p.1 p.2)))
    rw [Measure.comp_eq_comp_const_apply] at hi ⊢
    rw [Kernel.integral_comp hi]
    simp only [Kernel.const_apply,Kernel.prod_apply,Kernel.sectR_apply]
  have H := ((hpsi.comp hR).stronglyMeasurable.integral_kernel (κ := K ×ₖ K)).measurable
  have H' := H.stronglyMeasurable.integral_prod_right' (ν := d)
  convert H'.measurable using 1
  funext x
  rw [he]
  simp only [Kernel.prod_apply,Function.comp_def]

theorem parameterized_corrected_sum_measurable (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {means : X → Fin (n+1) → ℝ} (hmean : ∀ j, Measurable (fun x ↦ means x j)) :
    Measurable (fun p : X×(Fin (n+1) → V) ↦ ∑ l, correctedScore n overlap psi (means p.1) p.2 l) := by
  have H := corrected_sum_measurable n hR hpsi (fun _ ↦ 0)
  have HM : Measurable (fun x : X ↦ ∑ l, means x l) := Finset.measurable_sum _ (fun l _ ↦ hmean l)
  convert ((H.comp measurable_snd).add (HM.comp measurable_fst)) using 1
  funext p
  simp only [Function.comp_def,correctedScore,Finset.sum_add_distrib,add_zero,Pi.add_apply]

theorem parameterized_insertion_measurable (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {means : X → Fin (n+1) → ℝ} (hmean : ∀ j, Measurable (fun x ↦ means x j)) :
    Measurable (fun p : X×(Fin (n+2) → V) ↦ firstJetInsertion n overlap psi (means p.1) p.2) := by
  have H := (parameterized_corrected_sum_measurable n hR hpsi hmean).comp
    (measurable_fst.prodMk ((initial_measurable (n+1)).comp measurable_snd))
  have HS : Measurable (fun p : X×(Fin (n+2) → V) ↦
      score n overlap psi (initial p.2) (p.2 (Fin.last (n+1)))) :=
    (score_joint_measurable n hR hpsi).comp
      (((initial_measurable (n+1)).comp measurable_snd).prodMk ((measurable_pi_apply _).comp measurable_snd))
  convert H.sub (HS.const_mul ((n : ℝ)+1)) using 1
  funext p
  rfl

theorem parameterized_weight_measurable
    (K : Kernel (X×Ω) V) [IsMarkovKernel K] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {means : X → Fin (n+1) → ℝ} (hmean : ∀ j, Measurable (fun x ↦ means x j))
    {Phi : X → (Fin (n+1) → V) → ℝ} (hPhi : Measurable (fun p : X×(Fin (n+1) → V) ↦ Phi p.1 p.2))
    {t : X → ℝ} (ht : Measurable t) :
    Measurable (fun p : (X×Ω)×(Fin (n+1) → V) ↦
      Phi p.1.1 p.2*Real.exp (t p.1.1*(∑ l, correctedScore n overlap psi (means p.1.1) p.2 l))/
        (∫ v, Real.exp (t p.1.1*score n overlap psi p.2 v) ∂K p.1)^(n+1)) := by
  let P := (X×Ω)×(Fin (n+1) → V)
  have hT : Measurable (fun p : P ↦ t p.1.1) := ht.comp measurable_fst.fst
  have hS : Measurable (fun p : P×V ↦ score n overlap psi p.1.2 p.2) :=
    (score_joint_measurable n hR hpsi).comp (measurable_fst.snd.prodMk measurable_snd)
  let kap : Kernel P V := K.comap Prod.fst measurable_fst
  have hZ : Measurable (fun p : P ↦ ∫ v, Real.exp (t p.1.1*score n overlap psi p.2 v) ∂K p.1) := by
    simpa only [kap,Kernel.comap_apply,Function.comp_def,Pi.mul_apply] using
      (((hT.comp measurable_fst).mul hS).exp.stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable
  have hH : Measurable (fun p : P ↦ ∑ l, correctedScore n overlap psi (means p.1.1) p.2 l) := by
    convert (parameterized_corrected_sum_measurable n hR hpsi hmean).comp (measurable_fst.fst.prodMk measurable_snd) using 1
    rfl
  have hP : Measurable (fun p : P ↦ Phi p.1.1 p.2) := by
    convert hPhi.comp (measurable_fst.fst.prodMk measurable_snd) using 1
    rfl
  convert (hP.mul (hT.mul hH).exp).div (hZ.pow_const (n+1)) using 1

theorem parameterized_expectation_measurable (d : Measure Ω) [IsProbabilityMeasure d]
    (K : Kernel (X×Ω) V) [IsMarkovKernel K] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {means : X → Fin (n+1) → ℝ} (hmean : ∀ j, Measurable (fun x ↦ means x j))
    {Phi : X → (Fin (n+1) → V) → ℝ} (hPhi : Measurable (fun p : X×(Fin (n+1) → V) ↦ Phi p.1 p.2))
    {t : X → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ reweightingExpectation n d (K.sectR x) overlap psi (means x) (Phi x) (t x)) := by
  let W : (X×Ω)×(Fin (n+1) → V) → ℝ := fun p ↦ Phi p.1.1 p.2*Real.exp (t p.1.1*(∑ l, correctedScore n overlap psi (means p.1.1) p.2 l))/
    (∫ v, Real.exp (t p.1.1*score n overlap psi p.2 v) ∂K p.1)^(n+1)
  have HW : Measurable W := parameterized_weight_measurable K n hR hpsi hmean hPhi ht
  have HI : Measurable (fun p : X×Ω ↦ ∫ old, W (p,old) ∂iid K (n+1) p) :=
    (HW.stronglyMeasurable.integral_kernel_prod_right' (κ := iid K (n+1))).measurable
  have H : Measurable (fun x ↦ ∫ w, ∫ old, W ((x,w),old) ∂iid K (n+1) (x,w) ∂d) :=
    (HI.stronglyMeasurable.integral_prod_right' (ν := d)).measurable
  convert H using 1
  funext x
  unfold reweightingExpectation
  apply integral_congr_ae
  refine Eventually.of_forall (fun w ↦ ?_)
  simp only [W,iid_apply,reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,
    Kernel.sectR_apply]

theorem parameterized_jet_measurable (d : Measure Ω) [IsProbabilityMeasure d]
    (K : Kernel (X×Ω) V) [IsMarkovKernel K] (k n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {means : X → Fin (n+1) → ℝ} (hmean : ∀ j, Measurable (fun x ↦ means x j))
    {Phi : X → (Fin (n+1) → V) → ℝ} (hPhi : Measurable (fun p : X×(Fin (n+1) → V) ↦ Phi p.1 p.2))
    {t : X → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ reweightingJet d (K.sectR x) overlap k n psi (means x) (Phi x) (t x)) := by
  induction k generalizing n with
  | zero => exact parameterized_expectation_measurable d K n hR hpsi hmean hPhi ht
  | succ k ih =>
    have hmean' : ∀ j : Fin (n+2), Measurable (fun x ↦ (Fin.snoc (means x) 0 : Fin (n+2) → ℝ) j) := by
      intro j
      refine Fin.lastCases ?_ (fun l ↦ ?_) j
      · simpa only [Fin.snoc_last] using (measurable_const : Measurable (fun _ : X ↦ (0 : ℝ)))
      · simpa only [Fin.snoc_castSucc] using hmean l
    have hPhi' : Measurable (fun p : X×(Fin (n+2) → V) ↦
        Phi p.1 (initial p.2)*firstJetInsertion n overlap psi (means p.1) p.2) :=
      (hPhi.comp (measurable_fst.prodMk ((initial_measurable _).comp measurable_snd))).mul
        (parameterized_insertion_measurable n hR hpsi hmean)
    exact ih (n+1) (snoc_zero_measurable hpsi) hmean' hPhi'


end
end TensorPCA.NonRSLowerProofs.GGFiniteParameterizedJets
