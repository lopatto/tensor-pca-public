-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.GaussianReplicaKernel
public import TensorPCA.NonRSUpperProofs.GaussianGGIndicatorTransfer
public import Mathlib.Algebra.BigOperators.Fin

/-! Exact finite first-jet cancellation with iid replica laws. The diagonal self-test
cancels without any diagonal-value hypothesis. No full GG identity or reweighting
invariance is assumed or concluded.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteFirstJet
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

/-- The finite perturbation score, with the anchor first in the overlap. -/
def score (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (old : Fin (n+1) → V) (v : V) : ℝ := ∑ j, psi j (overlap (old j) v)

/-- Correction removes precisely the self-test and inserts the global pair mean. Later
uses instantiate `means` with the averaged two-replica law.
-/
def correctedScore (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (means : Fin (n+1) → ℝ) (old : Fin (n+1) → V) (l : Fin (n+1)) : ℝ :=
  score n overlap psi old (old l)-psi l (overlap (old l) (old l))+means l

def firstJetInsertion (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (means : Fin (n+1) → ℝ) (s : Fin (n+2) → V) : ℝ :=
  (∑ l, correctedScore n overlap psi means (initial s) l)-
    ((n : ℝ)+1)*score n overlap psi (initial s) (s (Fin.last (n+1)))

theorem correctedScore_diagonal_cancellation (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ)
    (old : Fin (n+1) → V) (l : Fin (n+1)) :
    correctedScore n overlap psi means old l=
      (∑ j : Fin n, psi (l.succAbove j) (overlap (old (l.succAbove j)) (old l)))+means l := by
  unfold correctedScore score
  rw [Fin.sum_univ_succAbove _ l]
  ring

theorem firstJetInsertion_eq (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ) (s : Fin (n+2) → V) :
    firstJetInsertion n overlap psi means s=
      ∑ j : Fin (n+1), (means j+
        (∑ l : Fin n, psi j (overlap (s j.castSucc) (s (j.succAbove l).castSucc)))-
        ((n : ℝ)+1)*psi j (overlap (s j.castSucc) (s (Fin.last (n+1))))) := by
  have hcolumns : (∑ j : Fin (n+1), ∑ l : Fin (n+1),
      psi j (overlap (s j.castSucc) (s l.castSucc)))=
      (∑ j : Fin (n+1), psi j (overlap (s j.castSucc) (s j.castSucc)))+
      (∑ j : Fin (n+1), ∑ l : Fin n, psi j (overlap (s j.castSucc) (s (j.succAbove l).castSucc))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Fin.sum_univ_succAbove _ j
  unfold firstJetInsertion correctedScore score
  dsimp only [initial]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [Finset.sum_comm,hcolumns]
  rw [← Finset.mul_sum]
  ring

theorem firstJetInsertion_measurable (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j)) (means : Fin (n+1) → ℝ) :
    Measurable (firstJetInsertion n overlap psi means) := by
  have hm (i j : Fin (n+2)) : Measurable (fun s : Fin (n+2) → V ↦ overlap (s i) (s j)) := by
    simpa only [Function.comp_def] using hR.comp
      (show Measurable (fun s : Fin (n+2) → V ↦ (s i,s j)) from
        (measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hc (l : Fin (n+1)) :
      Measurable (fun s : Fin (n+2) → V ↦ correctedScore n overlap psi means (initial s) l) := by
    exact ((Finset.measurable_sum _ (fun j _ ↦ (hpsi j).comp (hm j.castSucc l.castSucc))).sub
      ((hpsi l).comp (hm l.castSucc l.castSucc))).add measurable_const
  exact (Finset.measurable_sum _ (fun l _ ↦ hc l)).sub
    ((Finset.measurable_sum _ (fun j _ ↦ (hpsi j).comp (hm j.castSucc (Fin.last (n+1))))).const_mul ((n : ℝ)+1))

/-- Finite iid replicas retain every coordinate permutation after averaging over the
original disorder law.
-/
theorem replica_permutation_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) (p : Equiv.Perm (Fin n)) :
    HasLaw (fun s : Fin n → V ↦ fun i ↦ s (p i)) (law d G n) (law d G n) := by
  have hp : Measurable (fun s : Fin n → V ↦ fun i ↦ s (p i)) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (p i))
  have hk : (iid G n).map (fun s : Fin n → V ↦ fun i ↦ s (p i))=iid G n := by
    apply Kernel.ext
    intro w
    simp only [Kernel.map_apply _ hp,iid_apply]
    have H := (measurePreserving_piCongrLeft (fun _ : Fin n ↦ G w) p.symm).map_eq
    convert H using 1
    congr 1
    funext s i
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  refine ⟨hp.aemeasurable,?_⟩
  rw [law,Measure.map_comp _ _ hp,hk]

theorem overlap_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {n : ℕ} (i j : Fin n) (hij : i≠j) :
    HasLaw (fun s : Fin n → V ↦ overlap (s i) (s j))
      (((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)) (law d G n) :=
  (hasLaw_map hR.aemeasurable).fun_comp (pair_hasLaw d G i j hij)

theorem fresh_overlap_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (j : Fin (n+1)) :
    HasLaw (fun s : Fin (n+2) → V ↦ overlap (s j.castSucc) (s (Fin.last (n+1))))
      (((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)) (law d G (n+2)) :=
  overlap_hasLaw d G hR j.castSucc (Fin.last (n+1)) (Fin.castSucc_ne_last j)

theorem old_overlap_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (j : Fin (n+1)) (l : Fin n) :
    HasLaw (fun s : Fin (n+2) → V ↦ overlap (s j.castSucc) (s (j.succAbove l).castSucc))
      (((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)) (law d G (n+2)) := by
  apply overlap_hasLaw d G hR
  intro h
  exact Fin.ne_succAbove j l (Fin.ext (congrArg (fun q : Fin (n+2) ↦ q.val) h))

theorem score_abs_le (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (old : Fin (n+1) → V) (v : V) :
    |score n overlap psi old v|≤∑ j, B j :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ ↦ hb j _))

theorem correctedScore_abs_le (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    (old : Fin (n+1) → V) (l : Fin (n+1)) :
    |correctedScore n overlap psi means old l|≤∑ j, B j := by
  rw [correctedScore_diagonal_cancellation]
  calc
    _ ≤ |∑ j : Fin n, psi (l.succAbove j) (overlap (old (l.succAbove j)) (old l))|+|means l| := abs_add_le _ _
    _ ≤ (∑ j : Fin n, B (l.succAbove j))+B l :=
      add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ ↦ hb _ _))) (hm l)
    _ = _ := by rw [Fin.sum_univ_succAbove B l]; ring

theorem firstJetInsertion_abs_le (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    (s : Fin (n+2) → V) :
    |firstJetInsertion n overlap psi means s|≤2*((n : ℝ)+1)*(∑ j, B j) := by
  have hsum : |∑ l, correctedScore n overlap psi means (initial s) l|≤((n : ℝ)+1)*(∑ j, B j) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun l _ ↦ correctedScore_abs_le n overlap psi means B hb hm (initial s) l)).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  unfold firstJetInsertion
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(n : ℝ)+1)]
  have hf := mul_le_mul_of_nonneg_left
    (score_abs_le n overlap psi B hb (initial s) (s (Fin.last (n+1)))) (by positivity : 0≤(n : ℝ)+1)
  nlinarith [hsum,hf]

theorem prefix_test_mean (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) :
    (∫ s, Phi (initial s) ∂law d G (n+2))=∫ s, Phi s ∂law d G (n+1) :=
  (initial_hasLaw d G (n+1)).integral_comp hPhi.aestronglyMeasurable

private theorem weighted_overlap_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    {psi : ℝ → ℝ} (hpsi : Measurable psi) {B : ℝ} (hb : ∀ r, |psi r|≤B)
    (i j : Fin (n+2)) :
    Integrable (fun s ↦ Phi (initial s)*psi (overlap (s i) (s j))) (law d G (n+2)) := by
  have hp : Measurable (fun s : Fin (n+2) → V ↦ (s i,s j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hm := (hPhi.comp (initial_measurable (n+1))).mul (hpsi.comp (hR.comp hp))
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact Eventually.of_forall (fun s ↦ by
    change |Phi (initial s)*psi (overlap (s i) (s j))|≤B
    rw [abs_mul]
    exact (mul_le_mul (hPb _) (hb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul B))

/-- Exact first-jet expectation in terms of the anchored GG defects. The inserted means
come from the global averaged pair law, not the within-disorder Gibbs measure.
-/
theorem firstJet_expectation (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    (psi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let means := fun j ↦ ∫ r, psi j r ∂rho
    (∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu)=
      -((n : ℝ)+1)*(∑ j : Fin (n+1), discrepancy n mu rho (fun s ↦ Phi (initial s))
        (fun s ↦ overlap (s j.castSucc) (s (Fin.last (n+1))))
        (fun l s ↦ overlap (s j.castSucc) (s (j.succAbove l).castSucc)) (psi j)) := by
  dsimp only
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let means : Fin (n+1) → ℝ := fun j ↦ ∫ r, psi j r ∂rho
  let f : (Fin (n+2) → V) → ℝ := fun s ↦ Phi (initial s)
  have hfm : Measurable f := hPhi.comp (initial_measurable (n+1))
  have hfi : Integrable f mu := Integrable.of_bound hfm.aestronglyMeasurable 1
    (Eventually.of_forall (fun s ↦ by simpa only [f,Real.norm_eq_abs] using hPb (initial s)))
  have hfresh (j : Fin (n+1)) := weighted_overlap_integrable d G n hR hPhi hPb (hpsi j) (hb j)
    j.castSucc (Fin.last (n+1))
  have hold (j : Fin (n+1)) (l : Fin n) := weighted_overlap_integrable d G n hR hPhi hPb (hpsi j) (hb j)
    j.castSucc (j.succAbove l).castSucc
  have hmeans (j : Fin (n+1)) : |means j|≤B j := by
    have H := norm_integral_le_of_norm_le_const (μ := rho) (f := psi j) (C := B j)
      (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hb j r))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hjet : Integrable (fun s ↦ f s*firstJetInsertion n overlap psi means s) mu := by
    apply Integrable.of_bound (hfm.mul (firstJetInsertion_measurable n hR hpsi means)).aestronglyMeasurable
      (2*((n : ℝ)+1)*(∑ j, B j))
    exact Eventually.of_forall (fun s ↦ by
      change |f s*firstJetInsertion n overlap psi means s|≤_
      rw [abs_mul]
      exact (mul_le_mul (hPb _) (firstJetInsertion_abs_le n overlap psi means B hb hmeans s)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  let term (j : Fin (n+1)) (s : Fin (n+2) → V) : ℝ :=
    means j*f s+(∑ l : Fin n, f s*psi j (overlap (s j.castSucc) (s (j.succAbove l).castSucc)))-
      ((n : ℝ)+1)*(f s*psi j (overlap (s j.castSucc) (s (Fin.last (n+1)))))
  have hterm (j : Fin (n+1)) : Integrable (term j) mu :=
    ((hfi.const_mul (means j)).add (integrable_finsetSum Finset.univ (fun l _ ↦ hold j l))).sub
      ((hfresh j).const_mul ((n : ℝ)+1))
  have htermI (j : Fin (n+1)) : (∫ s, term j s ∂mu)=
      means j*(∫ s, f s ∂mu)+
        (∑ l : Fin n, ∫ s, f s*psi j (overlap (s j.castSucc) (s (j.succAbove l).castSucc)) ∂mu)-
        ((n : ℝ)+1)*(∫ s, f s*psi j (overlap (s j.castSucc) (s (Fin.last (n+1)))) ∂mu) := by
    unfold term
    have H := integral_sub ((hfi.const_mul (means j)).add
      (integrable_finsetSum Finset.univ (fun l _ ↦ hold j l))) ((hfresh j).const_mul ((n : ℝ)+1))
    dsimp only [Pi.add_apply] at H
    rw [H,integral_add (hfi.const_mul (means j))
      (integrable_finsetSum Finset.univ (fun l _ ↦ hold j l)),integral_const_mul,integral_const_mul,
      integral_finsetSum Finset.univ (fun l _ ↦ hold j l)]
  change (∫ s, f s*firstJetInsertion n overlap psi means s ∂mu)=_
  calc
    _ = ∫ s, ∑ j, term j s ∂mu := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s ↦ by
        dsimp only
        rw [firstJetInsertion_eq,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [term,mul_add,mul_sub,Finset.mul_sum]
        ring)
    _ = ∑ j, ∫ s, term j s ∂mu := integral_finsetSum Finset.univ (fun j _ ↦ hterm j)
    _ = _ := by
      simp_rw [htermI]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold discrepancy
      dsimp only [means]
      field_simp [show (n : ℝ)+1≠0 by positivity]
      ring

theorem firstJet_expectation_abs_le (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    (psi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let means := fun j ↦ ∫ r, psi j r ∂rho
    |∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu|≤
      ((n : ℝ)+1)*(∑ j : Fin (n+1), |discrepancy n mu rho (fun s ↦ Phi (initial s))
        (fun s ↦ overlap (s j.castSucc) (s (Fin.last (n+1))))
        (fun l s ↦ overlap (s j.castSucc) (s (j.succAbove l).castSucc)) (psi j)|) := by
  dsimp only
  rw [firstJet_expectation d G n hR Phi hPhi hPb psi hpsi B hb,
    abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤(n : ℝ)+1)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

end
end TensorPCA.NonRSLowerProofs.GGFiniteFirstJet
