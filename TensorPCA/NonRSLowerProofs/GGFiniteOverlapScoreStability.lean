-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteTiltStability
public import TensorPCA.NonRSLowerProofs.GGFiniteParameterizedJets

/-! Iid overlap-score L1 estimates with each ensemble's own averaged pair law. Self-
overlap terms cancel before any pair-law use.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteOverlapScoreStability
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet
open scoped BigOperators
noncomputable section
variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

theorem corrected_difference_l1 (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j)
    (l : Fin (n+1)) :
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let a := fun j ↦ ∫ r, psi j r ∂rho
    let a' := fun j ↦ ∫ r, phi j r ∂rho
    Integrable (fun old ↦ |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l|) (law d G (n+1)) ∧
      (∫ old, |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l| ∂law d G (n+1))≤
        ∑ j, ∫ r, |psi j r-phi j r| ∂rho := by
  dsimp only
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let a : Fin (n+1) → ℝ := fun j ↦ ∫ r, psi j r ∂rho
  let a' : Fin (n+1) → ℝ := fun j ↦ ∫ r, phi j r ∂rho
  let e : Fin (n+1) → ℝ := fun j ↦ ∫ r, |psi j r-phi j r| ∂rho
  let mu := law d G (n+1)
  have hPI (j : Fin (n+1)) : Integrable (psi j) rho := Integrable.of_bound (hpsi j).aestronglyMeasurable (B j)
    (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hpb j r))
  have hFI (j : Fin (n+1)) : Integrable (phi j) rho := Integrable.of_bound (hphi j).aestronglyMeasurable (B j)
    (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hfb j r))
  have hDM (j : Fin (n+1)) : Measurable (fun r ↦ psi j r-phi j r) := by
    convert (hpsi j).sub (hphi j) using 1 <;> rfl
  have hDI (j : Fin (n+1)) : Integrable (fun r ↦ psi j r-phi j r) rho := by
    convert (hPI j).sub (hFI j) using 1 <;> rfl
  have hMean : |a l-a' l|≤e l := by
    change |(∫ r, psi l r ∂rho)-(∫ r, phi l r ∂rho)|≤∫ r, |psi l r-phi l r| ∂rho
    rw [← integral_sub (hPI l) (hFI l)]
    exact abs_integral_le_integral_abs
  have hLaw (i : Fin n) := overlap_hasLaw d G hR (l.succAbove i) l (Fin.ne_succAbove l i).symm
  have hOI (i : Fin n) : Integrable (fun old : Fin (n+1) → V ↦
      psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
        phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))) mu := by
    simpa only [Function.comp_def] using (hLaw i).integrable_comp (hDI (l.succAbove i))
  have hOAI (i : Fin n) : Integrable (fun old : Fin (n+1) → V ↦
      |psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
        phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))|) mu := by
    simpa only [Real.norm_eq_abs] using (hOI i).norm
  have hOEq (i : Fin n) : (∫ old : Fin (n+1) → V,
      |psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
        phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))| ∂mu)=e (l.succAbove i) := by
    simpa only [Function.comp_def] using (hLaw i).integral_comp
      (continuous_abs.measurable.comp (hDM (l.succAbove i))).aestronglyMeasurable
  have he (old : Fin (n+1) → V) : correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l=
      (∑ i : Fin n, (psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
        phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))))+(a l-a' l) := by
    rw [correctedScore_diagonal_cancellation,correctedScore_diagonal_cancellation,Finset.sum_sub_distrib]
    ring
  have hCorrI : Integrable (fun old ↦ correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l) mu := by
    have H := (integrable_finset_sum Finset.univ (fun i _ ↦ hOI i)).add (integrable_const (a l-a' l))
    change Integrable (fun old : Fin (n+1) → V ↦
      (∑ i : Fin n, (psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
        phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))))+(a l-a' l)) mu at H
    exact H.congr (Eventually.of_forall (fun old ↦ (he old).symm))
  have hAbsI : Integrable (fun old ↦ |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l|) mu := by
    simpa only [Real.norm_eq_abs] using hCorrI.norm
  have hpoint (old : Fin (n+1) → V) : |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l|≤
      (∑ i : Fin n, |psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
        phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))|)+|a l-a' l| := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (le_refl _))
  have hRhs := (integrable_finset_sum Finset.univ (fun i _ ↦ hOAI i)).add (integrable_const |a l-a' l|)
  have H := integral_mono hAbsI hRhs hpoint
  change (∫ old, |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l| ∂mu)≤
    ∫ old, (∑ i : Fin n, |psi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))-
      phi (l.succAbove i) (overlap (old (l.succAbove i)) (old l))|)+|a l-a' l| ∂mu at H
  rw [integral_add (integrable_finset_sum Finset.univ (fun i _ ↦ hOAI i)) (integrable_const _),
    integral_finsetSum Finset.univ (fun i _ ↦ hOAI i),integral_const,probReal_univ,one_smul] at H
  simp_rw [hOEq] at H
  refine ⟨hAbsI,H.trans ?_⟩
  calc
    _ ≤ (∑ i : Fin n, e (l.succAbove i))+e l := add_le_add (le_refl _) hMean
    _ = _ := by rw [Fin.sum_univ_succAbove e l]; ring

theorem corrected_sum_difference_l1 (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j) :
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let a := fun j ↦ ∫ r, psi j r ∂rho
    let a' := fun j ↦ ∫ r, phi j r ∂rho
    Integrable (fun old ↦ |(∑ l, correctedScore n overlap psi a old l)-
      (∑ l, correctedScore n overlap phi a' old l)|) (law d G (n+1)) ∧
      (∫ old, |(∑ l, correctedScore n overlap psi a old l)-
        (∑ l, correctedScore n overlap phi a' old l)| ∂law d G (n+1))≤
          ((n : ℝ)+1)*(∑ j, ∫ r, |psi j r-phi j r| ∂rho) := by
  dsimp only
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let a : Fin (n+1) → ℝ := fun j ↦ ∫ r, psi j r ∂rho
  let a' : Fin (n+1) → ℝ := fun j ↦ ∫ r, phi j r ∂rho
  let mu := law d G (n+1)
  have hEach := corrected_difference_l1 d G n hR psi phi hpsi hphi B hpb hfb
  have hSumI : Integrable (fun old ↦ ∑ l, |correctedScore n overlap psi a old l-
      correctedScore n overlap phi a' old l|) mu := integrable_finset_sum Finset.univ (fun l _ ↦ (hEach l).1)
  have hM : Measurable (fun old ↦ |(∑ l, correctedScore n overlap psi a old l)-
      (∑ l, correctedScore n overlap phi a' old l)|) := by
    convert continuous_abs.measurable.comp
      ((GGFiniteReweightingDerivative.corrected_sum_measurable n hR hpsi a).sub
        (GGFiniteReweightingDerivative.corrected_sum_measurable n hR hphi a')) using 1 <;> rfl
  have hpoint (old : Fin (n+1) → V) : |(∑ l, correctedScore n overlap psi a old l)-
      (∑ l, correctedScore n overlap phi a' old l)|≤
        ∑ l, |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hAbsI := hSumI.mono' hM.aestronglyMeasurable (Eventually.of_forall (fun old ↦ by
    rw [Real.norm_eq_abs,abs_abs]
    exact hpoint old))
  refine ⟨hAbsI,?_⟩
  have H := integral_mono hAbsI hSumI hpoint
  rw [integral_finsetSum Finset.univ (fun l _ ↦ (hEach l).1)] at H
  calc
    _ ≤ ∑ l, ∫ old, |correctedScore n overlap psi a old l-correctedScore n overlap phi a' old l| ∂mu := H
    _ ≤ ∑ _l : Fin (n+1), (∑ j, ∫ r, |psi j r-phi j r| ∂rho) := Finset.sum_le_sum (fun l _ ↦ (hEach l).2)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      rfl

theorem fresh_score_difference_l1 (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j) :
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    Integrable (fun s : Fin (n+2) → V ↦ |score n overlap psi (initial s) (s (Fin.last (n+1)))-
      score n overlap phi (initial s) (s (Fin.last (n+1)))|) (law d G (n+2)) ∧
      (∫ s : Fin (n+2) → V, |score n overlap psi (initial s) (s (Fin.last (n+1)))-
        score n overlap phi (initial s) (s (Fin.last (n+1)))| ∂law d G (n+2))≤
          ∑ j, ∫ r, |psi j r-phi j r| ∂rho := by
  dsimp only
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let mu := law d G (n+2)
  have hDM (j : Fin (n+1)) : Measurable (fun r ↦ psi j r-phi j r) := by
    convert (hpsi j).sub (hphi j) using 1 <;> rfl
  have hDb (j : Fin (n+1)) (r : ℝ) : |psi j r-phi j r|≤2*B j := by
    exact (abs_sub _ _).trans (by linarith [hpb j r,hfb j r])
  have hDI (j : Fin (n+1)) : Integrable (fun r ↦ |psi j r-phi j r|) rho := by
    apply Integrable.of_bound (continuous_abs.measurable.comp (hDM j)).aestronglyMeasurable (2*B j)
    exact Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,abs_abs] using hDb j r)
  have hLaw (j : Fin (n+1)) := fresh_overlap_hasLaw d G n hR j
  have hOI (j : Fin (n+1)) : Integrable (fun s : Fin (n+2) → V ↦
      |psi j (overlap (s j.castSucc) (s (Fin.last (n+1))))-
        phi j (overlap (s j.castSucc) (s (Fin.last (n+1))))|) mu := by
    simpa only [Function.comp_def] using (hLaw j).integrable_comp (hDI j)
  have hEq (j : Fin (n+1)) : (∫ s : Fin (n+2) → V,
      |psi j (overlap (s j.castSucc) (s (Fin.last (n+1))))-
        phi j (overlap (s j.castSucc) (s (Fin.last (n+1))))| ∂mu)=∫ r, |psi j r-phi j r| ∂rho := by
    simpa only [Function.comp_def] using (hLaw j).integral_comp
      (continuous_abs.measurable.comp (hDM j)).aestronglyMeasurable
  have hScoreM (f : Fin (n+1) → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) :
      Measurable (fun s : Fin (n+2) → V ↦ score n overlap f (initial s) (s (Fin.last (n+1)))) :=
    (GGFiniteReweightingDerivative.score_joint_measurable n hR hf).comp
      ((initial_measurable _).prodMk (measurable_pi_apply _))
  have hM : Measurable (fun s : Fin (n+2) → V ↦
      |score n overlap psi (initial s) (s (Fin.last (n+1)))-score n overlap phi (initial s) (s (Fin.last (n+1)))|) := by
    convert continuous_abs.measurable.comp ((hScoreM psi hpsi).sub (hScoreM phi hphi)) using 1 <;> rfl
  have hpoint (s : Fin (n+2) → V) :
      |score n overlap psi (initial s) (s (Fin.last (n+1)))-score n overlap phi (initial s) (s (Fin.last (n+1)))|≤
        ∑ j, |psi j (overlap (s j.castSucc) (s (Fin.last (n+1))))-
          phi j (overlap (s j.castSucc) (s (Fin.last (n+1))))| := by
    unfold score
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hSumI := integrable_finset_sum Finset.univ (fun j _ ↦ hOI j)
  have hAbsI := hSumI.mono' hM.aestronglyMeasurable (Eventually.of_forall (fun s ↦ by
    rw [Real.norm_eq_abs,abs_abs]
    exact hpoint s))
  refine ⟨hAbsI,?_⟩
  have H := integral_mono hAbsI hSumI hpoint
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hOI j)] at H
  simpa only [hEq] using H


end
end TensorPCA.NonRSLowerProofs.GGFiniteOverlapScoreStability
