-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteFirstJet

/-! Exact anchored GG defect relabeling under the iid replica law. Old permutations fix
the fresh coordinate and transport the original test. No GG equation or reweighting
invariance is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteFirstJetPermutation
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open GGFiniteFirstJet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

private def liftOldPermutation (n : ℕ) (e : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin (n+2)) where
  toFun := Fin.lastCases (Fin.last (n+1)) (fun i ↦ (e i).castSucc)
  invFun := Fin.lastCases (Fin.last (n+1)) (fun i ↦ (e.symm i).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  right_inv i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

private theorem liftOldPermutation_castSucc (n : ℕ) (e : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    liftOldPermutation n e i.castSucc=(e i).castSucc := by simp [liftOldPermutation]

private theorem liftOldPermutation_last (n : ℕ) (e : Equiv.Perm (Fin (n+1))) :
    liftOldPermutation n e (Fin.last (n+1))=Fin.last (n+1) := by simp [liftOldPermutation]

private theorem sum_succAbove_reindex (n : ℕ) (e : Equiv.Perm (Fin (n+1)))
    (j : Fin (n+1)) (f : Fin (n+1) → ℝ) :
    (∑ l : Fin n, f (e (j.succAbove l)))=∑ l : Fin n, f ((e j).succAbove l) := by
  have H := Equiv.sum_comp e f
  rw [Fin.sum_univ_succAbove (fun i ↦ f (e i)) j,Fin.sum_univ_succAbove f (e j)] at H
  linarith

private theorem weighted_integrable {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] {f R : X → ℝ}
    (hf : Measurable f) (hfb : ∀ s, |f s|≤1) (hR : Measurable R)
    {psi : ℝ → ℝ} (hp : Measurable psi) {B : ℝ} (hb : ∀ r, |psi r|≤B) :
    Integrable (fun s ↦ f s*psi (R s)) mu := by
  apply Integrable.of_bound (hf.mul (hp.comp hR)).aestronglyMeasurable B
  exact Eventually.of_forall (fun s ↦ by
    change |f s*psi (R s)|≤B
    rw [abs_mul]
    exact (mul_le_mul (hfb s) (hb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul B))

theorem anchored_discrepancy_reindex (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    (psi : ℝ → ℝ) (hpsi : Measurable psi) {B : ℝ} (hb : ∀ r, |psi r|≤B)
    (e : Equiv.Perm (Fin (n+1))) (j : Fin (n+1)) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    discrepancy n mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ overlap (s j.castSucc) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s j.castSucc) (s (j.succAbove l).castSucc)) psi=
    discrepancy n mu rho (fun s ↦ Phi (fun i ↦ s (e i).castSucc))
      (fun s ↦ overlap (s (e j).castSucc) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s (e j).castSucc) (s ((e j).succAbove l).castSucc)) psi := by
  dsimp only
  let mu := law d G (n+2)
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  let f1 : (Fin (n+2) → V) → ℝ := fun s ↦ Phi (initial s)
  let f2 : (Fin (n+2) → V) → ℝ := fun s ↦ Phi (fun i ↦ s (e i).castSucc)
  let T : (Fin (n+2) → V) → (Fin (n+2) → V) := fun s i ↦ s (liftOldPermutation n e i)
  have hfm1 : Measurable f1 := hPhi.comp (initial_measurable (n+1))
  have hfm2 : Measurable f2 := hPhi.comp (Measurable.of_eval (fun i ↦ measurable_pi_apply (e i).castSucc))
  have hfb1 (s : Fin (n+2) → V) : |f1 s|≤1 := hPb _
  have hfb2 (s : Fin (n+2) → V) : |f2 s|≤1 := hPb _
  have hRm (i k : Fin (n+2)) : Measurable (fun s : Fin (n+2) → V ↦ overlap (s i) (s k)) := by
    simpa only [Function.comp_def] using hR.comp
      (show Measurable (fun s : Fin (n+2) → V ↦ (s i,s k)) from
        (measurable_pi_apply i).prodMk (measurable_pi_apply k))
  have hperm : HasLaw T mu mu := replica_permutation_hasLaw d G (n+2) (liftOldPermutation n e)
  have hpref (s : Fin (n+2) → V) : f1 (T s)=f2 s := by
    dsimp only [f1,f2,T,initial]
    congr 1
    funext i
    change s (liftOldPermutation n e i.castSucc)=s (e i).castSucc
    rw [liftOldPermutation_castSucc]
  have hF : (∫ s, f1 s ∂mu)=∫ s, f2 s ∂mu := by
    have H := hperm.integral_comp hfm1.aestronglyMeasurable
    simpa only [Function.comp_def,hpref] using H.symm
  have hFresh : (∫ s, f1 s*psi (overlap (s j.castSucc) (s (Fin.last (n+1)))) ∂mu)=
      ∫ s, f2 s*psi (overlap (s (e j).castSucc) (s (Fin.last (n+1)))) ∂mu := by
    have H := hperm.integral_comp (hfm1.mul (hpsi.comp (hRm j.castSucc (Fin.last (n+1))))).aestronglyMeasurable
    simpa only [Function.comp_def,Pi.mul_apply,hpref,T,liftOldPermutation_castSucc,liftOldPermutation_last] using H.symm
  have hi1 (l : Fin n) := weighted_integrable mu hfm1 hfb1 (hRm j.castSucc (j.succAbove l).castSucc) hpsi hb
  have hi2 (l : Fin n) := weighted_integrable mu hfm2 hfb2 (hRm (e j).castSucc ((e j).succAbove l).castSucc) hpsi hb
  have hOld : (∑ l : Fin n, ∫ s, f1 s*psi (overlap (s j.castSucc) (s (j.succAbove l).castSucc)) ∂mu)=
      ∑ l : Fin n, ∫ s, f2 s*psi (overlap (s (e j).castSucc) (s ((e j).succAbove l).castSucc)) ∂mu := by
    have H := hperm.integral_comp (Finset.measurable_sum Finset.univ
      (fun l _ ↦ hfm1.mul (hpsi.comp (hRm j.castSucc (j.succAbove l).castSucc)))).aestronglyMeasurable
    have heq (s : Fin (n+2) → V) :
        (∑ l : Fin n, f1 (T s)*psi (overlap ((T s) j.castSucc) ((T s) (j.succAbove l).castSucc)))=
        ∑ l : Fin n, f2 s*psi (overlap (s (e j).castSucc) (s ((e j).succAbove l).castSucc)) := by
      simp only [hpref,T,liftOldPermutation_castSucc]
      rw [← Finset.mul_sum,← Finset.mul_sum]
      exact congrArg (fun v ↦ f2 s*v)
        (sum_succAbove_reindex n e j (fun i ↦ psi (overlap (s (e j).castSucc) (s i.castSucc))))
    change (∫ s, ∑ l : Fin n, f1 (T s)*psi (overlap ((T s) j.castSucc) ((T s) (j.succAbove l).castSucc)) ∂mu)=
      ∫ s, ∑ l : Fin n, f1 s*psi (overlap (s j.castSucc) (s (j.succAbove l).castSucc)) ∂mu at H
    rw [integral_congr_ae (Eventually.of_forall heq),
      integral_finsetSum Finset.univ (fun l _ ↦ hi2 l),
      integral_finsetSum Finset.univ (fun l _ ↦ hi1 l)] at H
    exact H.symm
  change discrepancy n mu rho f1
    (fun s ↦ overlap (s j.castSucc) (s (Fin.last (n+1))))
    (fun l s ↦ overlap (s j.castSucc) (s (j.succAbove l).castSucc)) psi=
    discrepancy n mu rho f2
    (fun s ↦ overlap (s (e j).castSucc) (s (Fin.last (n+1))))
    (fun l s ↦ overlap (s (e j).castSucc) (s ((e j).succAbove l).castSucc)) psi
  unfold discrepancy
  rw [hF,hFresh,hOld]

theorem permuted_test_measurable (n : ℕ) (e : Equiv.Perm (Fin (n+1)))
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) :
    Measurable (fun old : Fin (n+1) → V ↦ Phi (fun i ↦ old (e i))) :=
  hPhi.comp (Measurable.of_eval (fun i ↦ measurable_pi_apply (e i)))

theorem permuted_test_abs_le (n : ℕ) (e : Equiv.Perm (Fin (n+1)))
    {Phi : (Fin (n+1) → V) → ℝ} (hPb : ∀ old, |Phi old|≤1) (old : Fin (n+1) → V) :
    |Phi (fun i ↦ old (e i))|≤1 := hPb _

theorem anchored_discrepancy_eq_first (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    (psi : ℝ → ℝ) (hpsi : Measurable psi) {B : ℝ} (hb : ∀ r, |psi r|≤B) (j : Fin (n+1)) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    discrepancy n mu rho (fun s ↦ Phi (initial s))
      (fun s ↦ overlap (s j.castSucc) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s j.castSucc) (s (j.succAbove l).castSucc)) psi=
    discrepancy n mu rho (fun s ↦ Phi (fun i ↦ s ((Equiv.swap j 0) i).castSucc))
      (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
      (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) psi := by
  simpa only [Equiv.swap_apply_left,Fin.castSucc_zero,Fin.zero_succAbove] using
    anchored_discrepancy_reindex d G n hR Phi hPhi hPb psi hpsi hb (Equiv.swap j 0) j

/-- Finite first-jet cancellation uses first-anchor GG defects with permuted bounded old
tests.
-/
theorem firstJet_expectation_first_anchor (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (Phi : (Fin (n+1) → V) → ℝ) (hPhi : Measurable Phi) (hPb : ∀ s, |Phi s|≤1)
    (psi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) :
    let mu := law d G (n+2)
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let means := fun j ↦ ∫ r, psi j r ∂rho
    (∫ s, Phi (initial s)*firstJetInsertion n overlap psi means s ∂mu)=
      -((n : ℝ)+1)*(∑ j : Fin (n+1), discrepancy n mu rho
        (fun s ↦ Phi (fun i ↦ s ((Equiv.swap j 0) i).castSucc))
        (fun s ↦ overlap (s 0) (s (Fin.last (n+1))))
        (fun l s ↦ overlap (s 0) (s l.succ.castSucc)) (psi j)) := by
  dsimp only
  rw [firstJet_expectation d G n hR Phi hPhi hPb psi hpsi B hb]
  apply congrArg (fun q : ℝ ↦ -((n : ℝ)+1)*q)
  apply Finset.sum_congr rfl
  intro j _
  exact anchored_discrepancy_eq_first d G n hR Phi hPhi hPb (psi j) (hpsi j) (hb j) j

end
end TensorPCA.NonRSLowerProofs.GGFiniteFirstJetPermutation
