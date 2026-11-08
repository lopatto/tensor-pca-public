-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteDuplication

/-! The physical duplication event as a next-iid-array observable. Both candidate copies
share the original prefix and the same Gibbs kernel.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGCloneExtension
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open GGFiniteFirstJet GGFiniteReplicaSnocIntegration
open SphericalGGWeightObservable SphericalGGLastSpinCandidate SphericalGGFiniteDuplication
open FiniteGGConditionalLowMass
open scoped BigOperators
noncomputable section

private theorem initial_snoc {V : Type*} {m : ℕ} (old : Fin (m+1) → V) (z : V) :
    initial (Fin.snoc old z)=old := by funext j; simp only [initial,Fin.snoc_castSucc]

def cloneOld {N : ℕ} (n : ℕ) (s : Fin (n+3) → UnitSpin N) : Fin (n+2) → UnitSpin N :=
  Fin.snoc (initial (initial s)) (s (Fin.last (n+2)))

def cloneWeight {N K : ℕ} (n : ℕ) (b : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (x : Fin K → ℝ) (s : Fin (n+3) → UnitSpin N) : ℝ := by
  classical
  exact if Phi x (initial s)≠0 ∧ Phi x (cloneOld n s)≠0 ∧
    unitOverlap (s (Fin.last (n+2))) (s (Fin.last (n+1)).castSucc)<b then 1 else 0

theorem cloneOld_measurable (N n : ℕ) : Measurable (cloneOld (N := N) n) :=
  (snoc_measurable n).comp (((initial_measurable _).comp (initial_measurable _)).prodMk (measurable_pi_apply _))

theorem cloneWeight_measurable {N K : ℕ} (n : ℕ) (b : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2)) :
    Measurable (fun p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) ↦ cloneWeight n b Phi p.1 p.2) := by
  classical
  have hFirst : Measurable (fun p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) ↦ Phi p.1 (initial p.2)) := by
    convert hPhi.comp (measurable_fst.prodMk ((initial_measurable (n+2)).comp measurable_snd)) using 1 <;> rfl
  have hSecond : Measurable (fun p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) ↦ Phi p.1 (cloneOld n p.2)) := by
    convert hPhi.comp (measurable_fst.prodMk ((cloneOld_measurable N n).comp measurable_snd)) using 1 <;> rfl
  have hCoords : Measurable (fun p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) ↦
      (p.2 (Fin.last (n+2)),p.2 (Fin.last (n+1)).castSucc)) :=
    ((measurable_pi_apply (Fin.last (n+2))).comp measurable_snd).prodMk
      ((measurable_pi_apply (Fin.last (n+1)).castSucc).comp measurable_snd)
  have hPair : Measurable (fun p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) ↦
      unitOverlap (p.2 (Fin.last (n+2))) (p.2 (Fin.last (n+1)).castSucc)) := by
    convert (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hCoords using 1 <;> rfl
  have hCond : MeasurableSet {p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) |
      Phi p.1 (initial p.2)≠0 ∧ Phi p.1 (cloneOld n p.2)≠0 ∧
        unitOverlap (p.2 (Fin.last (n+2))) (p.2 (Fin.last (n+1)).castSucc)<b} :=
    (((hFirst (measurableSet_singleton (0 : ℝ))).compl).inter
    (((hSecond (measurableSet_singleton (0 : ℝ))).compl).inter (measurableSet_lt hPair measurable_const)))
  have hIte : Measurable (fun p : (Fin K → ℝ)×(Fin (n+3) → UnitSpin N) ↦
      if Phi p.1 (initial p.2)≠0 ∧ Phi p.1 (cloneOld n p.2)≠0 ∧
        unitOverlap (p.2 (Fin.last (n+2))) (p.2 (Fin.last (n+1)).castSucc)<b then (1 : ℝ) else 0) :=
    Measurable.ite hCond measurable_const measurable_const
  convert hIte using 1 <;> rfl

theorem cloneWeight_mem {N K : ℕ} (n : ℕ) (b : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ) (x : Fin K → ℝ) (s : Fin (n+3) → UnitSpin N) :
    cloneWeight n b Phi x s∈Icc (0 : ℝ) 1 := by
  unfold cloneWeight
  split_ifs <;> norm_num

theorem cloneWeight_ne_zero_iff {N K : ℕ} (n : ℕ) (b : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ) (x : Fin K → ℝ) (s : Fin (n+3) → UnitSpin N) :
    cloneWeight n b Phi x s≠0 ↔ Phi x (initial s)≠0 ∧ Phi x (cloneOld n s)≠0 ∧
      unitOverlap (s (Fin.last (n+2))) (s (Fin.last (n+1)).castSucc)<b := by
  classical
  unfold cloneWeight
  split_ifs <;> simp_all

 theorem integral_jointLaw_two_last {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ)
    (F : (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+3) → UnitSpin N)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ q,|F q|≤C) :
    (∫ q,F q ∂jointLaw nu v (n+2))=
      ∫ q,(∫ u,∫ z,F (q.1,Fin.snoc (Fin.snoc q.2 u) z) ∂parameterizedGibbsKernel nu v q.1
        ∂parameterizedGibbsKernel nu v q.1) ∂jointLaw nu v n := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let H : (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N)) → ℝ :=
    fun q ↦ ∫ z,F (q.1,Fin.snoc q.2 z) ∂parameterizedGibbsKernel nu v q.1
  let kap : Kernel (((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N)) (UnitSpin N) :=
    (parameterizedGibbsKernel nu v).comap Prod.fst measurable_fst
  have hHM : Measurable H := by
    have hAppend : Measurable (fun q : ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N))×UnitSpin N) ↦
        (q.1.1,(Fin.snoc q.1.2 q.2 : Fin (n+3) → UnitSpin N))) := by
      convert measurable_fst.fst.prodMk
        ((snoc_measurable (n+1)).comp (measurable_fst.snd.prodMk measurable_snd)) using 1 <;> rfl
    convert ((hF.comp hAppend).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable using 1 <;> rfl
  have hHB (q) : |H q|≤C := by
    have HH := norm_integral_le_of_norm_le_const (μ := parameterizedGibbsKernel nu v q.1)
      (f := fun z ↦ F (q.1,Fin.snoc q.2 z)) (C := C) (.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hB (q.1,Fin.snoc q.2 z)))
    simpa only [H,Real.norm_eq_abs,probReal_univ,mul_one] using HH
  have H1 := integral_joint_iid_snoc ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)))
    (parameterizedGibbsKernel nu v) (n+1) F hF hB
  have H2 := integral_joint_iid_snoc ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)))
    (parameterizedGibbsKernel nu v) n H hHM hHB
  exact H1.trans H2

 theorem cloneWeight_integral_eq_badPairMass {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (b : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2)) :
    (∫ q,cloneWeight n b Phi q.1.1 q.2 ∂jointLaw nu v (n+2))=
      ∫ q,badPairMass (lastKernel nu v n) (eventSupport n Phi) (thresholdPairSet n b) q ∂jointLaw nu v n := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hF : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+3) → UnitSpin N) ↦
      cloneWeight n b Phi q.1.1 q.2) := (cloneWeight_measurable n b Phi hPhi).comp (measurable_fst.fst.prodMk measurable_snd)
  have hFb (q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+3) → UnitSpin N)) : |cloneWeight n b Phi q.1.1 q.2|≤1 := by
    rw [abs_of_nonneg (cloneWeight_mem n b Phi q.1.1 q.2).1]; exact (cloneWeight_mem n b Phi q.1.1 q.2).2
  rw [integral_jointLaw_two_last nu hv n _ hF hFb]
  apply integral_congr_ae
  refine Eventually.of_forall (fun q ↦ ?_)
  let E : Set (UnitSpin N×UnitSpin N) := {r | (q,r.1)∈eventSupport n Phi ∧
    (q,r.2)∈eventSupport n Phi ∧ (q,r)∉thresholdPairSet n b}
  have hOmega := eventSupport_measurable n Phi hPhi
  have hB := thresholdPairSet_measurable N K n b
  have hE : MeasurableSet E := (hOmega.preimage (measurable_const.prodMk measurable_fst)).inter
    ((hOmega.preimage (measurable_const.prodMk measurable_snd)).inter
      (hB.preimage (measurable_const.prodMk measurable_id)).compl)
  have hI : Integrable (E.indicator (fun _ ↦ (1 : ℝ)))
      ((parameterizedGibbsKernel nu v q.1).prod (parameterizedGibbsKernel nu v q.1)) := (integrable_const _).indicator hE
  have hMass : (∫ r,E.indicator (fun _ ↦ (1 : ℝ)) r
      ∂(parameterizedGibbsKernel nu v q.1).prod (parameterizedGibbsKernel nu v q.1))=
      badPairMass (lastKernel nu v n) (eventSupport n Phi) (thresholdPairSet n b) q := by
    simpa only [badPairMass,lastKernel,Kernel.comap_apply,E,smul_eq_mul,mul_one] using integral_indicator_const (1 : ℝ) hE
  rw [← hMass,integral_prod _ hI]
  apply integral_congr_ae
  refine Eventually.of_forall (fun u ↦ ?_)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z ↦ by
    simp only [cloneWeight,cloneOld,initial_snoc,Fin.snoc_last,Fin.snoc_castSucc,E,eventSupport,appendLast,
      thresholdPairSet,indicator_apply,mem_setOf_eq,not_le])

 theorem exists_uniform_clone_extension_threshold (n : ℕ)
    {a b p : ℝ} (ha : -1<a) (hab : a<b) (hb : b<1) (hp : p∈Ioc (0 : ℝ) 1) :
    ∃ Q : ℕ,∃ c : ℝ,0<c ∧ ∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        ∀ Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ,
          Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi q.1 q.2) →
          (∀ x old,Phi x old∈Icc (0 : ℝ) 1) →
          (∀ x old,Phi x old≠0 → ∀ l : Fin (n+1),unitOverlap (old (Fin.last (n+1))) (old l.castSucc)<a) →
          p≤(∫ q,Phi q.1.1 q.2 ∂jointLaw nu v (n+1)) →
          c≤∫ q,cloneWeight n b Phi q.1.1 q.2 ∂jointLaw nu v (n+2) := by
  obtain ⟨Q,c,hc,hMain⟩ := exists_uniform_physical_duplication_threshold n ha hab hb hp
  refine ⟨Q,c,hc,?_⟩
  intro K hK
  obtain ⟨V,hV,hDup⟩ := hMain K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhiM hPhi hSupport hMass
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  rw [cloneWeight_integral_eq_badPairMass nu hv0 n b Phi hPhiM]
  exact hDup nu v hv Phi hPhiM hPhi hSupport hMass

end
end TensorPCA.NonRSLowerProofs.SphericalGGCloneExtension
