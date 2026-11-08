-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGCloneExtension
public import TensorPCA.NonRSLowerProofs.FiniteGGBlockWindowArray

/-! Physical block-window event weights and one-step positive-mass cloning.
Deterministic windows and the law of the next array are established separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGBlockWindowWeights
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGCloneExtension SphericalGGWeightObservable
open FiniteGGBlockWindowArray
open scoped BigOperators
noncomputable section

def blockWeight {N : ℕ} (r s : ℕ) (a b c eps cap : ℝ)
    (old : Fin (r+s+1) → UnitSpin N) : ℝ := by
  classical
  exact if arrayBlockWindows r s (fun i ↦ (old i).val) a b c eps cap then 1 else 0

theorem blockWeight_measurable (N r s : ℕ) (a b c eps cap : ℝ) :
    Measurable (blockWeight (N := N) r s a b c eps cap) := by
  classical
  have hA : Continuous (fun old : Fin (r+s+1) → UnitSpin N ↦ fun i ↦ (old i).val) :=
    continuous_pi (fun i ↦ continuous_subtype_val.comp (continuous_apply i))
  have hSet := ((arrayBlockWindows_isClosed (E := EuclideanSpace ℝ (Fin N)) r s a b c eps cap).preimage hA).measurableSet
  have HH : Measurable (fun old : Fin (r+s+1) → UnitSpin N ↦
      if arrayBlockWindows r s (fun i ↦ (old i).val) a b c eps cap then (1 : ℝ) else 0) :=
    Measurable.ite hSet measurable_const measurable_const
  convert HH using 1 <;> rfl

theorem blockWeight_mem {N : ℕ} (r s : ℕ) (a b c eps cap : ℝ)
    (old : Fin (r+s+1) → UnitSpin N) : blockWeight r s a b c eps cap old∈Icc (0 : ℝ) 1 := by
  unfold blockWeight
  split_ifs <;> norm_num

theorem blockWeight_ne_zero_iff {N : ℕ} (r s : ℕ) (a b c eps cap : ℝ)
    (old : Fin (r+s+1) → UnitSpin N) :
    blockWeight r s a b c eps cap old≠0 ↔ arrayBlockWindows r s (fun i ↦ (old i).val) a b c eps cap := by
  classical
  unfold blockWeight
  split_ifs <;> simp_all

theorem blockWeight_last_row_le {N : ℕ} (r s : ℕ) (a b c eps cap : ℝ)
    (old : Fin (r+s+2) → UnitSpin N) (hW : blockWeight r (s+1) a b c eps cap old≠0)
    (ha : a+eps≤cap) (hb : b+eps≤cap) (hc : c+eps≤cap) (l : Fin (r+s+1)) :
    unitOverlap (old (Fin.last (r+s+1))) (old l.castSucc)≤cap := by
  have H := (blockWeight_ne_zero_iff r (s+1) a b c eps cap old).mp hW
  exact arrayBlockWindows_offdiag_le H ha hb hc _ _ (Fin.castSucc_ne_last l).symm

private theorem val_cloneOld {N : ℕ} (n : ℕ) (v : Fin (n+3) → UnitSpin N) :
    (fun i ↦ (cloneOld n v i).val)=
      Fin.snoc (Fin.init (Fin.init (fun i ↦ (v i).val))) ((v (Fin.last (n+2))).val) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [cloneOld,Fin.snoc_last]
  · simp only [cloneOld,Fin.snoc_castSucc,NonRSUpperProofs.GaussianReplicaKernel.initial,Fin.init]

theorem cloneWeight_le_new_blockWeight {N K : ℕ} (r s : ℕ) (a b c eps cap nextCap pairCut : ℝ)
    (hCap : cap≤nextCap) (hPair : pairCut≤nextCap) (x : Fin K → ℝ)
    (v : Fin (r+s+3) → UnitSpin N) :
    cloneWeight (r+s) pairCut (fun _ old ↦ blockWeight r (s+1) a b c eps cap old) x v≤
      blockWeight r (s+2) a b c eps nextCap v := by
  by_cases hz : cloneWeight (r+s) pairCut (fun _ old ↦ blockWeight r (s+1) a b c eps cap old) x v=0
  · rw [hz]; exact (blockWeight_mem r (s+2) a b c eps nextCap v).1
  · have H := (cloneWeight_ne_zero_iff (r+s) pairCut
      (fun _ old ↦ blockWeight r (s+1) a b c eps cap old) x v).mp hz
    have h0 := (blockWeight_ne_zero_iff r (s+1) a b c eps cap _).mp H.1
    have h1 := (blockWeight_ne_zero_iff r (s+1) a b c eps cap _).mp H.2.1
    have h1' := Eq.mp (congrArg
      (fun A : Fin (r+s+2) → EuclideanSpace ℝ (Fin N) ↦ arrayBlockWindows r (s+1) A a b c eps cap)
      (val_cloneOld (r+s) v)) h1
    have hPair' : inner ℝ ((v (Fin.last (r+s+1)).castSucc).val) ((v (Fin.last (r+s+2))).val)≤nextCap := by
      rw [real_inner_comm]
      exact H.2.2.le.trans hPair
    have hNew := arrayBlockWindows_extend_two_candidates (fun i ↦ (v i).val) a b c eps cap nextCap h0 h1' hCap hPair'
    have hOne : blockWeight r (s+2) a b c eps nextCap v=1 := by
      unfold blockWeight
      exact if_pos hNew
    rw [hOne]
    exact (cloneWeight_mem (r+s) pairCut (fun _ old ↦ blockWeight r (s+1) a b c eps cap old) x v).2

theorem exists_uniform_block_growth_threshold (r s : ℕ) (a b c eps cap nextCap : ℝ)
    {rowCut pairCut p : ℝ} (hRow : -1<rowCut) (hCut : rowCut<pairCut) (hUpper : pairCut<1)
    (hp : p∈Ioc (0 : ℝ) 1) (ha : a+eps≤cap) (hb : b+eps≤cap) (hc : c+eps≤cap)
    (hCapRow : cap<rowCut) (hCapNext : cap≤nextCap) (hPairNext : pairCut≤nextCap) :
    ∃ Q : ℕ,∃ d : ℝ,0<d ∧ ∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        p≤(∫ q,blockWeight r (s+1) a b c eps cap q.2 ∂jointLaw (K := K) nu v (r+s+1)) →
        d≤∫ q,blockWeight r (s+2) a b c eps nextCap q.2 ∂jointLaw (K := K) nu v (r+s+2) := by
  obtain ⟨Q,d,hd,hMain⟩ := exists_uniform_clone_extension_threshold (r+s) hRow hCut hUpper hp
  refine ⟨Q,d,hd,?_⟩
  intro K hK
  obtain ⟨V,hV,hClone⟩ := hMain K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv hMass
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  let Phi : (Fin K → ℝ) → (Fin (r+s+2) → UnitSpin N) → ℝ :=
    fun _x old ↦ blockWeight r (s+1) a b c eps cap old
  have hPhiM : Measurable (fun q : (Fin K → ℝ)×(Fin (r+s+2) → UnitSpin N) ↦ Phi q.1 q.2) :=
    (blockWeight_measurable N r (s+1) a b c eps cap).comp measurable_snd
  have hPhi (x) (old) : Phi x old∈Icc (0 : ℝ) 1 := blockWeight_mem r (s+1) a b c eps cap old
  have hSupport (_x : Fin K → ℝ) (old : Fin (r+s+2) → UnitSpin N) (hh : Phi _x old≠0) (l : Fin (r+s+1)) :
      unitOverlap (old (Fin.last (r+s+1))) (old l.castSucc)<rowCut :=
    (blockWeight_last_row_le r s a b c eps cap old hh ha hb hc l).trans_lt hCapRow
  have H := hClone nu v hv Phi hPhiM hPhi hSupport hMass
  letI := jointLaw_probability nu hv0 (r+s+2) (K := K)
  have hWM : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+s+3) → UnitSpin N) ↦
      blockWeight r (s+2) a b c eps nextCap q.2) :=
    (blockWeight_measurable N r (s+2) a b c eps nextCap).comp measurable_snd
  have hWI : Integrable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+s+3) → UnitSpin N) ↦
      blockWeight r (s+2) a b c eps nextCap q.2) (jointLaw nu v (r+s+2)) := by
    apply Integrable.of_bound hWM.aestronglyMeasurable 1
    exact Eventually.of_forall (fun q ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (blockWeight_mem r (s+2) a b c eps nextCap q.2).1]
      exact (blockWeight_mem r (s+2) a b c eps nextCap q.2).2)
  have hCM : Measurable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+s+3) → UnitSpin N) ↦
      cloneWeight (r+s) pairCut Phi q.1.1 q.2) := by
    convert (cloneWeight_measurable (r+s) pairCut Phi hPhiM).comp
      (measurable_fst.fst.prodMk measurable_snd) using 1 <;> rfl
  have hCI : Integrable (fun q : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (r+s+3) → UnitSpin N) ↦
      cloneWeight (r+s) pairCut Phi q.1.1 q.2) (jointLaw nu v (r+s+2)) := by
    apply Integrable.of_bound hCM.aestronglyMeasurable 1
    exact Eventually.of_forall (fun q ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (cloneWeight_mem (r+s) pairCut Phi q.1.1 q.2).1]
      exact (cloneWeight_mem (r+s) pairCut Phi q.1.1 q.2).2)
  exact H.trans (integral_mono hCI hWI (fun q ↦ cloneWeight_le_new_blockWeight r s a b c eps cap nextCap pairCut hCapNext hPairNext q.1.1 q.2))

end
end TensorPCA.NonRSLowerProofs.SphericalGGBlockWindowWeights
