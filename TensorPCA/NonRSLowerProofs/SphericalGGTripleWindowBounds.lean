-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGBlockIteration
public import TensorPCA.NonRSLowerProofs.SphericalGGBlockSwap

/-! Two finite block-growth phases and deterministic barycenters make each fixed ordered
non-ultrametric triple window uniformly rare.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTripleWindowBounds
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteGGBlockWindows FiniteGGBlockWindowArray FiniteGGCloningGeometry
open SphericalGGWeightObservable SphericalGGBlockWindowWeights SphericalGGBlockIteration SphericalGGBlockSwap
noncomputable section

theorem square_blockWeight_zero {N m : ℕ} (hm : 0<m) {a b c eps epsG cap g : ℝ}
    (hEpsG : 0≤epsG) (hc : -1≤c) (hGap : g≤|a-b|)
    (hBudget : 2*epsG+Real.sqrt (4/(m : ℝ)+4*epsG)<g)
    (hEps : eps≤epsG) (hCap : cap≤c+epsG) (old : Fin (m+m+1) → UnitSpin N) :
    blockWeight m m a b c eps cap old=0 := by
  by_contra hh
  have H := (blockWeight_ne_zero_iff m m a b c eps cap old).mp hh
  have HW := arrayBlockWindows_weaken H hEps hCap
  exact (blockWindows_impossible_of_gap hm hEpsG hc hGap hBudget
    ((old 0).val) (fun i : Fin m ↦ (old (Fin.castAdd m i).succ).val)
    (fun j : Fin m ↦ (old (Fin.natAdd m j).succ).val)
    (old 0).property (fun i ↦ (old (Fin.castAdd m i).succ).property)
    (fun j ↦ (old (Fin.natAdd m j).succ).property)) HW

theorem exists_uniform_window_threshold_of_budget (k : ℕ) (a b c eps epsG cap h g : ℝ)
    (hh : 0<h) (hCap : -1≤cap) (ha : a+eps≤cap) (hb : b+eps≤cap) (hc : c+eps≤cap)
    (hFinal : cap+2*(k : ℝ)*h<1) (hEpsG : 0≤epsG) (hcLower : -1≤c)
    (hGap : g≤|a-b|) (hBudget : 2*epsG+Real.sqrt (4/((k+1 : ℕ) : ℝ)+4*epsG)<g)
    (hEps : eps≤epsG) (hGeoCap : cap+2*(k : ℝ)*h≤c+epsG) {p : ℝ} (hp : p∈Ioc (0 : ℝ) 1) :
    ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        (∫ q,blockWeight 1 1 a b c eps cap q.2 ∂jointLaw (K := K) nu v 2)<p := by
  let cap1 := cap+(k : ℝ)*h
  let cap2 := cap+2*(k : ℝ)*h
  have hkh : 0≤(k : ℝ)*h := mul_nonneg (Nat.cast_nonneg k) hh.le
  have hFirstFinal : cap+(k : ℝ)*h<1 := by linarith only [hFinal,hkh]
  obtain ⟨Q0,d0,hd0,H0⟩ := exists_uniform_finite_block_growth 1 0 k a b c eps cap h hh hCap ha hb hc hp hFirstFinal
  let p1 := min d0 1
  have hp1 : p1∈Ioc (0 : ℝ) 1 := ⟨lt_min hd0 zero_lt_one,min_le_right _ _⟩
  have hCap1 : cap≤cap1 := le_add_of_nonneg_right hkh
  have hSecondFinal : cap1+(k : ℝ)*h<1 := by dsimp only [cap1]; linarith only [hFinal]
  obtain ⟨Q1,d1,hd1,H1⟩ := exists_uniform_finite_block_growth (k+1) 0 k b a c eps cap1 h hh
    (hCap.trans hCap1) (hb.trans hCap1) (ha.trans hCap1) (hc.trans hCap1) hp1 hSecondFinal
  refine ⟨max Q0 Q1,?_⟩
  intro K hK
  obtain ⟨V0,hV0,HM0⟩ := H0 K ((Nat.le_max_left Q0 Q1).trans hK)
  obtain ⟨V1,hV1,HM1⟩ := H1 K ((Nat.le_max_right Q0 Q1).trans hK)
  let V := V0+V1
  have hV : 1≤V := by dsimp only [V]; linarith only [hV0,hV1]
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  by_contra hNot
  have hMass : p≤∫ q,blockWeight 1 1 a b c eps cap q.2 ∂jointLaw (K := K) nu v 2 := le_of_not_gt hNot
  have hv0 : V0≤v := by dsimp only [V] at hv; linarith only [hv,hV1]
  have hv1 : V1≤v := by dsimp only [V] at hv; linarith only [hv,hV0]
  have hvNonneg : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  have hMid : d0≤∫ q,blockWeight 1 (k+1) a b c eps cap1 q.2 ∂jointLaw (K := K) nu v (1+(k+1)) := by
    have hIndex := congrArg (fun j : ℕ ↦ ∫ q,blockWeight 1 (j+1) a b c eps cap1 q.2
      ∂jointLaw (K := K) nu v (1+(j+1))) (Nat.zero_add k)
    exact (HM0 nu v hv0 hMass).trans_eq hIndex
  rw [blockWeight_integral_swap nu hvNonneg 1 (k+1) a b c eps cap1] at hMid
  have hFloor : p1≤∫ q,blockWeight (k+1) 1 b a c eps cap1 q.2 ∂jointLaw (K := K) nu v ((k+1)+1) :=
    (min_le_left d0 1).trans hMid
  have H := HM1 nu v hv1 hFloor
  have hCapEq : cap1+(k : ℝ)*h=cap2 := by dsimp only [cap1,cap2]; ring
  have hLast : d1≤∫ q,blockWeight (k+1) (k+1) b a c eps cap2 q.2
      ∂jointLaw (K := K) nu v ((k+1)+(k+1)) := by
    rw [hCapEq] at H
    have hIndex := congrArg (fun j : ℕ ↦ ∫ q,blockWeight (k+1) (j+1) b a c eps cap2 q.2
      ∂jointLaw (K := K) nu v ((k+1)+(j+1))) (Nat.zero_add k)
    exact H.trans_eq hIndex
  have hZero (old : Fin ((k+1)+(k+1)+1) → UnitSpin N) : blockWeight (k+1) (k+1) b a c eps cap2 old=0 :=
    square_blockWeight_zero (Nat.succ_pos k) hEpsG hcLower (by simpa only [abs_sub_comm] using hGap) hBudget hEps hGeoCap old
  simp only [hZero,integral_zero] at hLast
  exact (not_le_of_gt hd1) hLast

theorem exists_uniform_small_ordered_window {g p : ℝ} (hg : 0<g) (hp : p∈Ioc (0 : ℝ) 1) :
    ∃ eps : ℝ,0<eps ∧ ∀ a b c : ℝ,-1≤c → g≤b-a → b≤c → c≤1-g^2/2 →
      ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
        ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
          (∫ q,blockWeight 1 1 a b c eps (c+eps) q.2 ∂jointLaw (K := K) nu v 2)<p := by
  obtain ⟨epsG,hEpsG,_hEpsGg,hEpsGsq,m,hm,hBudget⟩ := exists_barycenter_contradiction_budget hg
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  refine ⟨epsG/2,half_pos hEpsG,?_⟩
  intro a b c hc hGap hbc hTop
  have hTop' : c+epsG<1 := by nlinarith only [hTop,hEpsGsq,sq_pos_of_pos hg]
  obtain ⟨h,hh,hCaps⟩ := exists_increasing_cloning_caps hc hEpsG hTop' (2*k)
  dsimp only at hCaps
  have hL := (hCaps.1 (2*k) (le_refl _)).2
  have hEnd : c+epsG/2+2*(k : ℝ)*h<c+epsG := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hL
  have hac : a≤c := by linarith only [hGap,hg,hbc]
  have hGapAbs : g≤|a-b| := hGap.trans ((le_abs_self (b-a)).trans_eq (abs_sub_comm b a))
  exact exists_uniform_window_threshold_of_budget k a b c (epsG/2) epsG (c+epsG/2) h g hh
    (by linarith only [hc,hEpsG]) (add_le_add hac (le_refl _)) (add_le_add hbc (le_refl _)) (le_refl _)
    (hEnd.trans hTop') hEpsG.le hc hGapAbs hBudget (by linarith only [hEpsG]) hEnd.le hp

end
end TensorPCA.NonRSLowerProofs.SphericalGGTripleWindowBounds
