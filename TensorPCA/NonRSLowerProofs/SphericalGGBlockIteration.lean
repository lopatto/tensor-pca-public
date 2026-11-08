-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGBlockWindowWeights

/-! Finite block growth with all degree/strength choices preceding the physical model.
Intermediate probability floors are clipped explicitly.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGBlockIteration
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable SphericalGGBlockWindowWeights
noncomputable section

theorem exists_uniform_finite_block_growth (r s m : ℕ) (a b c eps cap h : ℝ)
    (hh : 0<h) (hCap : -1≤cap) (ha : a+eps≤cap) (hb : b+eps≤cap) (hc : c+eps≤cap)
    {p : ℝ} (hp : p∈Ioc (0 : ℝ) 1) (hFinal : cap+(m : ℝ)*h<1) :
    ∃ Q : ℕ,∃ d : ℝ,0<d ∧ ∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        p≤(∫ q,blockWeight r (s+1) a b c eps cap q.2 ∂jointLaw (K := K) nu v (r+s+1)) →
        d≤∫ q,blockWeight r (s+m+1) a b c eps (cap+(m : ℝ)*h) q.2
          ∂jointLaw (K := K) nu v (r+(s+m)+1) := by
  revert hFinal
  induction m with
  | zero =>
    intro _hFinal
    refine ⟨0,p,hp.1,?_⟩
    intro K _hK
    refine ⟨1,le_refl 1,?_⟩
    intro N nu hnu v hv hMass
    simpa only [Nat.add_zero,Nat.cast_zero,zero_mul,add_zero] using hMass
  | succ m ih =>
    intro hFinal
    let current := cap+(m : ℝ)*h
    let next := cap+((m+1 : ℕ) : ℝ)*h
    have hNext : next=current+h := by dsimp only [next,current]; push_cast; ring
    have hFinPrev : cap+(m : ℝ)*h<1 := by change next<1 at hFinal; linarith only [hNext,hFinal,hh]
    obtain ⟨Q0,d0,hd0,H0⟩ := ih hFinPrev
    let p0 := min d0 1
    have hp0 : p0∈Ioc (0 : ℝ) 1 := ⟨lt_min hd0 zero_lt_one,min_le_right _ _⟩
    have hIncrease : cap≤current := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg m) hh.le)
    have hRow : -1<current+h/3 := by linarith only [hCap,hIncrease,hh]
    have hCut : current+h/3<current+2*h/3 := by linarith only [hh]
    have hUpper : current+2*h/3<1 := by change next<1 at hFinal; linarith only [hNext,hFinal,hh]
    have hCapRow : current<current+h/3 := by linarith only [hh]
    have hCapNext : current≤next := by linarith only [hNext,hh]
    have hPairNext : current+2*h/3≤next := by linarith only [hNext,hh]
    obtain ⟨Q1,d1,hd1,H1⟩ := exists_uniform_block_growth_threshold r (s+m) a b c eps current next
      hRow hCut hUpper hp0 (ha.trans hIncrease) (hb.trans hIncrease) (hc.trans hIncrease)
      hCapRow hCapNext hPairNext
    refine ⟨max Q0 Q1,d1,hd1,?_⟩
    intro K hK
    obtain ⟨V0,hV0,HM0⟩ := H0 K ((Nat.le_max_left Q0 Q1).trans hK)
    obtain ⟨V1,hV1,HM1⟩ := H1 K ((Nat.le_max_right Q0 Q1).trans hK)
    let V := V0+V1
    have hV : 1≤V := by dsimp only [V]; linarith only [hV0,hV1]
    refine ⟨V,hV,?_⟩
    intro N nu hnu v hv hMass
    have hv0 : V0≤v := by dsimp only [V] at hv; linarith only [hv,hV1]
    have hv1 : V1≤v := by dsimp only [V] at hv; linarith only [hv,hV0]
    have hMid : d0≤∫ q,blockWeight r (s+m+1) a b c eps current q.2
        ∂jointLaw (K := K) nu v (r+(s+m)+1) := HM0 nu v hv0 hMass
    have hFloor : p0≤∫ q,blockWeight r (s+m+1) a b c eps current q.2
        ∂jointLaw (K := K) nu v (r+(s+m)+1) := (min_le_left d0 1).trans hMid
    have H := HM1 nu v hv1 hFloor
    simpa only [Nat.add_succ,next] using H

end
end TensorPCA.NonRSLowerProofs.SphericalGGBlockIteration
