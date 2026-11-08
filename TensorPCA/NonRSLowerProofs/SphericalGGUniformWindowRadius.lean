-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTripleWindowBounds

/-! The small-window radius is chosen before every mass threshold, so the finite-cover
cardinality is determined before the later mass choice.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGUniformWindowRadius
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteGGBlockWindows FiniteGGCloningGeometry
open SphericalGGWeightObservable SphericalGGBlockWindowWeights SphericalGGTripleWindowBounds
noncomputable section

theorem exists_uniform_window_radius {g : ℝ} (hg : 0<g) :
    ∃ eps : ℝ,0<eps ∧ ∀ p : ℝ,p∈Ioc (0 : ℝ) 1 →
      ∀ a b c : ℝ,-1≤c → g≤b-a → b≤c → c≤1-g^2/2 →
        ∃ Q : ℕ,∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
          ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
            (∫ q,blockWeight 1 1 a b c eps (c+eps) q.2 ∂jointLaw (K := K) nu v 2)<p := by
  obtain ⟨epsG,hEpsG,_hEpsGg,hEpsGsq,m,hm,hBudget⟩ := exists_barycenter_contradiction_budget hg
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  refine ⟨epsG/2,half_pos hEpsG,?_⟩
  intro p hp a b c hc hGap hbc hTop
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
end TensorPCA.NonRSLowerProofs.SphericalGGUniformWindowRadius
