-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGBlockWindowWeights
public import TensorPCA.NonRSLowerProofs.GGFiniteJointReplicaReindex
public import Mathlib.Logic.Equiv.Fin.Basic

/-! One fixed swap of the two literal overlap-window blocks. The first
spin and the complete amplitude/Gaussian state remain unchanged. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGBlockSwap
open MeasureTheory ProbabilityTheory
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteGGBlockWindows FiniteGGBlockWindowArray SphericalGGBlockWindowWeights
open GGFiniteJointReplicaReindex SphericalGGWeightObservable
noncomputable section

def tailSwap (r s : ℕ) : Fin (s+r) ≃ Fin (r+s) :=
  (finSumFinEquiv (m := s) (n := r)).symm |>.trans (Equiv.sumComm (Fin s) (Fin r)) |>.trans finSumFinEquiv

def blockSwap (r s : ℕ) : Fin (s+r+1) ≃ Fin (r+s+1) where
  toFun := Fin.cases 0 (fun j ↦ (tailSwap r s j).succ)
  invFun := Fin.cases 0 (fun j ↦ ((tailSwap r s).symm j).succ)
  left_inv i := by refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  right_inv i := by refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

theorem blockSwap_zero (r s : ℕ) : blockSwap r s 0=0 := rfl

theorem blockSwap_left (r s : ℕ) (i : Fin s) :
    blockSwap r s (Fin.castAdd r i).succ=(Fin.natAdd r i).succ := by
  simp [blockSwap,tailSwap]

theorem blockSwap_right (r s : ℕ) (i : Fin r) :
    blockSwap r s (Fin.natAdd s i).succ=(Fin.castAdd s i).succ := by
  simp [blockSwap,tailSwap]

theorem arrayBlockWindows_swap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r s : ℕ) (A : Fin (r+s+1) → E) (a b c eps cap : ℝ) :
    arrayBlockWindows s r (fun i ↦ A (blockSwap r s i)) b a c eps cap ↔
      arrayBlockWindows r s A a b c eps cap := by
  simp only [arrayBlockWindows,blockSwap_zero,blockSwap_left,blockSwap_right]
  constructor <;> intro H <;> exact blockWindows_swap H

theorem blockWeight_swap {N : ℕ} (r s : ℕ) (A : Fin (r+s+1) → UnitSpin N) (a b c eps cap : ℝ) :
    blockWeight s r b a c eps cap (fun i ↦ A (blockSwap r s i))=blockWeight r s a b c eps cap A := by
  have H := arrayBlockWindows_swap r s (fun i ↦ (A i).val) a b c eps cap
  classical
  unfold blockWeight
  exact if_congr H rfl rfl

theorem blockWeight_integral_swap {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (r s : ℕ) (a b c eps cap : ℝ) :
    (∫ q,blockWeight r s a b c eps cap q.2 ∂jointLaw (K := K) nu v (r+s))=
      ∫ q,blockWeight s r b a c eps cap q.2 ∂jointLaw (K := K) nu v (s+r) := by
  let Phi : (Fin K → ℝ) → (Fin (s+r+1) → UnitSpin N) → ℝ := fun _ old ↦ blockWeight s r b a c eps cap old
  have hM : Measurable (fun q : (Fin K → ℝ)×(Fin (s+r+1) → UnitSpin N) ↦ Phi q.1 q.2) :=
    (blockWeight_measurable N s r b a c eps cap).comp measurable_snd
  have H := old_test_integral_along nu hv (blockSwap r s) Phi hM
  simpa only [Phi,blockWeight_swap] using H

end
end TensorPCA.NonRSLowerProofs.SphericalGGBlockSwap
