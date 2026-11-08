-- SPDX-License-Identifier: Apache-2.0
/- Exact independent upper-entry splitting adapted from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean (upstream
   openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). The existing actual
   Fin-dimensional UpperIndex representation is reused. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixLaw
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def upperSplit (n : ℕ) : Unit ⊕ (Fin n ⊕ SphericalGaussianJet.UpperIndex n) ≃ SphericalGaussianJet.UpperIndex (n + 1) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl _ => ⟨(0, 0), le_rfl⟩
      | Sum.inr (Sum.inl i) => ⟨(0, i.succ), Fin.zero_le _⟩
      | Sum.inr (Sum.inr p) => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩)
    ⟨by
      intro x y h
      have hz (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      rcases x with u | (i | p) <;> rcases y with v | (j | q)
      all_goals simp_all [Subtype.ext_iff, Prod.ext_iff]
    , by
      rintro ⟨⟨i, j⟩, hij⟩
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact ⟨Sum.inl (), rfl⟩
        | succ j => exact ⟨Sum.inr (Sum.inl j), rfl⟩
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => exact ⟨Sum.inr (Sum.inr ⟨(i, j), Fin.succ_le_succ_iff.mp hij⟩), rfl⟩⟩

@[simp] lemma upperSplit_diag (n : ℕ) : upperSplit n (Sum.inl ()) = ⟨(0, 0), le_rfl⟩ := rfl

@[simp] lemma upperSplit_column (n : ℕ) (i : Fin n) :
    upperSplit n (Sum.inr (Sum.inl i)) = ⟨(0, i.succ), Fin.zero_le _⟩ := rfl

@[simp] lemma upperSplit_tail (n : ℕ) (p : SphericalGaussianJet.UpperIndex n) :
    upperSplit n (Sum.inr (Sum.inr p)) =
      ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩ := rfl

def goeUpperMarginal {m : ℕ} (s : ℝ) (p : SphericalGaussianJet.UpperIndex m) : Measure ℝ :=
  gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)

instance goeUpperMarginal_probability {m : ℕ} (s : ℝ) (p : SphericalGaussianJet.UpperIndex m) :
    IsProbabilityMeasure (goeUpperMarginal s p) := by
  unfold goeUpperMarginal
  infer_instance

def splitUpper (n : ℕ) (a : SphericalGaussianJet.UpperIndex (n + 1) → ℝ) :
    ℝ × ((Fin n → ℝ) × (SphericalGaussianJet.UpperIndex n → ℝ)) :=
  (a ⟨(0, 0), le_rfl⟩, ((fun i => a ⟨(0, i.succ), Fin.zero_le _⟩),
    fun p => a ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩))

lemma splitUpper_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (splitUpper n) (Measure.pi (goeUpperMarginal (m := n + 1) s))
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (Measure.pi (goeUpperMarginal (m := n) s)))) := by
  let μ := goeUpperMarginal (m := n + 1) s
  have h1 := (measurePreserving_piCongrLeft μ (upperSplit n)).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun i => μ (upperSplit n i))
  have h3 := (measurePreserving_piUnique (fun u : Unit => μ (upperSplit n (Sum.inl u)))).prod
    (measurePreserving_sumPiEquivProdPi (fun i => μ (upperSplit n (Sum.inr i))))
  have h := h3.comp (h2.comp h1)
  convert h using 1
  · rfl
  · dsimp [μ, goeUpperMarginal]
    simp only [Fin.succ_inj, (Ne.symm (Fin.succ_ne_zero _)), ite_false]
    rfl


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
