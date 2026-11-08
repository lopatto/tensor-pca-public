-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteMeasurableCellHeights
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeHeights
public import TensorPCA.NonRSLowerProofs.FiniteNestedStrictSurrogate

/-! One height family for a finite measurable cut partition. Each lower CDF is computed
under the fixed prior and the Gaussian-averaged pair law at that amplitude. The
strict surrogate is glued across cells with their original, unnormalized masses.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGSelectedOwnHeights
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeHeights FiniteNestedStrictSurrogate
open FiniteMeasurableCellHeights
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N K depth : ℕ} {I : Type*} [Fintype I]

def selectedOwnHeights (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ)
    (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ) (tau : ℝ)
    (amp : Fin K→ℝ) : Fin depth→ℝ :=
  gluedHeights cell (fun i amp => strictHeightApprox depth
    (fun l => lowerHeight nu v (cuts i l) amp) tau) amp

theorem selectedOwnHeights_eq_of_mem (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ) (tau : ℝ)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) {i : I} {amp : Fin K→ℝ}
    (hamp : amp∈cell i) : selectedOwnHeights nu v cell cuts tau amp=
      strictHeightApprox depth (fun l => lowerHeight nu v (cuts i l) amp) tau :=
  gluedHeights_eq_of_mem cell _ hDisjoint hamp

theorem selectedOwnHeights_measurable (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ) (tau : ℝ)
    (hCell : ∀i,MeasurableSet (cell i)) : Measurable (selectedOwnHeights nu v cell cuts tau) := by
  apply gluedHeights_measurable cell _ hCell
  intro i
  exact (strictHeightApprox_joint_measurable depth).comp
    ((own_lower_heights_measurable nu hv (cuts i)).prodMk measurable_const)

theorem selectedOwnHeights_positive (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ)
    {tau : ℝ} (htau : 0<tau) (htau1 : tau≤1)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ) :
    ∀amp l,0<selectedOwnHeights nu v cell cuts tau amp l := by
  apply gluedHeights_positive cell _ hDisjoint hCover
  intro i amp _
  exact strictHeightApprox_pos depth _ tau
    (fun l => (lowerHeight_mem_Icc nu hv (cuts i l) amp).1) htau htau1

theorem selectedOwnHeights_strictMono (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ)
    {tau : ℝ} (htau : 0<tau) (htau1 : tau≤1) (hCuts : ∀i,Monotone (cuts i))
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ) :
    ∀amp,StrictMono (selectedOwnHeights nu v cell cuts tau amp) := by
  apply gluedHeights_strictMono cell _ hDisjoint hCover
  intro i amp _
  exact strictHeightApprox_strictMono depth _ tau
    ((own_lower_heights_properties nu hv (cuts i) (hCuts i) amp).2.1) htau htau1

theorem selectedOwnHeights_lt_one (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ)
    {tau : ℝ} (htau : 0<tau) (htau1 : tau≤1)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ) :
    ∀amp l,selectedOwnHeights nu v cell cuts tau amp l<1 := by
  intro amp l
  have hMem : amp∈⋃i,cell i := by rw [hCover]; exact mem_univ amp
  obtain ⟨i,hi⟩ := mem_iUnion.mp hMem
  rw [selectedOwnHeights_eq_of_mem nu v cell cuts tau hDisjoint hi]
  exact strictHeightApprox_lt_one depth _ tau
    (fun l => (lowerHeight_mem_Icc nu hv (cuts i l) amp).2) htau htau1 l

theorem selectedOwnHeights_le_one (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (cell : I→Set (Fin K→ℝ)) (cuts : I→Fin depth→ℝ)
    {tau : ℝ} (htau : 0<tau) (htau1 : tau≤1)
    (hDisjoint : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ) :
    ∀amp l,selectedOwnHeights nu v cell cuts tau amp l≤1 :=
  fun amp l => (selectedOwnHeights_lt_one nu hv cell cuts htau htau1 hDisjoint hCover amp l).le

end
end TensorPCA.NonRSLowerProofs.SphericalGGSelectedOwnHeights
