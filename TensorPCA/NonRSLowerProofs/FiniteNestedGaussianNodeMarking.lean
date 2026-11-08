-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianFeature
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMoments
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.ProductMeasure

/-! Literal independent node-noise marking of the existing finite tree.
The outside common Gaussian is kept distinct from fresh child-block noise. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianNodeMarking
open MeasureTheory ProbabilityTheory
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedGaussianFeature
open FiniteNestedGaussianMarkedMoments
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def nodeField {depth n : ℕ} (t : NestedPartition depth n) (y : Fin (depth+1)→ℝ)
    (noise : Coordinate t→E) (i : Fin n) : E := ∑p,values t y i p •noise p

theorem nodeField_continuous {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (i : Fin n) : Continuous (fun noise : Coordinate t→E => nodeField t y noise i) := by
  unfold nodeField
  exact continuous_finset_sum _ (fun p _ => (continuous_apply p).const_smul _)

theorem blockValues_smul_sum {I : Type*} [Fintype I] [DecidableEq I]
    (size : I→ℕ) (C : I→Type*) [∀b,Fintype (C b)]
    (v : (b : I)→Fin (size b)→C b→ℝ) (b : I) (i : Fin (size b))
    (noise : (Σb : I,C b)→E) :
    (∑p : Σb : I,C b,blockValues size C v ⟨b,i⟩ p •noise p)=
      ∑p : C b,v b i p •noise ⟨b,p⟩ := by
  classical
  rw [Fintype.sum_sigma,Finset.sum_eq_single b]
  · simp [blockValues]
  · intro a _ hab
    simp [blockValues,Ne.symm hab]
  · simp

theorem nodeField_succ {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (y : Fin (depth+2)→ℝ)
    (noise : Coordinate (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)→E)
    (b : Fin c.length) (i : Fin (c.partSize b)) :
    nodeField (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) y noise
      (c.equivSigma ⟨b,i⟩)=Real.sqrt (y 0) •noise (Sum.inl PUnit.unit)+
        nodeField (f b) (fun j => y j.succ-y 0) (fun p => noise (Sum.inr ⟨b,p⟩)) i := by
  classical
  unfold nodeField
  change (∑p : PUnit ⊕ Σb : Fin c.length,Coordinate (f b),_)=_
  simp only [values,Equiv.symm_apply_apply,Fintype.sum_sum_type,Fintype.sum_unique,
    Sum.elim_inl,Sum.elim_inr]
  rw [blockValues_smul_sum]

def nodeNoiseSplit {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c) :
    (Coordinate (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)→E) ≃ᵐ
      E×((b : Fin c.length)→Coordinate (f b)→E) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => E)).trans
    ((MeasurableEquiv.funUnique PUnit E).prodCongr
      (MeasurableEquiv.piCurry (fun b (_ : Coordinate (f b)) => E)))

theorem nodeNoiseSplit_preserving {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c) :
    MeasurePreserving (nodeNoiseSplit (E := E) c f)
      (Measure.pi (fun _ : Coordinate (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) => stdGaussian E))
      ((stdGaussian E).prod (Measure.pi (fun b : Fin c.length =>
        Measure.pi (fun _ : Coordinate (f b) => stdGaussian E)))) := by
  have hCurry : MeasurePreserving (MeasurableEquiv.piCurry (fun b (_ : Coordinate (f b)) => E))
      (Measure.pi (fun _ : Σb : Fin c.length,Coordinate (f b) => stdGaussian E))
      (Measure.pi (fun b : Fin c.length => Measure.pi (fun _ : Coordinate (f b) => stdGaussian E))) := by
    refine ⟨(MeasurableEquiv.piCurry _).measurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_piCurry (fun (b : Fin c.length) (_ : Coordinate (f b)) => stdGaussian E))
  exact ((measurePreserving_funUnique (stdGaussian E) PUnit).prod hCurry).comp
    (measurePreserving_sumPiEquivProdPi (fun _ => stdGaussian E))

theorem node_mark_measurable {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) {Z : E→ℝ} (hZ : Measurable Z) (z : E) :
    Measurable (fun noise : Coordinate t→E => ∏i : Fin n,Z (z+nodeField t y noise i)) := by
  apply Finset.measurable_prod
  intro i _
  exact hZ.comp ((continuous_const.add (nodeField_continuous t y i)).measurable)

theorem node_mark_integrable {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    Integrable (fun noise : Coordinate t→E => ∏i : Fin n,Z (z+nodeField t y noise i))
      (Measure.pi (fun _ : Coordinate t => stdGaussian E)) := by
  apply Integrable.of_bound (node_mark_measurable t y hZ z).aestronglyMeasurable (a^n)
  apply ae_of_all
  intro noise
  have hp : 0≤(∏i : Fin n,Z (z+nodeField t y noise i)) :=
    Finset.prod_nonneg (fun i _ => (hb _).1)
  rw [Real.norm_of_nonneg hp]
  calc
    _ ≤ ∏i : Fin n,a := Finset.prod_le_prod₀ (fun i _ => (hb _).1) (fun i _ => (hb _).2)
    _ = a^n := by simp

theorem node_mark_succ {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (y : Fin (depth+2)→ℝ) (Z : E→ℝ) (z : E)
    (noise : Coordinate (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)→E) :
    (∏i : Fin n,Z (z+nodeField (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) y noise i))=
      ∏b : Fin c.length,∏i : Fin (c.partSize b),
        Z ((z+Real.sqrt (y 0) •noise (Sum.inl PUnit.unit))+
          nodeField (f b) (fun j => y j.succ-y 0) (fun p => noise (Sum.inr ⟨b,p⟩)) i) := by
  classical
  have H := Fintype.prod_equiv c.equivSigma
    (fun p : Σb : Fin c.length,Fin (c.partSize b) =>
      Z (z+nodeField (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) y noise (c.equivSigma p)))
    (fun i : Fin n => Z (z+nodeField (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) y noise i))
    (fun _ => rfl)
  rw [← H,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro b _
  apply Finset.prod_congr rfl
  intro i _
  rw [nodeField_succ,add_assoc]

theorem node_mark_split {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (y : Fin (depth+2)→ℝ) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    (∫noise : Coordinate (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)→E,
      ∏i : Fin n,Z (z+nodeField (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) y noise i)
        ∂Measure.pi (fun _ => stdGaussian E))=
      ∫g : E,∏b : Fin c.length,
        ∫noise : Coordinate (f b)→E,∏i : Fin (c.partSize b),
          Z ((z+Real.sqrt (y 0) •g)+nodeField (f b) (fun j => y j.succ-y 0) noise i)
          ∂Measure.pi (fun _ => stdGaussian E) ∂stdGaussian E := by
  classical
  let F := fun p : E×((b : Fin c.length)→Coordinate (f b)→E) =>
    ∏i : Fin n,Z (z+nodeField (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)
      y ((nodeNoiseSplit c f).symm p) i)
  have hF : Integrable F ((stdGaussian E).prod (Measure.pi (fun b : Fin c.length =>
      Measure.pi (fun _ : Coordinate (f b) => stdGaussian E)))) :=
    (nodeNoiseSplit_preserving (E := E) c f).symm.integrable_comp_of_integrable
      (node_mark_integrable (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) y hZ ha hb z)
  calc
    _ = ∫p,F p ∂(stdGaussian E).prod (Measure.pi (fun b : Fin c.length =>
        Measure.pi (fun _ : Coordinate (f b) => stdGaussian E))) := by
      simpa only [F,MeasurableEquiv.symm_apply_apply] using
        (nodeNoiseSplit_preserving (E := E) c f).integral_comp' F
    _ = ∫g : E,∫noise : (b : Fin c.length)→Coordinate (f b)→E,F (g,noise)
        ∂Measure.pi (fun b => Measure.pi (fun _ : Coordinate (f b) => stdGaussian E))
        ∂stdGaussian E := integral_prod _ hF
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro g
      have HE : (fun noise : (b : Fin c.length)→Coordinate (f b)→E => F (g,noise))=
          (fun noise => ∏b : Fin c.length,∏i : Fin (c.partSize b),
            Z ((z+Real.sqrt (y 0) •g)+nodeField (f b) (fun j => y j.succ-y 0) (noise b) i)) := by
        funext noise
        dsimp only [F]
        rw [node_mark_succ]
        rfl
      dsimp only
      rw [HE]
      exact integral_fintype_prod_eq_prod
        (μ := fun b : Fin c.length => Measure.pi (fun _ : Coordinate (f b) => stdGaussian E))
        (fun (b : Fin c.length) (noise : Coordinate (f b)→E) =>
          ∏i : Fin (c.partSize b),Z ((z+Real.sqrt (y 0) •g)+
            nodeField (f b) (fun j => y j.succ-y 0) noise i))

/-- Finite node-noise expectation equals recursive block marking, with one outside
common Gaussian and independent fresh blocks.
-/
theorem node_mark_eq_root_treeMoment {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a)
    (hb : ∀z,0≤Z z ∧ Z z≤a) (z : E) :
    (∫noise : Coordinate t→E,∏i : Fin n,Z (z+nodeField t y noise i)
      ∂Measure.pi (fun _ => stdGaussian E))=
      ∫g : E,treeMoment depth n
        (fun j : Fin depth => Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ E)
        Z (z+Real.sqrt (y 0) •g) t ∂stdGaussian E := by
  classical
  induction depth generalizing n z with
  | zero =>
    have H := (measurePreserving_funUnique (stdGaussian E) PUnit).integral_comp'
      (fun g : E => (Z (z+Real.sqrt (y 0) •g))^n)
    simpa [Coordinate,nodeField,values,treeMoment] using H
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    rw [node_mark_split c f y hZ ha hb z]
    apply integral_congr_ae
    apply ae_of_all
    intro g
    change (∏b : Fin c.length,_)=(∏b : Fin c.length,_)
    apply Finset.prod_congr rfl
    intro b _
    rw [ih (f b) (fun j => y j.succ-y 0) (z+Real.sqrt (y 0) •g)]
    apply integral_congr_ae
    apply ae_of_all
    intro fresh
    dsimp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply]
    congr 1
    funext j
    congr 2
    rw [show j.castSucc.succ=j.succ.castSucc from Fin.ext rfl]
    ring


end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianNodeMarking
