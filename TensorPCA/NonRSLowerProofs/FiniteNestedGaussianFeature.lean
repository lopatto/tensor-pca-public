-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionOverlap
public import TensorPCA.RetainedCountProofs.GaussianFiniteFeatures

/-! Scalar Gaussian feature on the finite nodes of the authoritative nested partition.
The root is shared; child coordinates are independent.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianFeature
open MeasureTheory ProbabilityTheory
open FiniteNestedPartition FiniteNestedPartitionOverlap
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Coordinate : {depth n : ℕ}→NestedPartition depth n→Type
  | 0,_,_ => PUnit
  | depth+1,_,t => PUnit ⊕ Σb : Fin t.1.length,Coordinate (t.2 b)

instance coordinateFintype {depth n : ℕ} (t : NestedPartition depth n) :
    Fintype (Coordinate t) := by
  induction depth generalizing n with
  | zero => change Fintype PUnit; infer_instance
  | succ depth ih =>
    change Fintype (PUnit ⊕ Σb : Fin t.1.length,Coordinate (t.2 b))
    letI (b : Fin t.1.length) : Fintype (Coordinate (t.2 b)) := ih (t.2 b)
    infer_instance

def blockValues {I : Type*} [DecidableEq I] (size : I→ℕ) (C : I→Type*)
    (v : (b : I)→Fin (size b)→C b→ℝ) (a : Σb : I,Fin (size b)) :
    (Σb : I,C b)→ℝ := fun p =>
  if h : a.1=p.1 then v p.1 (Fin.cast (congrArg size h) a.2) p.2 else 0

def values : {depth n : ℕ}→(t : NestedPartition depth n)→
    (Fin (depth+1)→ℝ)→Fin n→Coordinate t→ℝ
  | 0,_,_,y,_ => fun _ => Real.sqrt (y 0)
  | depth+1,_,t,y,i => Sum.elim (fun _ => Real.sqrt (y 0))
      (blockValues t.1.partSize (fun b => Coordinate (t.2 b))
        (fun b => values (t.2 b) (fun j => y j.succ-y 0)) (t.1.equivSigma.symm i))

def feature {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (i : Fin n) : EuclideanSpace ℝ (Coordinate t) :=
  WithLp.toLp 2 (values t y i)

theorem blockValues_same {I : Type*} [Fintype I] [DecidableEq I]
    (size : I→ℕ) (C : I→Type*) [∀b,Fintype (C b)]
    (v : (b : I)→Fin (size b)→C b→ℝ) (b : I) (i j : Fin (size b)) :
    (∑p : Σb : I,C b,blockValues size C v ⟨b,i⟩ p*blockValues size C v ⟨b,j⟩ p)=
      ∑p : C b,v b i p*v b j p := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single b]
  · simp [blockValues]
  · intro a _ hab
    simp [blockValues,Ne.symm hab]
  · simp

theorem blockValues_cross {I : Type*} [Fintype I] [DecidableEq I]
    (size : I→ℕ) (C : I→Type*) [∀b,Fintype (C b)]
    (v : (b : I)→Fin (size b)→C b→ℝ) {a b : I} (hab : a≠b)
    (i : Fin (size a)) (j : Fin (size b)) :
    (∑p : Σb : I,C b,blockValues size C v ⟨a,i⟩ p*blockValues size C v ⟨b,j⟩ p)=0 := by
  classical
  apply Finset.sum_eq_zero
  rintro ⟨c,p⟩ _
  by_cases hac : a=c
  · subst c
    simp [blockValues,Ne.symm hab]
  · simp [blockValues,hac]

theorem values_gram {depth n : ℕ} (t : NestedPartition depth n)
    {y : Fin (depth+1)→ℝ} (hy0 : 0≤y 0) (hym : Monotone y) (i j : Fin n) :
    (∑p : Coordinate t,values t y i p*values t y j p)=overlap t y i j := by
  classical
  induction depth generalizing n with
  | zero =>
    change (∑p : PUnit,Real.sqrt (y 0)*Real.sqrt (y 0))=y 0
    simpa only [Fintype.sum_unique,← sq] using Real.sq_sqrt hy0
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
    obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
    have hyshift0 : 0≤y (0 : Fin (depth+1)).succ-y 0 :=
      sub_nonneg.mpr (hym (Fin.zero_le _))
    have hyshift : Monotone (fun l : Fin (depth+1) => y l.succ-y 0) :=
      fun l k hlk => sub_le_sub_right (hym (Fin.succ_le_succ_iff.mpr hlk)) _
    change (∑p : PUnit ⊕ Σb : Fin c.length,Coordinate (f b),_) = _
    simp only [values,Equiv.symm_apply_apply,Fintype.sum_sum_type,Sum.elim_inl,
      Sum.elim_inr,Fintype.sum_unique]
    rw [← sq,Real.sq_sqrt hy0]
    by_cases h : a=b
    · subst b
      rw [blockValues_same,ih (f a) hyshift0 hyshift,overlap_same]
      unfold overlap
      ring
    · rw [blockValues_cross _ _ _ h,overlap_cross c f y h]
      ring

theorem feature_gram {depth n : ℕ} (t : NestedPartition depth n)
    {y : Fin (depth+1)→ℝ} (hy0 : 0≤y 0) (hym : Monotone y) (i j : Fin n) :
    inner ℝ (feature t y i) (feature t y j)=overlap t y i j := by
  simpa only [feature,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm] using
    values_gram t hy0 hym i j

/-- Field of independent standard Gaussian coefficients on finite nodes.
-/
def replicaField {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (g : EuclideanSpace ℝ (Coordinate t)) : Fin n→ℝ :=
  fun i => inner ℝ (feature t y i) g

theorem node_gaussian_product_law {depth n : ℕ} (t : NestedPartition depth n) :
    (stdGaussian (EuclideanSpace ℝ (Coordinate t))).map (fun g => fun c => g c)=
      Measure.pi (fun _ : Coordinate t => gaussianReal 0 1) := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

theorem replicaField_hasGaussianLaw {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) :
    HasGaussianLaw (replicaField t y) (stdGaussian (EuclideanSpace ℝ (Coordinate t))) :=
  IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi (fun i => innerSL ℝ (feature t y i)))

theorem replicaField_mean {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (i : Fin n) :
    (∫g,replicaField t y g i ∂stdGaussian (EuclideanSpace ℝ (Coordinate t)))=0 :=
  integral_strongDual_stdGaussian (innerSL ℝ (feature t y i))

theorem replicaField_covariance {depth n : ℕ} (t : NestedPartition depth n)
    {y : Fin (depth+1)→ℝ} (hy0 : 0≤y 0) (hym : Monotone y) (i j : Fin n) :
    cov[fun g => replicaField t y g i,fun g => replicaField t y g j;
      stdGaussian (EuclideanSpace ℝ (Coordinate t))]=overlap t y i j := by
  unfold replicaField
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  exact feature_gram t hy0 hym i j

/-- Equality of the full finite Gaussian vector laws, not only of covariance. -/
theorem replicaField_law_eq {depth n : ℕ} (t : NestedPartition depth n)
    {y : Fin (depth+1)→ℝ} (hy0 : 0≤y 0) (hym : Monotone y)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Fin n→E→L[ℝ]ℝ)
    (hGram : ∀i j,inner ℝ ((F i).adjoint 1) ((F j).adjoint 1)=overlap t y i j) :
    (stdGaussian (EuclideanSpace ℝ (Coordinate t))).map (replicaField t y)=
      (stdGaussian E).map (fun g i => F i g) := by
  apply RetainedCountProofs.GaussianFiniteFeatures.feature_law_eq
    (fun i => innerSL ℝ (feature t y i)) F
  intro i j
  simpa only [ContinuousLinearMap.adjoint_innerSL_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
    (feature_gram t hy0 hym i j).trans (hGram i j).symm


end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianFeature
