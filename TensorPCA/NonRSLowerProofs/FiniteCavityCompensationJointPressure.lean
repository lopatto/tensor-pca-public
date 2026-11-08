-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility
public import TensorPCA.NonRSLowerProofs.GaussianFeatureCovarianceComparison

/-! Expected pressure restoration by independent Gaussian bulk and finite compensator
banks. Marginal covariance restoration is expressed as a Euclidean sum/product
integral before Gibbs factorization.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison
open FiniteCavityGaussianCompatibility
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sphere_feature_bound {N : ℕ} (hN : 0<N) {E : Type*} [NormedAddCommGroup E]
    (a : Model.Vector N→E) (ha : Continuous a) :
    ∃K : ℝ,0≤K ∧ ∀ᵐ x∂Model.spherePrior N,‖a x‖≤K := by
  obtain ⟨K,hK⟩ := (Geometry.unitSphere_isCompact N).bddAbove_image ha.norm.continuousOn
  refine ⟨max K 0,le_max_right _ _,?_⟩
  exact (Geometry.spherePrior_norm_ae hN).mono (fun x hx => (hK ⟨x,hx,rfl⟩).trans (le_max_left _ _))

theorem sumJoin_inner {I J : Type*} [Fintype I] [Fintype J]
    (a c : EuclideanSpace ℝ I) (b d : EuclideanSpace ℝ J) :
    inner ℝ (sumJoin (a,b)) (sumJoin (c,d))=inner ℝ a c+inner ℝ b d := by
  simp only [sumJoin,PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

private theorem sumJoin_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (a : EuclideanSpace ℝ I) (b : EuclideanSpace ℝ J) : ‖sumJoin (a,b)‖≤‖a‖+‖b‖ := by
  have hsq : ‖sumJoin (a,b)‖^2=‖a‖^2+‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq,sumJoin_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith only [hsq,norm_nonneg (sumJoin (a,b)),norm_nonneg a,norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem joined_logPartition_product_integrable_and_eq
    {V I J : Type*} [MeasurableSpace V] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (nu : Measure V) [IsProbabilityMeasure nu]
    (a : V→EuclideanSpace ℝ I) (b : V→EuclideanSpace ℝ J)
    (ha : Measurable a) (hb : Measurable b) {KA KB : ℝ} (hKA : 0≤KA) (hKB : 0≤KB)
    (hba : ∀ᵐ x∂nu,‖a x‖≤KA) (hbb : ∀ᵐ x∂nu,‖b x‖≤KB) :
    Integrable (fun p : EuclideanSpace ℝ I×EuclideanSpace ℝ J =>
      Real.log (∫x,Real.exp (inner ℝ (a x) p.1+inner ℝ (b x) p.2)∂nu))
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) ∧
    (∫g,logPartition nu (fun x => innerSL ℝ (sumJoin (a x,b x))) g
      ∂stdGaussian (EuclideanSpace ℝ (I⊕J)))=
      ∫ga,(∫gb,Real.log (∫x,Real.exp (inner ℝ (a x) ga+inner ℝ (b x) gb)∂nu)
        ∂stdGaussian (EuclideanSpace ℝ J))∂stdGaussian (EuclideanSpace ℝ I) := by
  let F := logPartition nu (fun x => innerSL ℝ (sumJoin (a x,b x)))
  let P : EuclideanSpace ℝ I×EuclideanSpace ℝ J→ℝ :=
    fun p => Real.log (∫x,Real.exp (inner ℝ (a x) p.1+inner ℝ (b x) p.2)∂nu)
  have hjoin : Measurable (fun x => sumJoin (a x,b x)) := sumJoin.continuous.measurable.comp (ha.prodMk hb)
  have hbound : ∀ᵐ x∂nu,‖sumJoin (a x,b x)‖≤KA+KB := by
    filter_upwards [hba,hbb] with x hx hy
    exact (sumJoin_norm_le _ _).trans (add_le_add hx hy)
  have hFc : Continuous F := (logPartition_contDiff nu _
    ((innerSL ℝ).continuous.measurable.comp hjoin) (add_nonneg hKA hKB)
    (hbound.mono (fun x hx => by simpa only [Function.comp_apply,innerSL_apply_norm] using hx))).continuous
  have hFi : Integrable F (stdGaussian (EuclideanSpace ℝ (I⊕J))) :=
    feature_logPartition_integrable nu _ hjoin (add_nonneg hKA hKB) hbound
  have hfun (p : EuclideanSpace ℝ I×EuclideanSpace ℝ J) : F (sumJoin p)=P p := by
    rcases p with ⟨ga,gb⟩
    unfold F logPartition GaussianSpinInterpolation.moment weight P
    congr 1
    apply integral_congr_ae
    exact .of_forall fun x => by simp only [one_mul,innerSL_apply_apply,sumJoin_inner]
  have hPc : Continuous P := by
    have hh : P=F ∘ sumJoin := funext (fun p => (hfun p).symm)
    rw [hh]
    exact hFc.comp sumJoin.continuous
  have hsplit : MeasurePreserving (sumSplit (ι := I) (κ := J))
      (stdGaussian (EuclideanSpace ℝ (I⊕J)))
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) := by
    refine ⟨sumSplit.continuous.measurable,?_⟩
    simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using (sumSplit_gaussian_map (ι := I) (κ := J))
  have hid (g : EuclideanSpace ℝ (I⊕J)) : sumJoin (sumSplit g)=g := by
    ext (i|j) <;> rfl
  have hcomp : P ∘ sumSplit=F := funext (fun g => by dsimp only [Function.comp_apply]; rw [← hfun,hid])
  have hPi : Integrable P ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) :=
    (hsplit.integrable_comp hPc.aestronglyMeasurable).1 (by rw [hcomp]; exact hFi)
  refine ⟨hPi,?_⟩
  have hm := integral_map hsplit.measurable.aemeasurable
    (show AEStronglyMeasurable P ((stdGaussian (EuclideanSpace ℝ (I⊕J))).map sumSplit) by
      rw [hsplit.map_eq]; exact hPc.aestronglyMeasurable)
  rw [hsplit.map_eq] at hm
  have hh : (∫p,P p∂(stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J)))=
      ∫g,F g∂stdGaussian (EuclideanSpace ℝ (I⊕J)) := by
    change (∫p,P p∂(stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J)))=
      ∫g,(P ∘ sumSplit) g∂stdGaussian (EuclideanSpace ℝ (I⊕J)) at hm
    rw [hcomp] at hm
    exact hm
  rw [← hh,integral_prod P hPi]

section Actual
variable {N M k : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
local notation "a" => bulkFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "b" => compensatorFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)

theorem bulkFeature_continuous : Continuous a := by
  unfold bulkFeature
  exact NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _

theorem compensatorFeature_continuous : Continuous b := by
  unfold compensatorFeature
  exact (continuous_const : Continuous (fun _ : Model.Vector N => Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
    (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)

include hN hM hmu

theorem joined_compensation_gram (x y : Model.Vector N) :
    inner ℝ (sumJoin (a x,b x)) (sumJoin (a y,b y))=
      inner ℝ (beta • GroundState.sliceFeature k mu x) (beta • GroundState.sliceFeature k mu y) := by
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k mu p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hmu p)
  rw [sumJoin_inner,bulk_add_compensator_inner hN hM _ _ hc,
    NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_inner _ _ hc,
    real_inner_smul_left,real_inner_smul_right,GroundUpperProofs.sliceFeature_inner hmu,VariationalProofs.xiSlice_eq_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem expected_full_logPartition_eq_independent_bulk_compensator :
    (∫g,logPartition (Model.spherePrior N) (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g
      ∂stdGaussian (GroundState.Disorder N k))=
      ∫gB,(∫gE,Real.log (∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (b x) gE)∂Model.spherePrior N)
        ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (GroundState.Disorder N k) := by
  let j := fun x => sumJoin (a x,b x)
  let s := fun x : Model.Vector N => beta • GroundState.sliceFeature k mu x
  have ha := bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hb := compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hj : Continuous j := sumJoin.continuous.comp (ha.prodMk hb)
  have hs : Continuous s := (continuous_const : Continuous (fun _ : Model.Vector N => beta)).smul
    (GroundUpperProofs.continuous_sliceFeature N k mu)
  obtain ⟨Kj,hKj,hbj⟩ := sphere_feature_bound hN j hj
  obtain ⟨Ks,hKs,hbs⟩ := sphere_feature_bound hN s hs
  have H := expected_logPartition_abs_sub_le (Model.spherePrior N) s j hs.measurable hj.measurable hKs hKj hbs hbj
    (ddiag := 0) (dpair := 0)
    (.of_forall fun x => by rw [joined_compensation_gram hN hM hmu beta]; simp only [s,sub_self,abs_zero,le_refl])
    (.of_forall fun p => by rw [joined_compensation_gram hN hM hmu beta]; simp only [s,sub_self,abs_zero,le_refl])
  have heq : (∫g,logPartition (Model.spherePrior N) (fun x => innerSL ℝ (s x)) g
      ∂stdGaussian (GroundState.Disorder N k))=
      ∫g,logPartition (Model.spherePrior N) (fun x => innerSL ℝ (j x)) g
        ∂stdGaussian (EuclideanSpace ℝ (GroundState.Coordinate N k⊕GroundState.Coordinate N k)) := by
    exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa only [zero_add,zero_div] using H))
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  exact heq.trans (joined_logPartition_product_integrable_and_eq (Model.spherePrior N) a b ha.measurable hb.measurable hKa hKb hba hbb).2

end Actual


end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure
