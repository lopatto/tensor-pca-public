-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGeometry
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceCovarianceBounds
public import TensorPCA.NonRSLowerProofs.FiniteCavityIdealField
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility

/-! Pointwise covariance error between the normalized reference slice feature and the
independent Euclidean bulk-plus-ideal cavity feature. The retained measure and all
pressure comparisons are separate consumers.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGramBounds
open Set FiniteCavityReferenceLaw FiniteCavityReferenceGeometry
open FiniteCavityReferenceCovarianceBounds FiniteCavityIdealField FiniteCavityGaussianCompatibility
open GaussianCompactFeatureComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem bulkFeature_inner_eq {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    inner ℝ (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x)
      (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) y)=
      ((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu ((N : ℝ)/((N : ℝ)+M)*inner ℝ x y) := by
  have H := enlarged_slice_bulk_covariance hM k hmu beta x y
  rw [actualGaussian_thermal_slice_covariance k hmu,bulkEmbedding_inner,actualGaussian_linear_covariance] at H
  calc
    _ = beta^2*((N+M : ℕ) : ℝ)*Scalar.xiSlice k mu (FiniteCavityCompensator.bulkRatio N M*inner ℝ x y) := H.symm
    _ = _ := by rw [Nat.cast_add]; unfold FiniteCavityCompensator.bulkRatio; ring

private theorem sumJoin_inner {I J : Type*} [Fintype I] [Fintype J]
    (a c : EuclideanSpace ℝ I) (b d : EuclideanSpace ℝ J) :
    inner ℝ (sumJoin (a,b)) (sumJoin (c,d))=inner ℝ a c+inner ℝ b d := by
  simp only [sumJoin,PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

private theorem sumJoin_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (a : EuclideanSpace ℝ I) (b : EuclideanSpace ℝ J) : ‖sumJoin (a,b)‖≤‖a‖+‖b‖ := by
  have hs : ‖sumJoin (a,b)‖^2=‖a‖^2+‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq,sumJoin_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith only [hs,norm_nonneg (sumJoin (a,b)),norm_nonneg a,norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b)]

/-- The ideal comparison feature uses independent Euclidean bulk and cavity banks. The
radius coordinate is ignored by this feature.
-/
def idealReferenceFeature (N M k : ℕ) (mu beta : ℝ) (z : Model.Vector N×(ℝ×Model.Vector M)) :
    EuclideanSpace ℝ (GroundState.Coordinate N k⊕IdealCoordinate N M k) :=
  sumJoin (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
    (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) z.1,
    cavityFeature k mu beta z.2.2 z.1)

theorem idealReferenceFeature_continuous (N M k : ℕ) (mu beta : ℝ) :
    Continuous (idealReferenceFeature N M k mu beta) := by
  have hb : Continuous (fun x : Model.Vector N => bulkFeature M (fun p : Fin k => (p : ℕ)+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x) := by
    unfold bulkFeature
    exact NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _
  have hc : Continuous (fun z : Model.Vector N×(ℝ×Model.Vector M) => cavityFeature k mu beta z.2.2 z.1) :=
    (cavityFeature_joint_continuous N M k mu beta).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact sumJoin.continuous.comp ((hb.comp continuous_fst).prodMk hc)

theorem idealReferenceFeature_measurable (N M k : ℕ) (mu beta : ℝ) :
    Measurable (idealReferenceFeature N M k mu beta) := (idealReferenceFeature_continuous N M k mu beta).measurable

theorem bulkFeature_norm_on_unit {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    ‖bulkFeature M (fun p : Fin k => (p : ℕ)+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x‖=
      Real.sqrt (((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu ((N : ℝ)/((N : ℝ)+M))) := by
  calc
    _ = Real.sqrt (‖bulkFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by
      congr 1
      rw [← real_inner_self_eq_norm_sq,bulkFeature_inner_eq hM k hmu beta,
        real_inner_self_eq_norm_sq,show ‖x‖=1 from hx,one_pow,mul_one]

theorem idealReferenceFeature_norm_le {N M : ℕ} (hM : 0<M) (k : ℕ) {mu L : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hL : 0≤L)
    {z : Model.Vector N×(ℝ×Model.Vector M)} (hx : z.1∈Model.unitSphere N) (heta : ‖z.2.2‖^2≤L) :
    ‖idealReferenceFeature N M k mu beta z‖≤
      Real.sqrt (((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu ((N : ℝ)/((N : ℝ)+M)))+
        Real.sqrt L*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  unfold idealReferenceFeature
  calc
    _ ≤ ‖bulkFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) z.1‖+‖cavityFeature k mu beta z.2.2 z.1‖ := sumJoin_norm_le _ _
    _ ≤ _ := by
      rw [bulkFeature_norm_on_unit hM k hmu beta hx]
      exact add_le_add le_rfl (cavityFeature_norm_le k hmu beta hL z.2.2 heta hx)

theorem reference_minus_bulk_ideal_gram_error {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) (hk : 3≤k) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    {delta e r r' : ℝ} (hdelta : 0≤delta) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ))
    {x y : Model.Vector N} (hx : x∈Model.unitSphere N) (hy : y∈Model.unitSphere N)
    (hr : 0≤r) (hr' : 0≤r') (eta eta' : Model.Vector M)
    (hs : ‖eta‖^2∈Icc (M : ℝ) ((M : ℝ)*(1+delta)))
    (hs' : ‖eta'‖^2∈Icc (M : ℝ) ((M : ℝ)*(1+delta)))
    (hbox : r^2/(N : ℝ)∈Icc (1-e) (1+e)) (hbox' : r'^2/(N : ℝ)∈Icc (1-e) (1+e)) :
    let L := (M : ℝ)*(1+delta)
    |inner ℝ (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (x,(r,eta))))
        (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (y,(r',eta'))))-
      inner ℝ (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x)
        (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) y)-
      inner ℝ (cavityFeature k mu beta eta x) (cavityFeature k mu beta eta' y)|≤
      ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ) := by
  have hR : |inner ℝ x y|≤1 := (abs_real_inner_le_norm x y).trans_eq (by rw [hx,hy,mul_one])
  have hc : (inner ℝ eta eta')^2≤‖eta‖^2*‖eta'‖^2 := by
    simpa only [sq_abs,mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm eta eta') 2
  have H := thermal_xiSlice_reference_covariance_error_delta k hk hmu (Nat.cast_pos.mpr hN)
    (Nat.cast_nonneg M) hdelta he0 he1 hscale hr hr' hs hs' hbox hbox' hR hc beta
  dsimp only at H ⊢
  rw [reference_sliceFeature_inner k hmu beta hx hy,bulkFeature_inner_eq hM k hmu beta,
    cavityFeature_inner k hmu beta]
  convert H using 1 <;> ring

theorem reference_minus_joined_ideal_gram_error {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) (hk : 3≤k) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    {delta e r r' : ℝ} (hdelta : 0≤delta) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ))
    {x y : Model.Vector N} (hx : x∈Model.unitSphere N) (hy : y∈Model.unitSphere N)
    (hr : 0≤r) (hr' : 0≤r') (eta eta' : Model.Vector M)
    (hs : ‖eta‖^2∈Icc (M : ℝ) ((M : ℝ)*(1+delta)))
    (hs' : ‖eta'‖^2∈Icc (M : ℝ) ((M : ℝ)*(1+delta)))
    (hbox : r^2/(N : ℝ)∈Icc (1-e) (1+e)) (hbox' : r'^2/(N : ℝ)∈Icc (1-e) (1+e)) :
    let L := (M : ℝ)*(1+delta)
    |inner ℝ (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (x,(r,eta))))
        (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (y,(r',eta'))))-
      inner ℝ (sumJoin (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x,cavityFeature k mu beta eta x))
        (sumJoin (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) y,cavityFeature k mu beta eta' y))|≤
      ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ) := by
  dsimp only
  rw [sumJoin_inner]
  have H := reference_minus_bulk_ideal_gram_error hN hM k hk hmu beta hdelta he0 he1 hscale hx hy hr hr' eta eta' hs hs' hbox hbox'
  dsimp only at H
  convert H using 1 <;> ring

theorem reference_idealReferenceFeature_gram_error {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) (hk : 3≤k) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    {delta e r r' : ℝ} (hdelta : 0≤delta) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ))
    {x y : Model.Vector N} (hx : x∈Model.unitSphere N) (hy : y∈Model.unitSphere N)
    (hr : 0≤r) (hr' : 0≤r') (eta eta' : Model.Vector M)
    (hs : ‖eta‖^2∈Icc (M : ℝ) ((M : ℝ)*(1+delta)))
    (hs' : ‖eta'‖^2∈Icc (M : ℝ) ((M : ℝ)*(1+delta)))
    (hbox : r^2/(N : ℝ)∈Icc (1-e) (1+e)) (hbox' : r'^2/(N : ℝ)∈Icc (1-e) (1+e)) :
    let L := (M : ℝ)*(1+delta)
    |inner ℝ (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (x,(r,eta))))
        (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (y,(r',eta'))))-
      inner ℝ (idealReferenceFeature N M k mu beta (x,(r,eta)))
        (idealReferenceFeature N M k mu beta (y,(r',eta')))|≤
      ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ) := by
  exact reference_minus_joined_ideal_gram_error hN hM k hk hmu beta hdelta he0 he1 hscale hx hy hr hr' eta eta' hs hs' hbox hbox'


end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGramBounds
