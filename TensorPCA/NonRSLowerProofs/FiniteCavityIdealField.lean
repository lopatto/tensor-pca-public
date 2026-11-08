-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.SliceDecompositionProofs

/-! The full derivative-covariance cavity field, including xi'(0). It is a tensor power
of the latitude vector, with independent copies for the cavity coordinates. There is
no extra sqrt(N), sqrt(M), or beta.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityIdealField
open MeasureTheory ProbabilityTheory Set SliceDecompositionProofs VariationalProofs
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev IdealCoordinate (N M k : ℕ) := Fin M×(Fin (k-1)→Fin (N+1))

def zFeature {N : ℕ} (k : ℕ) (mu beta : ℝ) (x : Model.Vector N) : Model.Tensor (N+1) (k-1) :=
  (beta*Real.sqrt ((k : ℝ)*(1-mu^2))) • Model.feature (k-1) (sliceVector mu x)

def cavityFeature {N M : ℕ} (k : ℕ) (mu beta : ℝ) (eta : Model.Vector M) (x : Model.Vector N) :
    EuclideanSpace ℝ (IdealCoordinate N M k) :=
  WithLp.toLp 2 (fun I => eta I.1*zFeature k mu beta x I.2)

theorem zFeature_continuous (N k : ℕ) (mu beta : ℝ) : Continuous (zFeature (N := N) k mu beta) := by
  unfold zFeature
  exact (continuous_const : Continuous (fun _ : Model.Vector N => beta*Real.sqrt ((k : ℝ)*(1-mu^2)))).smul
    ((Model.continuous_feature (N+1) (k-1)).comp (continuous_sliceVector N mu))

theorem cavityFeature_joint_continuous (N M k : ℕ) (mu beta : ℝ) :
    Continuous (fun p : Model.Vector N×Model.Vector M => cavityFeature k mu beta p.2 p.1) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro I
  exact ((PiLp.continuous_apply 2 _ I.1).comp continuous_snd).mul
    ((PiLp.continuous_apply 2 _ I.2).comp ((zFeature_continuous N k mu beta).comp continuous_fst))

theorem zFeature_inner {N : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (x y : Model.Vector N) :
    inner ℝ (zFeature k mu beta x) (zFeature k mu beta y)=
      beta^2*deriv (Scalar.xiSlice k mu) (inner ℝ x y) := by
  have hcoef : 0≤(k : ℝ)*(1-mu^2) := mul_nonneg (Nat.cast_nonneg k) (one_sub_sq_nonneg hmu)
  rw [zFeature,zFeature,real_inner_smul_left,real_inner_smul_right,
    Geometry.feature_inner,sliceVector_inner hmu,deriv_xiSlice]
  have hs := Real.sq_sqrt hcoef
  calc
    _ = beta^2*(Real.sqrt ((k : ℝ)*(1-mu^2)))^2*(mu^2+(1-mu^2)*inner ℝ x y)^(k-1) := by ring
    _ = _ := by rw [hs]; ring

theorem cavityFeature_inner {N M : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (eta eta' : Model.Vector M) (x y : Model.Vector N) :
    inner ℝ (cavityFeature k mu beta eta x) (cavityFeature k mu beta eta' y)=
      inner ℝ eta eta'*beta^2*deriv (Scalar.xiSlice k mu) (inner ℝ x y) := by
  have hfactor : inner ℝ (cavityFeature k mu beta eta x) (cavityFeature k mu beta eta' y)=
      inner ℝ eta eta'*inner ℝ (zFeature k mu beta x) (zFeature k mu beta y) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,cavityFeature,Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [hfactor,zFeature_inner k hmu]
  ring

theorem actual_cavity_field_covariance {N M : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (eta eta' : Model.Vector M) (x y : Model.Vector N) :
    cov[fun g => inner ℝ (cavityFeature k mu beta eta x) g,
      fun g => inner ℝ (cavityFeature k mu beta eta' y) g;
      stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k))]=
      inner ℝ eta eta'*beta^2*deriv (Scalar.xiSlice k mu) (inner ℝ x y) := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  exact cavityFeature_inner k hmu beta eta eta' x y

theorem actual_cavity_field_mean_zero {N M : ℕ} (k : ℕ) (mu beta : ℝ)
    (eta : Model.Vector M) (x : Model.Vector N) :
    (∫g,inner ℝ (cavityFeature k mu beta eta x) g
      ∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))=0 :=
  integral_strongDual_stdGaussian (innerSL ℝ (cavityFeature k mu beta eta x))

theorem zFeature_norm {N : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    ‖zFeature k mu beta x‖=|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  rw [zFeature,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),
    Geometry.feature_unit_norm _ (sliceVector_mem_slice hmu hx).1,mul_one,deriv_xiSlice_one]

theorem cavityFeature_norm_sq {N M : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (eta : Model.Vector M) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    ‖cavityFeature k mu beta eta x‖^2=‖eta‖^2*beta^2*deriv (Scalar.xiSlice k mu) 1 := by
  rw [← real_inner_self_eq_norm_sq,cavityFeature_inner k hmu,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,show ‖x‖=1 from hx,one_pow]

theorem cavityFeature_norm {N M : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (eta : Model.Vector M) {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    ‖cavityFeature k mu beta eta x‖=‖eta‖*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  have hd : 0≤deriv (Scalar.xiSlice k mu) 1 := by
    rw [deriv_xiSlice_one]
    exact mul_nonneg (Nat.cast_nonneg k) (one_sub_sq_nonneg hmu)
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [cavityFeature_norm_sq k hmu beta eta hx,mul_pow,mul_pow,sq_abs,Real.sq_sqrt hd]

theorem cavityFeature_norm_le {N M : ℕ} (k : ℕ) {mu L : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (hL : 0≤L) (eta : Model.Vector M) (heta : ‖eta‖^2≤L)
    {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    ‖cavityFeature k mu beta eta x‖≤Real.sqrt L*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  rw [cavityFeature_norm k hmu beta eta hx]
  have hnorm : ‖eta‖≤Real.sqrt L := Real.le_sqrt_of_sq_le heta
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (abs_nonneg beta)) (Real.sqrt_nonneg _)

theorem zFeature_norm_ae {N : ℕ} (hN : 0<N) (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) : ∀ᵐ x ∂Model.spherePrior N,
    ‖zFeature k mu beta x‖=|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) :=
  (Geometry.spherePrior_norm_ae hN).mono (fun x hx => zFeature_norm k hmu beta hx)

theorem cavityFeature_norm_ae_le {N M : ℕ} (hN : 0<N) (k : ℕ) {mu L : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hL : 0≤L) :
    ∀ᵐ p ∂(Model.spherePrior N).prod ((stdGaussian (Model.Vector M)).restrict {eta | ‖eta‖^2≤L}),
      ‖cavityFeature k mu beta p.2 p.1‖≤Real.sqrt L*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_le (cavityFeature_joint_continuous N M k mu beta).norm
    continuous_const).measurableSet).2
  filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
  filter_upwards [ae_restrict_mem (isClosed_le (continuous_norm.pow 2) continuous_const).measurableSet] with eta heta
  exact cavityFeature_norm_le k hmu beta hL eta heta hx

/-- The all-head tensor coordinate is a random constant component with variance beta
squared times xi'(0).
-/
theorem zFeature_head_coordinate {N : ℕ} (k : ℕ) (mu beta : ℝ) (x : Model.Vector N) :
    zFeature k mu beta x (fun _ => 0)=beta*Real.sqrt ((k : ℝ)*(1-mu^2))*mu^(k-1) := by
  simp [zFeature,Model.feature,PiLp.smul_apply,smul_eq_mul,Finset.prod_const]

theorem zFeature_head_variance {N : ℕ} (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) (x : Model.Vector N) :
    (zFeature k mu beta x (fun _ => 0))^2=beta^2*deriv (Scalar.xiSlice k mu) 0 := by
  have hcoef : 0≤(k : ℝ)*(1-mu^2) := mul_nonneg (Nat.cast_nonneg k) (one_sub_sq_nonneg hmu)
  have hp : (mu^(k-1))^2=(mu^2)^(k-1) := by
    rw [← pow_mul,← pow_mul]
    congr 1
    omega
  rw [zFeature_head_coordinate,mul_pow,mul_pow,Real.sq_sqrt hcoef,hp,deriv_xiSlice]
  simp only [mul_zero,add_zero]
  ring


end
end TensorPCA.NonRSLowerProofs.FiniteCavityIdealField
