-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensator
public import TensorPCA.NonRSSphericalGroundUpperTransportProofs
public import TensorPCA.NonRSSphericalGroundTrialTransportProofs

/-! Concrete degree-one-inclusive Gaussian bulk and compensator features. These
identities concern canonical finite Gaussian fields. No cavity free-energy
inequality, limiting law, or ASS representation is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility
open MeasureTheory ProbabilityTheory Set
open FiniteCavityCompensator NonRSUpperProofs
open scoped RealInnerProductSpace BigOperators ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Mixture
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def bulkFeature {N : ℕ} (M : ℕ) (d : σ→ℕ) (c : σ→ℝ) (x : Model.Vector N) :=
  FiniteTensorMixtureMaximum.feature d (fun i => c i*bulkRatio N M^(d i-1)) x

def compensatorFeature {N : ℕ} (M : ℕ) (d : σ→ℕ) (c : σ→ℝ) (x : Model.Vector N) :=
  Real.sqrt ((M : ℝ)/(N : ℝ)) •
    FiniteTensorMixtureMaximum.feature d (fun i => c i*degreeCompensator N M (d i)) x

def limitingCompensatorFeature {N : ℕ} (M : ℕ) (d : σ→ℕ) (c : σ→ℝ) (x : Model.Vector N) :=
  Real.sqrt ((M : ℝ)/(N : ℝ)) •
    FiniteTensorMixtureMaximum.feature d (fun i => c i*((d i-1 : ℕ) : ℝ)) x

theorem bulkFeature_inner {N M : ℕ} (d : σ→ℕ) (c : σ→ℝ)
    (hc : ∀i,0≤c i) (x y : Model.Vector N) :
    inner ℝ (bulkFeature M d c x) (bulkFeature M d c y)=
      (N : ℝ)*∑i,c i*bulkRatio N M^(d i-1)*(inner ℝ x y)^(d i) := by
  exact FiniteTensorMixtureMaximum.feature_inner d _
    (fun i => mul_nonneg (hc i) (pow_nonneg (bulkRatio_nonneg N M) _)) x y

theorem compensatorFeature_inner {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (d : σ→ℕ) (c : σ→ℝ) (hc : ∀i,0≤c i) (x y : Model.Vector N) :
    inner ℝ (compensatorFeature M d c x) (compensatorFeature M d c y)=
      (M : ℝ)*∑i,c i*degreeCompensator N M (d i)*(inner ℝ x y)^(d i) := by
  rw [compensatorFeature,compensatorFeature,real_inner_smul_left,real_inner_smul_right,
    FiniteTensorMixtureMaximum.feature_inner d _
      (fun i => mul_nonneg (hc i) (degreeCompensator_nonneg N (d i) hM))]
  have hs := Real.sq_sqrt (show 0≤(M : ℝ)/(N : ℝ) by positivity)
  have hn : (N : ℝ)≠0 := by positivity
  calc
    _ = (Real.sqrt ((M : ℝ)/(N : ℝ)))^2*(N : ℝ)*
        (∑i,c i*degreeCompensator N M (d i)*(inner ℝ x y)^(d i)) := by ring
    _ = _ := by rw [hs]; field_simp

theorem limitingCompensatorFeature_inner {N : ℕ} (M : ℕ) (hN : 0<N)
    (d : σ→ℕ) (c : σ→ℝ) (hc : ∀i,0≤c i) (x y : Model.Vector N) :
    inner ℝ (limitingCompensatorFeature M d c x) (limitingCompensatorFeature M d c y)=
      (M : ℝ)*∑i,c i*((d i-1 : ℕ) : ℝ)*(inner ℝ x y)^(d i) := by
  rw [limitingCompensatorFeature,limitingCompensatorFeature,real_inner_smul_left,real_inner_smul_right,
    FiniteTensorMixtureMaximum.feature_inner d _
      (fun i => mul_nonneg (hc i) (Nat.cast_nonneg _))]
  have hs := Real.sq_sqrt (show 0≤(M : ℝ)/(N : ℝ) by positivity)
  have hn : (N : ℝ)≠0 := by positivity
  calc
    _ = (Real.sqrt ((M : ℝ)/(N : ℝ)))^2*(N : ℝ)*
        (∑i,c i*((d i-1 : ℕ) : ℝ)*(inner ℝ x y)^(d i)) := by ring
    _ = _ := by rw [hs]; field_simp

theorem bulk_add_compensator_inner {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (d : σ→ℕ) (c : σ→ℝ) (hc : ∀i,0≤c i) (x y : Model.Vector N) :
    inner ℝ (bulkFeature M d c x) (bulkFeature M d c y)+
      inner ℝ (compensatorFeature M d c x) (compensatorFeature M d c y)=
    inner ℝ (FiniteTensorMixtureMaximum.feature d c x) (FiniteTensorMixtureMaximum.feature d c y) := by
  rw [bulkFeature_inner d c hc,compensatorFeature_inner hN hM d c hc,
    FiniteTensorMixtureMaximum.feature_inner d c hc,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he := exact_bulk_compensation N (d i) hM hN
  have hn : (N : ℝ)≠0 := by positivity
  have he' : (N : ℝ)*bulkRatio N M^(d i-1)+(M : ℝ)*degreeCompensator N M (d i)=(N : ℝ) := by
    field_simp at he
    simpa only [mul_comm (bulkRatio N M^(d i-1)) (N : ℝ)] using he
  calc
    _ = ((N : ℝ)*bulkRatio N M^(d i-1)+(M : ℝ)*degreeCompensator N M (d i))*c i*(inner ℝ x y)^(d i) := by ring
    _ = _ := by rw [he']; ring

theorem compensator_covariance_error {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (d : σ→ℕ) (c : σ→ℝ) (hc : ∀i,0≤c i) (hd : ∀i,1≤d i)
    (x y : Model.Vector N) (hxy : |inner ℝ x y|≤1) :
    |inner ℝ (compensatorFeature M d c x) (compensatorFeature M d c y)-
      inner ℝ (limitingCompensatorFeature M d c x) (limitingCompensatorFeature M d c y)|≤
      (M : ℝ)^2/(2*((N : ℝ)+M))*∑i,c i*(d i : ℝ)*((d i-1 : ℕ) : ℝ) := by
  rw [compensatorFeature_inner hN hM d c hc,limitingCompensatorFeature_inner M hN d c hc]
  have hi (i : σ) : |c i*degreeCompensator N M (d i)*(inner ℝ x y)^(d i)-
      c i*((d i-1 : ℕ) : ℝ)*(inner ℝ x y)^(d i)|≤
      c i*((M : ℝ)/((N : ℝ)+M)*(d i : ℝ)*((d i-1 : ℕ) : ℝ)/2) := by
    have he := degreeCompensator_error N (d i) hM (hd i)
    have hp : |(inner ℝ x y)^(d i)|≤1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hxy
    calc
      _ = c i*(((d i-1 : ℕ) : ℝ)-degreeCompensator N M (d i))*|(inner ℝ x y)^(d i)| := by
        rw [← mul_sub_right_distrib,← mul_sub_left_distrib,abs_mul,abs_mul,
          abs_of_nonneg (hc i),abs_of_nonpos (sub_nonpos.mpr (by linarith : degreeCompensator N M (d i)≤((d i-1 : ℕ) : ℝ)))]
        ring
      _ ≤ c i*(((d i-1 : ℕ) : ℝ)-degreeCompensator N M (d i))*1 :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (hc i) he.1)
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left he.2 (hc i)
  calc
    _ = (M : ℝ)*|∑i,(c i*degreeCompensator N M (d i)*(inner ℝ x y)^(d i)-
        c i*((d i-1 : ℕ) : ℝ)*(inner ℝ x y)^(d i))| := by
      rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (Nat.cast_nonneg M)]
    _ ≤ (M : ℝ)*∑i,|c i*degreeCompensator N M (d i)*(inner ℝ x y)^(d i)-
        c i*((d i-1 : ℕ) : ℝ)*(inner ℝ x y)^(d i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
    _ ≤ (M : ℝ)*∑i,c i*((M : ℝ)/((N : ℝ)+M)*(d i : ℝ)*((d i-1 : ℕ) : ℝ)/2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (Nat.cast_nonneg M)
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have htotal : (N : ℝ)+(M : ℝ)≠0 := by positivity
      field_simp

end Mixture

theorem actualGaussian_linear_covariance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a b : E) :
    cov[fun g : E => inner ℝ a g,fun g : E => inner ℝ b g; stdGaussian E]=inner ℝ a b := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  rfl

/-- The bulk coordinates inside the enlarged unit-spin representation. The norm shrinks
by sqrt(N/(N+M)); the cavity coordinates are literally zero.
-/
def bulkEmbedding {N : ℕ} (M : ℕ) (x : Model.Vector N) : Model.Vector (N+M) :=
  WithLp.toLp 2 (Fin.addCases (Real.sqrt (bulkRatio N M) • x) (0 : Model.Vector M))

private theorem bulkEmbedding_left {N M : ℕ} (x : Model.Vector N) (i : Fin N) :
    bulkEmbedding M x (Fin.castAdd M i)=Real.sqrt (bulkRatio N M)*x i := by
  simp [bulkEmbedding,PiLp.smul_apply,smul_eq_mul]

private theorem bulkEmbedding_right {N M : ℕ} (x : Model.Vector N) (i : Fin M) :
    bulkEmbedding M x (Fin.natAdd N i)=0 := by simp [bulkEmbedding]

theorem bulkEmbedding_inner {N M : ℕ} (x y : Model.Vector N) :
    inner ℝ (bulkEmbedding M x) (bulkEmbedding M y)=bulkRatio N M*inner ℝ x y := by
  rw [PiLp.inner_apply,Fin.sum_univ_add]
  simp only [bulkEmbedding_left,bulkEmbedding_right,RCLike.inner_apply,conj_trivial,
    mul_zero,Finset.sum_const_zero,add_zero]
  rw [PiLp.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs := Real.sq_sqrt (bulkRatio_nonneg N M)
  simp only [RCLike.inner_apply,conj_trivial]
  have hmul := congrArg (fun a : ℝ => a*(x i*y i)) hs
  nlinarith only [hmul]

theorem actualGaussian_thermal_slice_covariance {N : ℕ} (k : ℕ) {m : ℝ}
    (hm : m∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    cov[fun g => beta*inner ℝ (GroundState.sliceFeature k m x) g,
      fun g => beta*inner ℝ (GroundState.sliceFeature k m y) g;
      stdGaussian (GroundState.Disorder N k)]=
      beta^2*(N : ℝ)*Scalar.xiSlice k m (inner ℝ x y) := by
  have hfun (z : Model.Vector N) : (fun g => beta*inner ℝ (GroundState.sliceFeature k m z) g)=
      (fun g => inner ℝ (beta • GroundState.sliceFeature k m z) g) := by
    funext g; rw [real_inner_smul_left]
  rw [hfun x,hfun y,actualGaussian_linear_covariance,real_inner_smul_left,real_inner_smul_right,
    GroundUpperProofs.sliceFeature_inner hm]
  ring

/-- The finite bulk feature has the covariance of the literal enlarged
physical slice restricted to zero cavity coordinates. Degree one is retained. -/
theorem enlarged_slice_bulk_covariance {N M : ℕ} (hM : 0<M)
    (k : ℕ) {m : ℝ} (hm : m∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    cov[fun g => beta*inner ℝ (GroundState.sliceFeature k m (bulkEmbedding M x)) g,
      fun g => beta*inner ℝ (GroundState.sliceFeature k m (bulkEmbedding M y)) g;
      stdGaussian (GroundState.Disorder (N+M) k)]=
    cov[fun g => inner ℝ (bulkFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) x) g,
      fun g => inner ℝ (bulkFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) y) g;
      stdGaussian (GroundState.Disorder N k)] := by
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k m p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hm p)
  rw [actualGaussian_thermal_slice_covariance k hm,bulkEmbedding_inner,
    actualGaussian_linear_covariance,bulkFeature_inner _ _ hc,VariationalProofs.xiSlice_eq_sum]
  have hratio : ((N+M : ℕ) : ℝ)*bulkRatio N M=(N : ℝ) := by
    simp only [Nat.cast_add]
    unfold bulkRatio
    have htotal : (N : ℝ)+(M : ℝ)≠0 := by positivity
    field_simp
  simp only [Finset.mul_sum,mul_pow,Nat.add_sub_cancel,pow_succ]
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = (((N+M : ℕ) : ℝ)*bulkRatio N M)*
        (beta^2*VariationalProofs.sliceCoefficient k m p*bulkRatio N M^p.val*(inner ℝ x y)^(p.val+1)) := by ring
    _ = _ := by rw [hratio]; ring

theorem slice_bulk_compensator_covariance {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) {m : ℝ} (hm : m∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    cov[fun g => inner ℝ (bulkFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) x) g,
      fun g => inner ℝ (bulkFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) y) g;
      stdGaussian (GroundState.Disorder N k)]+
    cov[fun g => inner ℝ (compensatorFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) x) g,
      fun g => inner ℝ (compensatorFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) y) g;
      stdGaussian (GroundState.Disorder N k)]=
    cov[fun g => beta*inner ℝ (GroundState.sliceFeature k m x) g,
      fun g => beta*inner ℝ (GroundState.sliceFeature k m y) g;
      stdGaussian (GroundState.Disorder N k)] := by
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k m p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hm p)
  rw [actualGaussian_linear_covariance,actualGaussian_linear_covariance,
    bulk_add_compensator_inner hN hM _ _ hc,FiniteTensorMixtureMaximum.feature_inner _ _ hc]
  have hfunx : (fun g => beta*inner ℝ (GroundState.sliceFeature k m x) g)=
      (fun g => inner ℝ (beta • GroundState.sliceFeature k m x) g) := by
    funext g; rw [real_inner_smul_left]
  have hfuny : (fun g => beta*inner ℝ (GroundState.sliceFeature k m y) g)=
      (fun g => inner ℝ (beta • GroundState.sliceFeature k m y) g) := by
    funext g; rw [real_inner_smul_left]
  rw [hfunx,hfuny,actualGaussian_linear_covariance,real_inner_smul_left,real_inner_smul_right,
    GroundUpperProofs.sliceFeature_inner hm,VariationalProofs.xiSlice_eq_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem slice_compensator_covariance_error {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) {m : ℝ} (hm : m∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (x y : Model.Vector N) (hxy : |inner ℝ x y|≤1) :
    |cov[fun g => inner ℝ (compensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) x) g,
        fun g => inner ℝ (compensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) y) g;
        stdGaussian (GroundState.Disorder N k)]-
      cov[fun g => inner ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) x) g,
        fun g => inner ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) y) g;
        stdGaussian (GroundState.Disorder N k)]|≤
      (M : ℝ)^2*beta^2*deriv (deriv (Scalar.xiSlice k m)) 1/(2*((N : ℝ)+M)) := by
  rw [actualGaussian_linear_covariance,actualGaussian_linear_covariance]
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k m p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hm p)
  have he := compensator_covariance_error hN hM (fun p : Fin k => p.val+1)
    (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) hc (fun _ => by omega) x y hxy
  have hderiv := congrFun (NonRSSphericalGroundTrialTransportProofs.source_xi2_eq_secondDeriv_xiSlice k m) 1
  simp only [SphericalParisiPositivePolynomialCalculus.xi2,one_pow,mul_one] at hderiv
  have hsum : (∑p : Fin k,beta^2*VariationalProofs.sliceCoefficient k m p*
      ((p.val+1 : ℕ) : ℝ)*((p.val+1-1 : ℕ) : ℝ))=
      beta^2*deriv (deriv (Scalar.xiSlice k m)) 1 := by
    rw [← hderiv,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsum] at he
  convert he using 1 <;> ring

theorem limiting_compensator_covariance_eq_theta {N : ℕ} (M : ℕ) (hN : 0<N)
    (k : ℕ) {m : ℝ} (hm : m∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    cov[fun g => inner ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) x) g,
        fun g => inner ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k m p) y) g;
        stdGaussian (GroundState.Disorder N k)]=
      (M : ℝ)*beta^2*(inner ℝ x y*deriv (Scalar.xiSlice k m) (inner ℝ x y)-
        Scalar.xiSlice k m (inner ℝ x y)) := by
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k m p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hm p)
  rw [actualGaussian_linear_covariance,limitingCompensatorFeature_inner M hN _ _ hc]
  have hderiv := congrFun (NonRSSphericalGroundTrialTransportProofs.source_xi1_eq_deriv_xiSlice k m) (inner ℝ x y)
  rw [← hderiv,VariationalProofs.xiSlice_eq_sum]
  unfold SphericalParisiLabeledCovariance.xi1
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Finset.mul_sum,mul_sub,
    ← Finset.sum_sub_distrib,pow_succ]
  apply Finset.sum_congr rfl
  intro p _
  ring


end
end TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility
