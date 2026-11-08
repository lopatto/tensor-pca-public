-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.Geometry
public import Mathlib.Basic.Real.Pointwise
public import TensorPCA.RetainedCountProofs.SphericalGaussianJet
public import TensorPCA.RetainedCountProofs.OrthogonalGaussianDisclosure

/-! Exact finite normalization from the ordered-tensor source pure field
to the TensorPCA Gaussian-noise model. Other degree blocks remain in
the original disorder product and have exactly zero coefficients. -/
@[expose] public section
namespace TensorPCA.PureFieldNormalizationProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set
open RetainedCountProofs SphericalModel SphericalGaussianJet
open scoped RealInnerProductSpace BigOperators Pointwise
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma pure_maxDegree (k : ℕ) (hk : 2 ≤ k) :
    (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree=k := by
  simp [FiniteMixture.maxDegree,FiniteMixture.pure,Finsupp.support_single k one_ne_zero]

/-- The supported degree has natural value definitionally k. -/
def pureDegree (k : ℕ) (hk : 2 ≤ k) :
    Degree (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree :=
  ⟨⟨k,by rw [pure_maxDegree];omega⟩,hk⟩

lemma field_pure_eq {N : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (J : Disorder N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) (x : Model.Vector N) :
    field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1) J x =
      RetainedCountProofs.FiniteModel.Hamiltonian N k (J (pureDegree k hk)) x := by
  unfold field
  rw [Finset.sum_eq_single (pureDegree k hk)]
  · simp [centerCoefficients,mixtureCoefficients,FiniteMixture.pure,blockField,pureDegree]
  · intro q hq hne
    have hqk : q.val.val ≠ k := by
      intro h
      apply hne
      apply Subtype.ext
      exact Fin.ext h
    simp [centerCoefficients,mixtureCoefficients,FiniteMixture.pure,hqk]
  · simp

lemma pureBlock_hasLaw (N k : ℕ) (hk : 2 ≤ k) :
    HasLaw (fun J : Disorder N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree =>
      WithLp.toLp 2 (J (pureDegree k hk))) (Model.noiseLaw N k)
        (disorderLaw N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) := by
  simpa only [Model.noiseLaw] using
    (OrthogonalGaussianDisclosure.ordered_tensor_hasLaw N k).fun_comp
      (degree_block_hasLaw (N := N) (pureDegree k hk))

lemma Hamiltonian_eq_score {N k : ℕ} (J : RetainedCountProofs.FiniteModel.Disorder N k)
    (x : Model.Vector N) :
    RetainedCountProofs.FiniteModel.Hamiltonian N k J x =
      RetainedCountProofs.FiniteModel.normalization N k * Model.score (WithLp.toLp 2 J) x := by
  simp only [RetainedCountProofs.FiniteModel.Hamiltonian,Model.score,Model.feature,
    RetainedCountProofs.FiniteModel.tensorMonomial,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    WithLp.ofLp_toLp]

lemma normalization_sqrt_power_succ {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) :
    RetainedCountProofs.FiniteModel.normalization N k * Real.sqrt (N : ℝ)^k = Real.sqrt N := by
  have H := LandscapeDerivatives.normalization_sqrt_power (p := k) hN
  calc
    _ = (RetainedCountProofs.FiniteModel.normalization N k * Real.sqrt (N : ℝ)^(k-1))*Real.sqrt N := by
      rw [mul_assoc,← pow_succ,Nat.sub_add_cancel hk]
    _ = _ := by rw [H,one_mul]

/-- Exact pathwise source-to-model field normalization on every ambient point. -/
theorem field_pure_sqrt_smul {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : 2 ≤ k)
    (J : Disorder N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) (x : Model.Vector N) :
    field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
      J (Real.sqrt (N : ℝ) • x) =
        Real.sqrt N * Model.score (WithLp.toLp 2 (J (pureDegree k hk))) x := by
  rw [field_pure_eq,pure_spatial_smul,Hamiltonian_eq_score]
  have H := normalization_sqrt_power_succ hN (show 1 ≤ k by omega)
  calc
    _ = (RetainedCountProofs.FiniteModel.normalization N k * Real.sqrt (N : ℝ)^k) *
        Model.score (WithLp.toLp 2 (J (pureDegree k hk))) x := by ring
    _ = _ := by rw [H]

lemma sqrt_smul_unitSphere_image {N : ℕ} (hN : 0 < N) :
    (fun x : Model.Vector N => Real.sqrt (N : ℝ) • x) '' Model.unitSphere N =
      {z : Model.Vector N | ‖z‖^2=(N : ℝ)} := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change ‖Real.sqrt (N : ℝ) • x‖^2=(N : ℝ)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs,(show ‖x‖=1 from hx),mul_one,
      Real.sq_sqrt (Nat.cast_nonneg N)]
  · intro hz
    refine ⟨(Real.sqrt (N : ℝ))⁻¹ • z,?_,?_⟩
    · change ‖(Real.sqrt (N : ℝ))⁻¹ • z‖=1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),LandscapeDerivatives.sphere_norm z hz]
      exact inv_mul_cancel₀ hs.ne'
    · change Real.sqrt (N : ℝ) • ((Real.sqrt (N : ℝ))⁻¹ • z)=z
      rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]

/-- The source spherical maximum/N equals the normalized maximum of the active ordered tensor block. -/
theorem pure_source_maximum_eq {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : 2 ≤ k)
    (J : Disorder N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) :
    sSup (field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
      J '' {z : Model.Vector N | ‖z‖^2=(N : ℝ)})/(N : ℝ) =
        Model.normalizedMaximum (WithLp.toLp 2 (J (pureDegree k hk))) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have himage : field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
      J '' {z : Model.Vector N | ‖z‖^2=(N : ℝ)} =
        Real.sqrt (N : ℝ) • (Model.score (WithLp.toLp 2 (J (pureDegree k hk))) '' Model.unitSphere N) := by
    rw [← sqrt_smul_unitSphere_image hN,Set.image_image,← Set.image_smul,Set.image_image]
    congr 1
    funext x
    exact field_pure_sqrt_smul hN k hk J x
  rw [himage,Real.sSup_smul_of_nonneg hs.le,smul_eq_mul,Model.normalizedMaximum]
  apply (div_eq_div_iff (Nat.cast_pos.mpr hN).ne' hs.ne').mpr
  have H := congrArg (fun t : ℝ => t * sSup (Model.score
    (WithLp.toLp 2 (J (pureDegree k hk))) '' Model.unitSphere N))
    (Real.sq_sqrt (Nat.cast_nonneg N))
  nlinarith

/-- The whole source disorder induces exactly the actual normalized maximum
law; unused Gaussian degree blocks have not been removed by a hypothesis. -/
theorem pure_source_maximum_hasLaw {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : 2 ≤ k) :
    HasLaw (fun J : Disorder N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree =>
      sSup (field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
        J '' {z : Model.Vector N | ‖z‖^2=(N : ℝ)})/(N : ℝ))
      ((Model.noiseLaw N k).map Model.normalizedMaximum)
      (disorderLaw N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) := by
  have hmodel : HasLaw (Model.normalizedMaximum (N := N) (k := k))
      ((Model.noiseLaw N k).map Model.normalizedMaximum) (Model.noiseLaw N k) :=
    hasLaw_map (Geometry.normalizedMaximum_lipschitz hN).continuous.measurable.aemeasurable
  exact (hmodel.fun_comp (pureBlock_hasLaw N k hk)).congr
    (.of_forall (fun J => pure_source_maximum_eq hN k hk J))

theorem pure_source_maximum_integral {N : ℕ} (hN : 0 < N) (k : ℕ) (hk : 2 ≤ k) :
    (∫ J : Disorder N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree,
      sSup (field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
        J '' {z : Model.Vector N | ‖z‖^2=(N : ℝ)})/(N : ℝ)
        ∂disorderLaw N (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) =
      ∫ W, Model.normalizedMaximum W ∂Model.noiseLaw N k := by
  have H := (pureBlock_hasLaw N k hk).integral_comp
    (Geometry.normalizedMaximum_lipschitz hN).continuous.aestronglyMeasurable
  apply (integral_congr_ae (.of_forall (fun J => pure_source_maximum_eq hN k hk J))).trans
  exact H


end
end TensorPCA.PureFieldNormalizationProofs
