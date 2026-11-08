-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureFieldNormalizationProofs
public import TensorPCA.GroundUpperProofs
public import TensorPCA.RetainedCountProofs.SphericalLatitude

/-! Exact finite expectation transport of the original pure field restricted
to an affine latitude to the slice Gaussian process. The literal
latitudeField wrapper is definitionally field composed with latitudeMap.
No physical ground-state, RS or concentration conclusion is an input. -/
@[expose] public section
namespace TensorPCA.PureLatitudeGroundTransportProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set
open RetainedCountProofs SphericalModel SphericalGaussianJet
open PureFieldNormalizationProofs
open scoped Topology RealInnerProductSpace Pointwise
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The actual affine-latitude sphere point in unit-sphere coordinates. -/
def latitudeUnitPoint (n : ℕ) (w : Model.Vector (n+2))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (m : ℝ) (x : Model.Vector (n+1)) :
    Model.Vector (n+2) :=
  (Real.sqrt (n+2 : ℕ))⁻¹ • latitudeMap w e m (Real.sqrt (n+1 : ℕ) • x)

lemma latitudeUnitPoint_continuous (n : ℕ) (w : Model.Vector (n+2))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (m : ℝ) :
    Continuous (latitudeUnitPoint n w e m) := by
  unfold latitudeUnitPoint
  exact ((latitudeMap_continuous w e m).comp
    (continuous_const_smul (Real.sqrt (n+1 : ℕ)))).const_smul ((Real.sqrt (n+2 : ℕ))⁻¹)

lemma latitudeUnitPoint_norm {n : ℕ} (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) {x : Model.Vector (n+1)} (hx : x ∈ Model.unitSphere (n+1)) :
    ‖latitudeUnitPoint n w e m x‖=1 := by
  have hs : 0 < Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hy : ‖Real.sqrt (n+1 : ℕ) • x‖^2=(n+1 : ℕ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      (show ‖x‖=1 from hx),mul_one,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n+1 : ℕ))]
  have hlat := latitudeMap_norm_sq (n := n+1) (by omega) w hw e he (abs_le.mpr hm) _ hy
  unfold latitudeUnitPoint
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),LandscapeDerivatives.sphere_norm _ hlat,
    inv_mul_cancel₀ hs.ne']

lemma inner_inv_sqrt_smul {N : ℕ} (x y : Model.Vector N) :
    inner ℝ ((Real.sqrt (N : ℝ))⁻¹ • x) ((Real.sqrt (N : ℝ))⁻¹ • y)=inner ℝ x y/(N : ℝ) := by
  rw [real_inner_smul_left,real_inner_smul_right]
  calc
    _ = ((Real.sqrt (N : ℝ))⁻¹)^2*inner ℝ x y := by ring
    _ = _ := by rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)];ring

lemma overlap_sqrt_smul {N : ℕ} (hN : 0 < N) (x y : Model.Vector N) :
    overlap (Real.sqrt (N : ℝ) • x) (Real.sqrt (N : ℝ) • y)=inner ℝ x y := by
  unfold overlap
  rw [real_inner_smul_left,real_inner_smul_right]
  calc
    _ = ((Real.sqrt (N : ℝ))^2/(N : ℝ))*inner ℝ x y := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N),div_self (Nat.cast_pos.mpr hN).ne',one_mul]

lemma latitudeUnitPoint_inner {n : ℕ} (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (x y : Model.Vector (n+1)) :
    inner ℝ (latitudeUnitPoint n w e m x) (latitudeUnitPoint n w e m y)=
      m^2+(1-m^2)*inner ℝ x y := by
  unfold latitudeUnitPoint
  rw [inner_inv_sqrt_smul]
  change overlap (latitudeMap w e m (Real.sqrt (n+1 : ℕ) • x))
    (latitudeMap w e m (Real.sqrt (n+1 : ℕ) • y)) = _
  rw [overlap_latitude_pair (n := n+1) (by omega) w hw e he (abs_le.mpr hm),
    overlap_sqrt_smul (by omega)]

lemma latitude_feature_increment_eq {n : ℕ} (k : ℕ)
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) {x y : Model.Vector (n+1)}
    (hx : x ∈ Model.unitSphere (n+1)) (hy : y ∈ Model.unitSphere (n+1)) :
    ‖Model.feature k (latitudeUnitPoint n w e m x)-Model.feature k (latitudeUnitPoint n w e m y)‖ =
      ‖(Real.sqrt (n+1 : ℕ))⁻¹ • GroundState.sliceFeature k m x-
        (Real.sqrt (n+1 : ℕ))⁻¹ • GroundState.sliceFeature k m y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real,Geometry.feature_unit_norm _ (latitudeUnitPoint_norm w hw e he hm hx),
    Geometry.feature_unit_norm _ (latitudeUnitPoint_norm w hw e he hm hy),Geometry.feature_inner,
    latitudeUnitPoint_inner w hw e he hm]
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n+1 : ℕ)),norm_sub_sq_real,
    GroundUpperProofs.sliceFeature_norm_sq hm hx,GroundUpperProofs.sliceFeature_norm_sq hm hy,
    GroundUpperProofs.sliceFeature_inner hm]
  unfold Scalar.xiSlice
  simp only [one_pow]
  field_simp [(by positivity : ((n+1 : ℕ) : ℝ) ≠ 0)]
  ring

/-- Increment equality identifies the true expected Gaussian suprema; the
omitted common random constant has zero mean, handled by comparison itself. -/
theorem expected_latitude_feature_supremum_eq (n k : ℕ)
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    (∫ g : Model.Tensor (n+2) k, (⨆ x : Model.unitSphere (n+1),
      inner ℝ (Model.feature k (latitudeUnitPoint n w e m x)) g) ∂stdGaussian (Model.Tensor (n+2) k)) =
      (Real.sqrt (n+1 : ℕ))⁻¹ *
        (∫ g : GroundState.Disorder (n+1) k, (⨆ x : Model.unitSphere (n+1),
          inner ℝ (GroundState.sliceFeature k m x) g) ∂stdGaussian (GroundState.Disorder (n+1) k)) := by
  let : Nonempty (Model.unitSphere (n+1)) := (Geometry.unitSphere_nonempty (by omega)).to_subtype
  let : CompactSpace (Model.unitSphere (n+1)) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact (n+1))
  let a : Model.unitSphere (n+1) → Model.Tensor (n+2) k :=
    fun x => Model.feature k (latitudeUnitPoint n w e m x)
  let b : Model.unitSphere (n+1) → GroundState.Disorder (n+1) k :=
    fun x => (Real.sqrt (n+1 : ℕ))⁻¹ • GroundState.sliceFeature k m x
  have ha : Continuous a := (Model.continuous_feature (n+2) k).comp
    ((latitudeUnitPoint_continuous n w e m).comp continuous_subtype_val)
  have hb : Continuous b :=
    ((GroundUpperProofs.continuous_sliceFeature (n+1) k m).comp continuous_subtype_val).const_smul
      ((Real.sqrt (n+1 : ℕ))⁻¹)
  have hinc (x y : Model.unitSphere (n+1)) : ‖a x-a y‖=‖b x-b y‖ :=
    latitude_feature_increment_eq k w hw e he hm x.property y.property
  have H := le_antisymm
    (GaussianMaximumComparisonProofs.expected_supremum_comparison a b ha hb (fun x y => (hinc x y).le))
    (GaussianMaximumComparisonProofs.expected_supremum_comparison b a hb ha (fun x y => (hinc x y).ge))
  change (∫ g : Model.Tensor (n+2) k, (⨆ x, inner ℝ (a x) g) ∂stdGaussian (Model.Tensor (n+2) k)) = _
  rw [H]
  have hscaled (g : GroundState.Disorder (n+1) k) :
      (⨆ x : Model.unitSphere (n+1), inner ℝ (b x) g) =
        (Real.sqrt (n+1 : ℕ))⁻¹*(⨆ x : Model.unitSphere (n+1), inner ℝ (GroundState.sliceFeature k m x) g) := by
    dsimp only [b]
    simp_rw [real_inner_smul_left]
    exact (Real.mul_iSup_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _).symm
  simp_rw [hscaled]
  exact integral_const_mul _ _

lemma field_latitudeUnitPoint {n : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (J : Disorder (n+2) (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree)
    (w : Model.Vector (n+2)) (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2))
    (m : ℝ) (x : Model.Vector (n+1)) :
    field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
      J (latitudeMap w e m (Real.sqrt (n+1 : ℕ) • x)) =
        Real.sqrt (n+2 : ℕ)*Model.score (WithLp.toLp 2 (J (pureDegree k hk))) (latitudeUnitPoint n w e m x) := by
  have hs : 0 < Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have heq : Real.sqrt (n+2 : ℕ) • latitudeUnitPoint n w e m x =
      latitudeMap w e m (Real.sqrt (n+1 : ℕ) • x) := by
    unfold latitudeUnitPoint
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  have H := field_pure_sqrt_smul (show 0<n+2 by omega) k hk J (latitudeUnitPoint n w e m x)
  rw [heq] at H
  exact H


/-- Exact finite expectation transport from the original pure latitude field
in ambient n+2 to the reviewed slice process in dimension n+1. -/
theorem expected_latitude_ground_transport (n k : ℕ) (hk : 2 ≤ k)
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    let μ := FiniteMixture.pure k hk 1 zero_lt_one
    let c := centerCoefficients (mixtureCoefficients μ) 1
    (∫ J : Disorder (n+2) μ.maxDegree,
      sSup ((fun y : Model.Vector (n+1) => field c J (latitudeMap w e m y)) ''
        {y : Model.Vector (n+1) | ‖y‖^2=(n+1 : ℕ)})/(n+2 : ℕ) ∂disorderLaw (n+2) μ.maxDegree) =
      Real.sqrt (n+1 : ℕ)/Real.sqrt (n+2 : ℕ)*GroundState.expectedSliceGround (n+1) k m := by
  let : Nonempty (Model.unitSphere (n+1)) := (Geometry.unitSphere_nonempty (by omega)).to_subtype
  let : CompactSpace (Model.unitSphere (n+1)) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact (n+1))
  let μ := FiniteMixture.pure k hk 1 zero_lt_one
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let a : Model.unitSphere (n+1) → Model.Tensor (n+2) k :=
    fun x => Model.feature k (latitudeUnitPoint n w e m x)
  let F : Model.Tensor (n+2) k → ℝ := fun g => ⨆ x : Model.unitSphere (n+1), inner ℝ (a x) g
  have ha : Continuous a := (Model.continuous_feature (n+2) k).comp
    ((latitudeUnitPoint_continuous n w e m).comp continuous_subtype_val)
  have hFI : AEStronglyMeasurable F (Model.noiseLaw (n+2) k) :=
    (GaussianMaximumComparisonProofs.supremum_integrable a ha).aestronglyMeasurable
  have hlaw := (pureBlock_hasLaw (n+2) k hk).integral_comp hFI
  have hsource_sup (J : Disorder (n+2) μ.maxDegree) :
      sSup ((fun y : Model.Vector (n+1) => field c J (latitudeMap w e m y)) ''
        {y : Model.Vector (n+1) | ‖y‖^2=(n+1 : ℕ)}) =
          Real.sqrt (n+2 : ℕ)*F (WithLp.toLp 2 (J (pureDegree k hk))) := by
    have himage : (fun y : Model.Vector (n+1) => field c J (latitudeMap w e m y)) ''
        {y : Model.Vector (n+1) | ‖y‖^2=(n+1 : ℕ)} =
      Real.sqrt (n+2 : ℕ) • ((fun x : Model.Vector (n+1) =>
        Model.score (WithLp.toLp 2 (J (pureDegree k hk))) (latitudeUnitPoint n w e m x)) ''
          Model.unitSphere (n+1)) := by
      rw [← sqrt_smul_unitSphere_image (show 0<n+1 by omega),Set.image_image,
        ← Set.image_smul,Set.image_image]
      congr 1
      funext x
      exact field_latitudeUnitPoint k hk J w e m x
    rw [himage,Real.sSup_smul_of_nonneg (Real.sqrt_nonneg _),smul_eq_mul]
    congr 1
    dsimp only [F,a]
    rw [iSup,Set.image_eq_range]
    rfl
  have hslice (g : GroundState.Disorder (n+1) k) :
      sSup ((fun x => inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere (n+1)) =
        ⨆ x : Model.unitSphere (n+1), inner ℝ (GroundState.sliceFeature k m x) g := by
    rw [iSup,Set.image_eq_range]
  have hsM : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hsN : 0 < Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hcoeff : Real.sqrt (n+2 : ℕ)*(Real.sqrt (n+1 : ℕ))⁻¹/(n+2 : ℕ) =
      (Real.sqrt (n+1 : ℕ)/Real.sqrt (n+2 : ℕ))/(n+1 : ℕ) := by
    field_simp [hsM.ne',hsN.ne',(by positivity : ((n+1 : ℕ) : ℝ) ≠ 0),
      (by positivity : ((n+2 : ℕ) : ℝ) ≠ 0)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n+1 : ℕ) by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)]
  dsimp only
  calc
    _ = ∫ J : Disorder (n+2) μ.maxDegree,
        (Real.sqrt (n+2 : ℕ)*F (WithLp.toLp 2 (J (pureDegree k hk))))/(n+2 : ℕ)
          ∂disorderLaw (n+2) μ.maxDegree := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun J =>
        congrArg (fun r : ℝ => r/(n+2 : ℕ)) (hsource_sup J))
    _ = Real.sqrt (n+2 : ℕ)*(∫ J : Disorder (n+2) μ.maxDegree,
        F (WithLp.toLp 2 (J (pureDegree k hk))) ∂disorderLaw (n+2) μ.maxDegree)/(n+2 : ℕ) := by
      rw [integral_div,integral_const_mul]
    _ = Real.sqrt (n+2 : ℕ)*(∫ g, F g ∂Model.noiseLaw (n+2) k)/(n+2 : ℕ) :=
      congrArg (fun r : ℝ => Real.sqrt (n+2 : ℕ)*r/(n+2 : ℕ)) hlaw
    _ = Real.sqrt (n+2 : ℕ)*((Real.sqrt (n+1 : ℕ))⁻¹ *
        (∫ g : GroundState.Disorder (n+1) k, (⨆ x : Model.unitSphere (n+1),
          inner ℝ (GroundState.sliceFeature k m x) g) ∂stdGaussian (GroundState.Disorder (n+1) k)))/(n+2 : ℕ) :=
      congrArg (fun r : ℝ => Real.sqrt (n+2 : ℕ)*r/(n+2 : ℕ))
        (expected_latitude_feature_supremum_eq n k w hw e he hm)
    _ = _ := by
      unfold GroundState.expectedSliceGround
      simp_rw [hslice]
      rw [integral_div]
      rw [show Real.sqrt (n+2 : ℕ)*((Real.sqrt (n+1 : ℕ))⁻¹ *
          (∫ g : GroundState.Disorder (n+1) k, (⨆ x : Model.unitSphere (n+1),
            inner ℝ (GroundState.sliceFeature k m x) g) ∂stdGaussian (GroundState.Disorder (n+1) k)))/(n+2 : ℕ) =
          (Real.sqrt (n+2 : ℕ)*(Real.sqrt (n+1 : ℕ))⁻¹/(n+2 : ℕ))*
            (∫ g : GroundState.Disorder (n+1) k, (⨆ x : Model.unitSphere (n+1),
              inner ℝ (GroundState.sliceFeature k m x) g) ∂stdGaussian (GroundState.Disorder (n+1) k)) by ring,
        hcoeff]
      ring


end
end TensorPCA.PureLatitudeGroundTransportProofs
