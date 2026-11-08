-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureLatitudeGroundTransportProofs

/-! Pure-latitude low-probability bounds imply a lower bound for the slice mean. The input is a literal original-disorder probability event,
not a physical mean or ground-state-limit hypothesis. -/
@[expose] public section
namespace TensorPCA.PureLatitudeLowerMeanProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open RetainedCountProofs SphericalModel SphericalGaussianJet
open PureFieldNormalizationProofs PureLatitudeGroundTransportProofs
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The actual normalized Gaussian maximum on an affine latitude. -/
def gaussianLatitudeMaximum (n k : ℕ) (w : Model.Vector (n+2))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (m : ℝ)
    (W : Model.Tensor (n+2) k) : ℝ :=
  (Real.sqrt (n+2 : ℕ))⁻¹*(⨆ x : Model.unitSphere (n+1),
    inner ℝ (Model.feature k (latitudeUnitPoint n w e m x)) W)

lemma gaussianLatitudeMaximum_lipschitz {n k : ℕ}
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    LipschitzWith ((Real.sqrt (n+2 : ℕ))⁻¹).toNNReal (gaussianLatitudeMaximum n k w e m) := by
  let : Nonempty (Model.unitSphere (n+1)) := (Geometry.unitSphere_nonempty (by omega)).to_subtype
  let a : Model.unitSphere (n+1) → Model.Tensor (n+2) k :=
    fun x => Model.feature k (latitudeUnitPoint n w e m x)
  have hb (x : Model.unitSphere (n+1)) : ‖innerSL ℝ (a x)‖ ≤ 1 := by
    rw [innerSL_apply_norm]
    exact (Geometry.feature_unit_norm _ (latitudeUnitPoint_norm w hw e he hm x.property)).le
  have hF := GaussianCompactMaximum.field_supremum_lipschitz (fun x => innerSL ℝ (a x)) hb
  have hs : 0 < Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  apply LipschitzWith.of_dist_le_mul
  intro W V
  have H := hF.dist_le_mul W V
  change |gaussianLatitudeMaximum n k w e m W-gaussianLatitudeMaximum n k w e m V| ≤ _
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hs.le)]
  unfold gaussianLatitudeMaximum
  rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hs)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
  simpa only [Real.dist_eq,Real.toNNReal_one,NNReal.coe_one,one_mul,innerSL_apply_apply,a] using H

lemma gaussianLatitudeMaximum_tail {n k : ℕ}
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (t : ℝ) (ht : 0<t) :
    Model.noiseLaw (n+2) k {W | |gaussianLatitudeMaximum n k w e m W-
      ∫ V,gaussianLatitudeMaximum n k w e m V ∂Model.noiseLaw (n+2) k| > t} ≤
        ENNReal.ofReal (2*Real.exp (-(n+2 : ℕ)*t^2/2)) := by
  have hs : 0<Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have H := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (gaussianLatitudeMaximum n k w e m) ((Real.sqrt (n+2 : ℕ))⁻¹) t
    (inv_pos.mpr hs) ht (gaussianLatitudeMaximum_lipschitz w hw e he hm)
  have hex : -t^2/(2*((Real.sqrt (n+2 : ℕ))⁻¹)^2)=-(n+2 : ℕ)*t^2/2 := by
    field_simp [hs.ne']
    rw [Real.sq_sqrt (by positivity : (0 : ℝ)≤(n+2 : ℕ))]
  simpa only [Model.noiseLaw,hex] using H

lemma gaussianLatitudeMaximum_mean {n k : ℕ}
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    (∫ W,gaussianLatitudeMaximum n k w e m W ∂Model.noiseLaw (n+2) k)=
      Real.sqrt (n+1 : ℕ)/Real.sqrt (n+2 : ℕ)*GroundState.expectedSliceGround (n+1) k m := by
  unfold gaussianLatitudeMaximum Model.noiseLaw
  rw [integral_const_mul,expected_latitude_feature_supremum_eq n k w hw e he hm]
  have hsup (g : GroundState.Disorder (n+1) k) :
      sSup ((fun x => inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere (n+1))=
        ⨆ x : Model.unitSphere (n+1),inner ℝ (GroundState.sliceFeature k m x) g := by
    rw [iSup,Set.image_eq_range]
  unfold GroundState.expectedSliceGround
  simp_rw [hsup]
  rw [integral_div]
  have hsM : 0<Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hsN : 0<Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  field_simp [hsM.ne',hsN.ne',(by positivity : ((n+1 : ℕ) : ℝ)≠0)]
  rw [Real.sq_sqrt (show (0 : ℝ)≤(n+1 : ℕ) by positivity)]
  ring

lemma source_latitude_low_iff {n : ℕ} (k : ℕ) (hk : 2≤k)
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (J : Disorder (n+2) (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree) (z : ℝ) :
    (∀ y : Model.Vector (n+1), ‖y‖^2=(n+1 : ℕ) →
      field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
        J (latitudeMap w e m y) ≤ (n+2 : ℕ)*z) ↔
      gaussianLatitudeMaximum n k w e m (WithLp.toLp 2 (J (pureDegree k hk))) ≤ z := by
  let : Nonempty (Model.unitSphere (n+1)) := (Geometry.unitSphere_nonempty (by omega)).to_subtype
  let a : Model.unitSphere (n+1) → Model.Tensor (n+2) k :=
    fun x => Model.feature k (latitudeUnitPoint n w e m x)
  let W : Model.Tensor (n+2) k := WithLp.toLp 2 (J (pureDegree k hk))
  have hb (x : Model.unitSphere (n+1)) : ‖innerSL ℝ (a x)‖ ≤ 1 := by
    rw [innerSL_apply_norm]
    exact (Geometry.feature_unit_norm _ (latitudeUnitPoint_norm w hw e he hm x.property)).le
  have hbounded := GaussianCompactMaximum.field_bddAbove (fun x => innerSL ℝ (a x)) hb W
  have hs : 0<Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : (n+2 : ℕ)*z=Real.sqrt (n+2 : ℕ)*(Real.sqrt (n+2 : ℕ)*z) := by
    rw [← mul_assoc,← sq,Real.sq_sqrt (by positivity : (0 : ℝ)≤(n+2 : ℕ))]
  unfold gaussianLatitudeMaximum
  rw [inv_mul_le_iff₀ hs]
  constructor
  · intro H
    apply ciSup_le
    intro x
    have hy : ‖Real.sqrt (n+1 : ℕ) • (x : Model.Vector (n+1))‖^2=(n+1 : ℕ) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
        (show ‖(x : Model.Vector (n+1))‖=1 from x.property),mul_one,
        Real.sq_sqrt (by positivity : (0 : ℝ)≤(n+1 : ℕ))]
    have h := H _ hy
    rw [field_latitudeUnitPoint k hk J w e m,hscale] at h
    exact (mul_le_mul_iff_right₀ hs).mp h
  · intro H y hy
    change y ∈ {v : Model.Vector (n+1) | ‖v‖^2=(n+1 : ℕ)} at hy
    rw [← sqrt_smul_unitSphere_image (show 0<n+1 by omega)] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [field_latitudeUnitPoint k hk J w e m,hscale]
    apply mul_le_mul_of_nonneg_left _ hs.le
    exact (le_ciSup hbounded (⟨x,hx⟩ : Model.unitSphere (n+1))).trans H

lemma source_latitude_low_probability {n : ℕ} (k : ℕ) (hk : 2≤k)
    (w : Model.Vector (n+2)) (hw : ‖w‖^2=(n+2 : ℕ))
    (e : Model.Vector (n+1) →ₗᵢ[ℝ] Model.Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (z : ℝ) :
    let μ := FiniteMixture.pure k hk 1 zero_lt_one
    disorderLaw (n+2) μ.maxDegree
      {J | ∀ y : Model.Vector (n+1), ‖y‖^2=(n+1 : ℕ) →
        field (centerCoefficients (mixtureCoefficients μ) 1) J (latitudeMap w e m y) ≤ (n+2 : ℕ)*z} =
      Model.noiseLaw (n+2) k {W | gaussianLatitudeMaximum n k w e m W ≤ z} := by
  let μ := FiniteMixture.pure k hk 1 zero_lt_one
  have hmeas : MeasurableSet {W | gaussianLatitudeMaximum n k w e m W ≤ z} :=
    measurableSet_le (gaussianLatitudeMaximum_lipschitz w hw e he hm).continuous.measurable measurable_const
  have H := (pureBlock_hasLaw (n+2) k hk).measure_eq hmeas
  have heq : {J : Disorder (n+2) μ.maxDegree | ∀ y : Model.Vector (n+1),
      ‖y‖^2=(n+1 : ℕ) → field (centerCoefficients (mixtureCoefficients μ) 1) J
        (latitudeMap w e m y) ≤ (n+2 : ℕ)*z} =
      (fun J : Disorder (n+2) μ.maxDegree => WithLp.toLp 2 (J (pureDegree k hk))) ⁻¹'
        {W | gaussianLatitudeMaximum n k w e m W ≤ z} := by
    ext J
    exact source_latitude_low_iff k hk w hw e he hm J z
  change disorderLaw (n+2) μ.maxDegree _ = _
  rw [heq]
  exact H

lemma exponential_bound_tendsto (a c : ℝ) (hc : 0<c) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (a*Real.exp (-c*((n+3 : ℕ) : ℝ))))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hN : Tendsto (fun n : ℕ => ((n+3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hreal : Tendsto (fun n : ℕ => a*Real.exp (-c*((n+3 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    convert (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.atTop_mul_const hc)).const_mul a using 1
    · funext n
      congr 1
      congr 1
      ring
    · ring
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal

/-- A literal uniform exponential low-maximum event under the original pure
source law gives the actual one-sided slice-mean lower bound. The probability
input is an intermediate geometric claim, not a mean or ground-state limit. -/
theorem eventually_expectedSliceGround_lower_of_exponential_low
    (k : ℕ) (hk : 2≤k) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (g : ℝ) (hg : 0<g)
    (hbad : ∀ delta : ℝ, 0<delta → ∃ eta : ℝ, 0<eta ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w : Model.Vector (n+3), ‖w‖^2=(n+3 : ℕ) →
      ∀ e : Model.Vector (n+2) →ₗᵢ[ℝ] Model.Vector (n+3), (∀ x,inner ℝ (e x) w=0) →
      disorderLaw (n+3) (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree
        {J | ∀ y : Model.Vector (n+2), ‖y‖^2=(n+2 : ℕ) →
          field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
            J (latitudeMap w e m y) ≤ (n+3 : ℕ)*(g-delta)} ≤
          3*ENNReal.ofReal (Real.exp (-eta*(n+3 : ℕ))))
    (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ n : ℕ in atTop, g-eps ≤ GroundState.expectedSliceGround (n+1) k m := by
  let delta := min (eps/4) (g/4)
  have hd : 0<delta := lt_min (by positivity) (by positivity)
  have hdE : delta≤eps/4 := min_le_left _ _
  have hdG : delta≤g/4 := min_le_right _ _
  obtain ⟨eta,heta,hbadbound⟩ := hbad delta hd
  have hbadsmall := (exponential_bound_tendsto 3 eta heta).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞)<1/4))
  have htailsmall := (exponential_bound_tendsto 2 (delta^2/2) (by positivity)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞)<1/4))
  have hplus : ∀ᶠ n : ℕ in atTop, g-eps ≤ GroundState.expectedSliceGround (n+2) k m := by
    filter_upwards [hbadbound,hbadsmall,htailsmall] with n hn hbn htn
    obtain ⟨v,hv⟩ := Geometry.unitSphere_nonempty (show 0<n+3 by omega)
    let w := Real.sqrt (n+3 : ℕ) • v
    have hw : ‖w‖^2=(n+3 : ℕ) := by
      dsimp only [w]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
        (show ‖v‖=1 from hv),mul_one,Real.sq_sqrt (by positivity : (0 : ℝ)≤(n+3 : ℕ))]
    have hw0 : w≠0 := by
      intro H
      rw [H,norm_zero,zero_pow two_ne_zero] at hw
      have hpos : (0 : ℝ)<(n+3 : ℕ) := by positivity
      linarith
    let e : Model.Vector (n+2) →ₗᵢ[ℝ] Model.Vector (n+3) := latitudeTangentFrame w hw0
    have he : ∀ x,inner ℝ (e x) w=0 := latitudeTangentFrame_orthogonal w hw0
    let F := gaussianLatitudeMaximum (n+1) k w e m
    let mu := ∫ W,F W ∂Model.noiseLaw (n+3) k
    have hlow := hn w hw e he
    rw [source_latitude_low_probability k hk w hw e he hm (g-delta)] at hlow
    have hlowSmall : Model.noiseLaw (n+3) k {W | F W≤g-delta}<1/4 := by
      apply hlow.trans_lt
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤3),ENNReal.ofReal_ofNat] using hbn
    have htail := gaussianLatitudeMaximum_tail (k := k) w hw e he hm delta hd
    have htailSmall : Model.noiseLaw (n+3) k {W | |F W-mu| > delta}<1/4 := by
      apply htail.trans_lt
      convert htn using 1
      congr 1
      congr 1
      ring
    by_contra H
    have hEG : GroundState.expectedSliceGround (n+2) k m<g-eps := lt_of_not_ge H
    have hsN : 0<Real.sqrt (n+3 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsM : 0<Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hr0 : 0≤Real.sqrt (n+2 : ℕ)/Real.sqrt (n+3 : ℕ) := (div_pos hsM hsN).le
    have hr1 : Real.sqrt (n+2 : ℕ)/Real.sqrt (n+3 : ℕ)≤1 := by
      apply (div_le_one hsN).mpr
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show n+2≤n+3 by omega)
    have hmu : mu<g-2*delta := by
      dsimp only [mu,F]
      rw [gaussianLatitudeMaximum_mean w hw e he hm]
      by_cases hE0 : 0≤GroundState.expectedSliceGround (n+2) k m
      · have hmul := mul_le_mul_of_nonneg_right hr1 hE0
        simp only [one_mul] at hmul
        linarith
      · have hmul := mul_nonpos_of_nonneg_of_nonpos hr0 (le_of_not_ge hE0)
        linarith
    have hcover : (univ : Set (Model.Tensor (n+3) k)) ⊆
        {W | F W≤g-delta} ∪ {W | |F W-mu| > delta} := by
      intro W _
      by_cases hW : F W≤g-delta
      · exact Or.inl hW
      · apply Or.inr
        exact (show delta<F W-mu by linarith [lt_of_not_ge hW]).trans_le (le_abs_self _)
    have hsum : (1 : ℝ≥0∞)≤Model.noiseLaw (n+3) k {W | F W≤g-delta}+
        Model.noiseLaw (n+3) k {W | |F W-mu| > delta} := by
      calc
        1=Model.noiseLaw (n+3) k univ := by simp
        _≤Model.noiseLaw (n+3) k ({W | F W≤g-delta} ∪ {W | |F W-mu| > delta}) := measure_mono hcover
        _≤_ := measure_union_le _ _
    have hsmall := ENNReal.add_lt_add hlowSmall htailSmall
    have hquarter : (1/4 : ℝ≥0∞)+(1/4)<1 := by
      rw [ENNReal.div_add_div_same]
      apply (ENNReal.div_lt_iff (Or.inl (by norm_num : (4 : ℝ≥0∞)≠0))
        (Or.inl (by norm_num : (4 : ℝ≥0∞)≠⊤))).mpr
      norm_num
    exact not_lt_of_ge hsum (hsmall.trans hquarter)
  have hshift := (tendsto_sub_atTop_nat 1).eventually hplus
  filter_upwards [hshift,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have heq : n-1+2=n+1 := by omega
  simpa only [heq] using hn

end
end TensorPCA.PureLatitudeLowerMeanProofs
