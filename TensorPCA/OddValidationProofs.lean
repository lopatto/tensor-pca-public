-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PosteriorProofs
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian validation and sign orientation

The scalar orientation estimate below uses the first absolute noise moment.
For a unit Gaussian projection this moment is at most one, yielding the
manuscript's constant two without introducing a Gaussian tail approximation.
-/
@[expose] public section

namespace TensorPCA.OddValidationProofs

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace ProbabilityTheory

instance noiseLaw_isGaussian (N k : ℕ) : IsGaussian (Model.noiseLaw N k) := by
  unfold Model.noiseLaw
  infer_instance

/-- A wrong noisy sign costs at most twice the noise magnitude divided by
the validation signal strength. The convention at zero selects the plus sign. -/
theorem scalar_orientation_loss (s a z : ℝ) (hs : 0 < s) :
    |a| - (if 0 ≤ s * a + z then a else -a) ≤ 2 * |z| / s := by
  apply (le_div_iff₀ hs).2
  by_cases hsign : 0 ≤ s * a + z
  · rw [ite_eq_left hsign]
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha]
      nlinarith [abs_nonneg z]
    · rw [abs_of_neg (lt_of_not_ge ha)]
      nlinarith [le_abs_self z]
  · rw [ite_eq_right hsign]
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha]
      nlinarith [neg_le_abs z]
    · rw [abs_of_neg (lt_of_not_ge ha)]
      nlinarith [abs_nonneg z]

theorem projection_memLp_two {N k : ℕ} (v : Model.Tensor N k) :
    MemLp (fun w : Model.Tensor N k ↦ inner ℝ v w) 2 (Model.noiseLaw N k) :=
  (IsGaussian.memLp_two_id : MemLp id 2 (Model.noiseLaw N k)).const_inner v

theorem integral_projection (N k : ℕ) (v : Model.Tensor N k) :
    (∫ w, inner ℝ v w ∂Model.noiseLaw N k) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ v)

theorem integral_projection_sq {N k : ℕ} (v : Model.Tensor N k) :
    (∫ w, (inner ℝ v w) ^ 2 ∂Model.noiseLaw N k) = ‖v‖ ^ 2 := by
  have h := variance_eq_sub (projection_memLp_two v)
  have hmean := integral_projection N k v
  have hvar : variance (fun w : Model.Tensor N k ↦ inner ℝ v w)
      (Model.noiseLaw N k) = ‖v‖ ^ 2 := by
    simpa only [Model.noiseLaw, coe_innerSL_apply, innerSL_apply_norm] using
      variance_dual_stdGaussian (innerSL ℝ v)
  simpa only [Pi.pow_apply, hmean, zero_pow two_ne_zero, sub_zero, hvar] using h.symm

/-- A unit Gaussian projection has first absolute moment at most one. -/
theorem integral_abs_projection_le_one {N k : ℕ} (v : Model.Tensor N k) (hv : ‖v‖ = 1) :
    (∫ w, |inner ℝ v w| ∂Model.noiseLaw N k) ≤ 1 := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := Model.noiseLaw N k) (p := 2) (q := 2)
    (f := fun w ↦ |inner ℝ v w|) (g := fun _ ↦ (1 : ℝ))
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using (projection_memLp_two v).norm)
    (by simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : Model.Tensor N k ↦ (1 : ℝ)) 2 (Model.noiseLaw N k)))
  simpa [Real.rpow_two, sq_abs, integral_projection_sq, hv] using h

/-- Integrating the pointwise sign loss against a unit Gaussian projection
gives the exact constant two in the finite validation loss. -/
theorem integral_oriented_scalar_lower_bound {N k : ℕ} (s a : ℝ) (hs : 0 < s)
    (v : Model.Tensor N k) (hv : ‖v‖ = 1) :
    |a| - 2 / s ≤
      ∫ w, (if 0 ≤ s * a + inner ℝ v w then a else -a) ∂Model.noiseLaw N k := by
  have hf_meas : Measurable (fun w : Model.Tensor N k ↦
      if 0 ≤ s * a + inner ℝ v w then a else -a) :=
    Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const
  have hf : Integrable (fun w : Model.Tensor N k ↦
      if 0 ≤ s * a + inner ℝ v w then a else -a) (Model.noiseLaw N k) := by
    apply (integrable_const |a|).mono' hf_meas.aestronglyMeasurable
    filter_upwards with w
    split_ifs <;> simp
  have hz : Integrable (fun w : Model.Tensor N k ↦ |inner ℝ v w|) (Model.noiseLaw N k) := by
    simpa only [Real.norm_eq_abs] using ((projection_memLp_two v).integrable (by norm_num)).norm
  have hle := integral_mono_ae ((integrable_const |a|).sub hf)
    ((hz.const_mul 2).div_const s)
    (Filter.Eventually.of_forall fun w ↦ scalar_orientation_loss s a (inner ℝ v w) hs)
  simp only [Pi.sub_apply] at hle
  rw [integral_sub (integrable_const |a|) hf] at hle
  simp only [integral_const, probReal_univ,
    one_smul, integral_div, integral_const_mul] at hle
  have hnoise' : 2 * (∫ w, |inner ℝ v w| ∂Model.noiseLaw N k) ≤ (2 : ℝ) := by
    linarith [integral_abs_projection_le_one v hv]
  have hnoise : 2 * (∫ w, |inner ℝ v w| ∂Model.noiseLaw N k) / s ≤ 2 / s :=
    div_le_div_of_nonneg_right hnoise' hs.le
  linarith

theorem noise_fst_hasGaussianLaw (N k : ℕ) :
    HasGaussianLaw (Prod.fst : Model.Tensor N k × Model.Tensor N k → Model.Tensor N k)
      ((Model.noiseLaw N k).prod (Model.noiseLaw N k)) := by
  constructor
  · exact measurable_fst.aemeasurable
  · simpa only [Measure.map_fst_prod, measure_univ, one_smul] using noiseLaw_isGaussian N k

theorem noise_snd_hasGaussianLaw (N k : ℕ) :
    HasGaussianLaw (Prod.snd : Model.Tensor N k × Model.Tensor N k → Model.Tensor N k)
      ((Model.noiseLaw N k).prod (Model.noiseLaw N k)) := by
  constructor
  · exact measurable_snd.aemeasurable
  · simpa only [Measure.map_snd_prod, measure_univ, one_smul] using noiseLaw_isGaussian N k

/-- The orthogonal validation-noise mixing map before specializing coefficients. -/
noncomputable def noiseMix {N k : ℕ} (a b : ℝ) :
    (Model.Tensor N k × Model.Tensor N k) →L[ℝ] (Model.Tensor N k × Model.Tensor N k) :=
  (a • ContinuousLinearMap.fst ℝ (Model.Tensor N k) (Model.Tensor N k) +
    b • ContinuousLinearMap.snd ℝ (Model.Tensor N k) (Model.Tensor N k)).prod
      (b • ContinuousLinearMap.fst ℝ (Model.Tensor N k) (Model.Tensor N k) -
        a • ContinuousLinearMap.snd ℝ (Model.Tensor N k) (Model.Tensor N k))

@[simp] theorem noiseMix_apply {N k : ℕ} (a b : ℝ)
    (z : Model.Tensor N k × Model.Tensor N k) :
    noiseMix a b z = (a • z.1 + b • z.2, b • z.1 - a • z.2) := rfl

theorem noiseMix_hasGaussianLaw (N k : ℕ) (a b : ℝ) :
    HasGaussianLaw (noiseMix (N := N) (k := k) a b)
      ((Model.noiseLaw N k).prod (Model.noiseLaw N k)) := by
  have hpair := IndepFun.hasGaussianLaw (noise_fst_hasGaussianLaw N k)
    (noise_snd_hasGaussianLaw N k) (indepFun_prod measurable_id measurable_id)
  exact hpair.map_fun (noiseMix a b)

theorem covariance_projection_fst_eq_snd {N k : ℕ} (x y : Model.Tensor N k) :
    cov[fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ x z.1,
      fun z ↦ inner ℝ y z.1; (Model.noiseLaw N k).prod (Model.noiseLaw N k)] =
    cov[fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ x z.2,
      fun z ↦ inner ℝ y z.2; (Model.noiseLaw N k).prod (Model.noiseLaw N k)] := by
  have hfst := covariance_map_fun (μ := (Model.noiseLaw N k).prod (Model.noiseLaw N k))
    (Z := Prod.fst) (X := fun w : Model.Tensor N k ↦ inner ℝ x w)
    (Y := fun w : Model.Tensor N k ↦ inner ℝ y w)
    (by fun_prop) (by fun_prop) measurable_fst.aemeasurable
  have hsnd := covariance_map_fun (μ := (Model.noiseLaw N k).prod (Model.noiseLaw N k))
    (Z := Prod.snd) (X := fun w : Model.Tensor N k ↦ inner ℝ x w)
    (Y := fun w : Model.Tensor N k ↦ inner ℝ y w)
    (by fun_prop) (by fun_prop) measurable_snd.aemeasurable
  simp only [Measure.map_fst_prod, measure_univ, one_smul] at hfst
  simp only [Measure.map_snd_prod, measure_univ, one_smul] at hsnd
  exact hfst.symm.trans hsnd

/-- The two Gaussian mixtures have zero cross covariance, for all coefficients. -/
theorem covariance_noiseMix_eq_zero {N k : ℕ} (a b : ℝ) (x y : Model.Tensor N k) :
    cov[fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ x (a • z.1 + b • z.2),
      fun z ↦ inner ℝ y (b • z.1 - a • z.2);
      (Model.noiseLaw N k).prod (Model.noiseLaw N k)] = 0 := by
  have hxf := (noise_fst_hasGaussianLaw N k).memLp_two.const_inner (𝕜 := ℝ) x
  have hxg := (noise_snd_hasGaussianLaw N k).memLp_two.const_inner (𝕜 := ℝ) x
  have hyf := (noise_fst_hasGaussianLaw N k).memLp_two.const_inner (𝕜 := ℝ) y
  have hyg := (noise_snd_hasGaussianLaw N k).memLp_two.const_inner (𝕜 := ℝ) y
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right]
  change cov[a • (fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ x z.1) +
      b • (fun z ↦ inner ℝ x z.2),
    b • (fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ y z.1) -
      a • (fun z ↦ inner ℝ y z.2);
    (Model.noiseLaw N k).prod (Model.noiseLaw N k)] = 0
  rw [covariance_sub_right ((hxf.const_smul a).add (hxg.const_smul b))
      (hyf.const_smul b) (hyg.const_smul a),
    covariance_add_left (hxf.const_smul a) (hxg.const_smul b) (hyf.const_smul b),
    covariance_add_left (hxf.const_smul a) (hxg.const_smul b) (hyg.const_smul a)]
  simp only [covariance_smul_left, covariance_smul_right]
  have hxy := covariance_fst_snd_prod (projection_memLp_two x) (projection_memLp_two y)
  have hyx := covariance_fst_snd_prod (projection_memLp_two y) (projection_memLp_two x)
  rw [hxy, covariance_comm (fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ x z.2)
    (fun z ↦ inner ℝ y z.1), hyx,
    covariance_projection_fst_eq_snd x y]
  ring

/-- The validation-noise coordinates are independent, as uncorrelated jointly
Gaussian variables. -/
theorem noiseMix_indepFun (N k : ℕ) (a b : ℝ) :
    IndepFun (fun z : Model.Tensor N k × Model.Tensor N k ↦ a • z.1 + b • z.2)
      (fun z ↦ b • z.1 - a • z.2)
      ((Model.noiseLaw N k).prod (Model.noiseLaw N k)) :=
  (noiseMix_hasGaussianLaw N k a b).indepFun_of_covariance_inner
    (covariance_noiseMix_eq_zero a b)

theorem integral_noiseSum_projection {N k : ℕ} (a b : ℝ) (x : Model.Tensor N k) :
    (∫ z, inner ℝ x (a • z.1 + b • z.2)
      ∂(Model.noiseLaw N k).prod (Model.noiseLaw N k)) = 0 := by
  have hxf := ((noise_fst_hasGaussianLaw N k).memLp_two.const_inner (𝕜 := ℝ) x).integrable
    (by norm_num)
  have hxg := ((noise_snd_hasGaussianLaw N k).memLp_two.const_inner (𝕜 := ℝ) x).integrable
    (by norm_num)
  simp only [inner_add_right, real_inner_smul_right]
  rw [integral_add
    (f := fun z : Model.Tensor N k × Model.Tensor N k ↦ a * inner ℝ x z.1)
    (g := fun z : Model.Tensor N k × Model.Tensor N k ↦ b * inner ℝ x z.2)
    (hxf.const_mul a) (hxg.const_mul b), integral_const_mul, integral_const_mul,
    integral_fun_fst (fun w : Model.Tensor N k ↦ inner ℝ x w),
    integral_fun_snd (fun w : Model.Tensor N k ↦ inner ℝ x w), integral_projection N k x]
  simp

theorem variance_noiseSum_projection {N k : ℕ} (a b : ℝ) (x : Model.Tensor N k) :
    Var[fun z : Model.Tensor N k × Model.Tensor N k ↦ inner ℝ x (a • z.1 + b • z.2);
      (Model.noiseLaw N k).prod (Model.noiseLaw N k)] = (a ^ 2 + b ^ 2) * ‖x‖ ^ 2 := by
  simp only [inner_add_right, real_inner_smul_right]
  rw [variance_add_prod ((projection_memLp_two x).const_mul a)
    ((projection_memLp_two x).const_mul b), variance_const_mul, variance_const_mul]
  have hvar : Var[fun w : Model.Tensor N k ↦ inner ℝ x w; Model.noiseLaw N k] = ‖x‖ ^ 2 := by
    simpa only [Model.noiseLaw, coe_innerSL_apply, innerSL_apply_norm] using
      variance_dual_stdGaussian (innerSL ℝ x)
  rw [hvar]
  ring

/-- A normalized linear mixture of independent standard Gaussian tensors is
again a standard Gaussian tensor. -/
theorem noiseSum_map (N k : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((Model.noiseLaw N k).prod (Model.noiseLaw N k)).map
      (fun z ↦ a • z.1 + b • z.2) = Model.noiseLaw N k := by
  have hG : HasGaussianLaw (fun z : Model.Tensor N k × Model.Tensor N k ↦
      a • z.1 + b • z.2) ((Model.noiseLaw N k).prod (Model.noiseLaw N k)) :=
    (noiseMix_hasGaussianLaw N k a b).fst
  apply Measure.ext_of_charFun
  ext x
  rw [hG.charFun_map_eq x, integral_noiseSum_projection, variance_noiseSum_projection, hab]
  simp [Model.noiseLaw, charFun_stdGaussian, neg_div]

/-- The full Gaussian validation split preserves the independent product law. -/
theorem noiseMix_map (N k : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((Model.noiseLaw N k).prod (Model.noiseLaw N k)).map (noiseMix a b) =
      (Model.noiseLaw N k).prod (Model.noiseLaw N k) := by
  have hsecond := noiseSum_map N k b (-a) (by nlinarith [hab])
  simp only [neg_smul, ← sub_eq_add_neg] at hsecond
  change ((Model.noiseLaw N k).prod (Model.noiseLaw N k)).map
    (fun z ↦ (a • z.1 + b • z.2, b • z.1 - a • z.2)) = _
  rw [(noiseMix_indepFun N k a b).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    noiseSum_map N k a b hab, hsecond]

/-- Orient a vector using the independent validation score, with plus sign at zero. -/
noncomputable def orient {N k : ℕ} (y : Model.Tensor N k) (v : Model.Vector N) : Model.Vector N :=
  if 0 ≤ Model.score y v then v else -v

theorem norm_orient {N k : ℕ} (y : Model.Tensor N k) (v : Model.Vector N) :
    ‖orient y v‖ = ‖v‖ := by
  unfold orient
  split_ifs <;> simp

theorem measurable_orient (N k : ℕ) :
    Measurable (fun z : Model.Tensor N k × Model.Vector N ↦ orient z.1 z.2) := by
  have hc : Continuous (fun z : Model.Tensor N k × Model.Vector N ↦ Model.score z.1 z.2) :=
    ((Model.continuous_feature N k).comp continuous_snd).inner continuous_fst
  exact Measurable.ite (measurableSet_le measurable_const hc.measurable)
    measurable_snd measurable_snd.neg

theorem inner_orient_pow {N k : ℕ} (hk : Odd k) (y : Model.Tensor N k)
    (v x : Model.Vector N) :
    (inner ℝ (orient y v) x) ^ k =
      if 0 ≤ Model.score y v then (inner ℝ v x) ^ k else -(inner ℝ v x) ^ k := by
  unfold orient
  split_ifs <;> simp [hk.neg_pow]

theorem validation_score {N k : ℕ} (s : ℝ) (x v : Model.Vector N) (w : Model.Tensor N k) :
    Model.score (s • Model.feature k x + w) v =
      s * (inner ℝ v x) ^ k + inner ℝ (Model.feature k v) w := by
  simp only [Model.score, inner_add_right, real_inner_smul_right, Geometry.feature_inner]

/-- The actual odd-order overlap after orienting by a fresh validation channel
loses at most `2/s` in expectation. The estimator vector and planted vector are
fixed here; Fubini supplies the random-estimator version. -/
theorem integral_oriented_overlap_lower_bound {N k : ℕ} (hk : Odd k) (s : ℝ) (hs : 0 < s)
    (x v : Model.Vector N) (hv : ‖v‖ = 1) :
    |inner ℝ v x| ^ k - 2 / s ≤
      ∫ w, (inner ℝ (orient (s • Model.feature k x + w) v) x) ^ k
        ∂Model.noiseLaw N k := by
  have hfeature : ‖Model.feature k v‖ = 1 := Geometry.feature_unit_norm v hv
  simpa only [inner_orient_pow hk, validation_score, abs_pow] using
    integral_oriented_scalar_lower_bound s ((inner ℝ v x) ^ k) hs (Model.feature k v) hfeature

theorem measurePreserving_noiseMix (N k : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (noiseMix (N := N) (k := k) a b)
      ((Model.noiseLaw N k).prod (Model.noiseLaw N k))
      ((Model.noiseLaw N k).prod (Model.noiseLaw N k)) :=
  ⟨(noiseMix a b).continuous.measurable, noiseMix_map N k a b hab⟩

/-- Mix the two tensor noises while preserving the planted vector. -/
noncomputable def experimentMix {N k : ℕ} (a b : ℝ)
    (z : (Model.Vector N × Model.Tensor N k) × Model.Tensor N k) :
    (Model.Vector N × Model.Tensor N k) × Model.Tensor N k :=
  ((z.1.1, a • z.1.2 + b • z.2), b • z.1.2 - a • z.2)

theorem measurePreserving_experimentMix (N k : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (experimentMix (N := N) (k := k) a b)
      ((Model.experimentLaw N k).prod (Model.noiseLaw N k))
      ((Model.experimentLaw N k).prod (Model.noiseLaw N k)) := by
  have hAssoc := measurePreserving_prodAssoc (Model.spherePrior N) (Model.noiseLaw N k)
    (Model.noiseLaw N k)
  have hMix := (MeasurePreserving.id (Model.spherePrior N)).prod
    (measurePreserving_noiseMix N k a b hab)
  have h := (MeasurePreserving.symm MeasurableEquiv.prodAssoc hAssoc).comp (hMix.comp hAssoc)
  exact h

theorem mix_observation_first {N k : ℕ} (a b rho lam : ℝ) (ha : a * rho = lam)
    (x : Model.Vector N) (w g : Model.Tensor N k) :
    a • Model.observation rho (x, w) + b • g =
      Model.observation lam (x, a • w + b • g) := by
  simp only [Model.observation, smul_add, smul_smul, ← mul_assoc, ha, add_assoc]

theorem mix_observation_second {N k : ℕ} (a b rho delta : ℝ) (hb : b * rho = delta)
    (x : Model.Vector N) (w g : Model.Tensor N k) :
    b • Model.observation rho (x, w) - a • g =
      Model.observation delta (x, b • w - a • g) := by
  simp only [Model.observation, smul_add, smul_smul, ← mul_assoc, hb,
    sub_eq_add_neg, add_assoc]

/-- The estimator produced by the Gaussian split and the validation sign. -/
noncomputable def validationEstimator {N k : ℕ} {A : Type*} (a b : ℝ)
    (est : Model.Estimator N k A) : Model.Estimator N k (Model.Tensor N k × A) :=
  fun y z ↦ orient (b • y - a • z.1) (est (a • y + b • z.1) z.2)

theorem validationEstimator_isUnitEstimator {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (a b : ℝ) (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.IsUnitEstimator (validationEstimator a b est) := by
  constructor
  · change Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦
      orient (b • z.1 - a • z.2.1) (est (a • z.1 + b • z.2.1) z.2.2))
    have hfirst : Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦
        a • z.1 + b • z.2.1) := by fun_prop
    have hsecond : Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦
        b • z.1 - a • z.2.1) := by fun_prop
    have haux : Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦ z.2.2) :=
      measurable_snd.comp measurable_snd
    have hbase : Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦
        est (a • z.1 + b • z.2.1) z.2.2) := hest.1.comp (hfirst.prodMk haux)
    change Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦
      if 0 ≤ Model.score (b • z.1 - a • z.2.1) (est (a • z.1 + b • z.2.1) z.2.2)
      then est (a • z.1 + b • z.2.1) z.2.2 else -est (a • z.1 + b • z.2.1) z.2.2)
    have hc_score : Continuous (fun z : Model.Tensor N k × Model.Vector N ↦ Model.score z.1 z.2) :=
      ((Model.continuous_feature N k).comp continuous_snd).inner continuous_fst
    have hscore : Measurable (fun z : Model.Tensor N k × (Model.Tensor N k × A) ↦
        Model.score (b • z.1 - a • z.2.1) (est (a • z.1 + b • z.2.1) z.2.2)) :=
      Continuous.measurable2 hc_score hsecond hbase
    exact Measurable.ite (measurableSet_le measurable_const hscore) hbase hbase.neg
  · intro y z
    change ‖orient (b • y - a • z.1) (est (a • y + b • z.1) z.2)‖ = 1
    rw [norm_orient]
    exact hest.2 _ _

theorem measurePreserving_swapLast {E F A : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace A]
    (μ : Measure E) (ν : Measure F) (τ : Measure A)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving (fun z : (E × F) × A ↦ ((z.1.1, z.2), z.1.2))
      ((μ.prod ν).prod τ) ((μ.prod τ).prod ν) := by
  have hAssoc₁ := measurePreserving_prodAssoc μ ν τ
  have hSwap := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := τ))
  have hAssoc₂ := measurePreserving_prodAssoc μ τ ν
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc hAssoc₂).comp (hSwap.comp hAssoc₁)

/-- The full split preserves the original signal and independent auxiliary law,
placing the fresh validation noise in the last coordinate for Fubini. -/
theorem measurePreserving_augmentedMix (N k : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : (Model.Vector N × Model.Tensor N k) × (Model.Tensor N k × A) ↦
      (((z.1.1, a • z.1.2 + b • z.2.1), z.2.2), b • z.1.2 - a • z.2.1))
      ((Model.experimentLaw N k).prod ((Model.noiseLaw N k).prod ν))
      (((Model.experimentLaw N k).prod ν).prod (Model.noiseLaw N k)) := by
  have hAssoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (Model.experimentLaw N k) (Model.noiseLaw N k) ν)
  have hMix := (measurePreserving_experimentMix N k a b hab).prod (MeasurePreserving.id ν)
  have hSwap := measurePreserving_swapLast (Model.experimentLaw N k) (Model.noiseLaw N k) ν
  exact hSwap.comp (hMix.comp hAssoc)

theorem measurable_orient_comp {E : Type*} [MeasurableSpace E] {N k : ℕ}
    (y : E → Model.Tensor N k) (v : E → Model.Vector N)
    (hy : Measurable y) (hv : Measurable v) : Measurable (fun z ↦ orient (y z) (v z)) := by
  have hc : Continuous (fun p : Model.Tensor N k × Model.Vector N ↦ Model.score p.1 p.2) :=
    ((Model.continuous_feature N k).comp continuous_snd).inner continuous_fst
  exact Measurable.ite (measurableSet_le measurable_const (Continuous.measurable2 hc hy hv))
    hv hv.neg

theorem integrable_inner_pow_of_unit {E : Type*} [MeasurableSpace E] {N : ℕ}
    (μ : Measure E) [IsFiniteMeasure μ] (k : ℕ) (x v : E → Model.Vector N)
    (hx : Measurable x) (hv : Measurable v)
    (hx_norm : ∀ᵐ z ∂μ, ‖x z‖ = 1) (hv_norm : ∀ᵐ z ∂μ, ‖v z‖ = 1) :
    Integrable (fun z ↦ (inner ℝ (v z) (x z)) ^ k) μ := by
  have hmeas : Measurable (fun z ↦ (inner ℝ (v z) (x z)) ^ k) :=
    (Continuous.measurable2 (continuous_inner (𝕜 := ℝ)) hv hx).pow_const k
  apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [hx_norm, hv_norm] with z hzx hzv
  have hinner : |inner ℝ (v z) (x z)| ≤ 1 := by
    simpa only [hzx, hzv, one_mul] using abs_real_inner_le_norm (v z) (x z)
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_one₀ (abs_nonneg _) hinner

theorem experiment_vector_norm_ae {N k : ℕ} (hN : 0 < N) :
    ∀ᵐ z ∂Model.experimentLaw N k, ‖z.1‖ = 1 :=
  Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)

/-- The actual signed overlap after using a fresh independent validation noise. -/
noncomputable def validatedOverlap {N k : ℕ} {A : Type*} (lam delta : ℝ)
    (est : Model.Estimator N k A)
    (z : ((Model.Vector N × Model.Tensor N k) × A) × Model.Tensor N k) : ℝ :=
  (inner ℝ (orient (Model.observation delta (z.1.1.1, z.2))
    (est (Model.observation lam z.1.1) z.1.2)) z.1.1.1) ^ k

theorem measurable_validatedOverlap {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (lam delta : ℝ) (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Measurable (validatedOverlap lam delta est) := by
  have hx : Measurable (fun z : ((Model.Vector N × Model.Tensor N k) × A) × Model.Tensor N k ↦
      z.1.1.1) := measurable_fst.comp (measurable_fst.comp measurable_fst)
  have he : Measurable (fun z : ((Model.Vector N × Model.Tensor N k) × A) × Model.Tensor N k ↦
      z.1.1) := measurable_fst.comp measurable_fst
  have ha : Measurable (fun z : ((Model.Vector N × Model.Tensor N k) × A) × Model.Tensor N k ↦
      z.1.2) := measurable_snd.comp measurable_fst
  have hv : Measurable (fun z : ((Model.Vector N × Model.Tensor N k) × A) × Model.Tensor N k ↦
      est (Model.observation lam z.1.1) z.1.2) :=
    hest.1.comp (((Model.measurable_observation N k lam).comp he).prodMk ha)
  have hy : Measurable (fun z : ((Model.Vector N × Model.Tensor N k) × A) × Model.Tensor N k ↦
      Model.observation delta (z.1.1.1, z.2)) :=
    (Model.measurable_observation N k delta).comp (hx.prodMk measurable_snd)
  exact (Continuous.measurable2 (continuous_inner (𝕜 := ℝ))
    (measurable_orient_comp _ _ hy hv) hx).pow_const k

theorem integrable_validatedOverlap {N k : ℕ} (hN : 0 < N)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (lam delta : ℝ) (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Integrable (validatedOverlap lam delta est)
      (((Model.experimentLaw N k).prod ν).prod (Model.noiseLaw N k)) := by
  have hx : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ‖z.1.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (experiment_vector_norm_ae hN)
  have hx' : ∀ᵐ z ∂((Model.experimentLaw N k).prod ν).prod (Model.noiseLaw N k),
      ‖z.1.1.1‖ = 1 := Measure.quasiMeasurePreserving_fst.ae hx
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_validatedOverlap lam delta est hest).aestronglyMeasurable
  filter_upwards [hx'] with z hz
  have ho : ‖orient (Model.observation delta (z.1.1.1, z.2))
      (est (Model.observation lam z.1.1) z.1.2)‖ = 1 := (norm_orient _ _).trans (hest.2 _ _)
  have hi := abs_real_inner_le_norm
    (orient (Model.observation delta (z.1.1.1, z.2))
      (est (Model.observation lam z.1.1) z.1.2)) z.1.1.1
  simp only [ho, hz, one_mul] at hi
  simpa only [validatedOverlap, Real.norm_eq_abs, abs_pow] using pow_le_one₀ (abs_nonneg _) hi

theorem integrable_absolute_overlap {N k : ℕ} (hN : 0 < N)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (lam : ℝ) (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Integrable (fun z ↦ |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1| ^ k)
      ((Model.experimentLaw N k).prod ν) := by
  have hx : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ‖z.1.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (experiment_vector_norm_ae hN)
  have hv : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      est (Model.observation lam z.1) z.2) :=
    hest.1.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk measurable_snd)
  have h := integrable_inner_pow_of_unit ((Model.experimentLaw N k).prod ν) k
    (fun z ↦ z.1.1) (fun z ↦ est (Model.observation lam z.1) z.2)
    (measurable_fst.comp measurable_fst) hv hx
    (Filter.Eventually.of_forall fun z ↦ hest.2 _ _)
  simpa only [abs_pow] using h.abs

/-- The validation loss estimate also holds for even orders, where the sign
does not alter the kth power. -/
theorem integral_oriented_overlap_lower_bound_all {N k : ℕ} (s : ℝ) (hs : 0 < s)
    (x v : Model.Vector N) (hv : ‖v‖ = 1) :
    |inner ℝ v x| ^ k - 2 / s ≤
      ∫ w, (inner ℝ (orient (s • Model.feature k x + w) v) x) ^ k
        ∂Model.noiseLaw N k := by
  rcases Nat.even_or_odd k with hk | hk
  · have heq (w : Model.Tensor N k) :
        (inner ℝ (orient (s • Model.feature k x + w) v) x) ^ k = |inner ℝ v x| ^ k := by
      unfold orient
      split_ifs <;> simp [hk.neg_pow, hk.pow_abs]
    rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
    simp only [integral_const, probReal_univ, one_smul]
    exact sub_le_self _ (div_nonneg (by norm_num) hs.le)
  · exact integral_oriented_overlap_lower_bound hk s hs x v hv

theorem expectedOverlapPower_sub_le_validated {N k : ℕ} (hN : 0 < N)
    (lam delta : ℝ) (hdelta : 0 < delta)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k lam est ν k - 2 / (delta * Real.sqrt N) ≤
      ∫ z, validatedOverlap lam delta est z
        ∂((Model.experimentLaw N k).prod ν).prod (Model.noiseLaw N k) := by
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hs : 0 < delta * Real.sqrt N := mul_pos hdelta hsqrt
  have hF := integrable_validatedOverlap hN ν lam delta est hest
  have hA := integrable_absolute_overlap hN ν lam est hest
  unfold Model.expectedOverlapPower
  calc
    _ = ∫ z : (Model.Vector N × Model.Tensor N k) × A,
        |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1| ^ k -
          2 / (delta * Real.sqrt N) ∂(Model.experimentLaw N k).prod ν := by
      rw [integral_sub (f := fun z : (Model.Vector N × Model.Tensor N k) × A ↦
        |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1| ^ k)
        (g := fun _ ↦ 2 / (delta * Real.sqrt N)) hA (integrable_const _)]
      simp
    _ ≤ ∫ z : (Model.Vector N × Model.Tensor N k) × A,
        ∫ w, validatedOverlap lam delta est (z, w) ∂Model.noiseLaw N k
          ∂(Model.experimentLaw N k).prod ν := by
      apply integral_mono_ae (hA.sub (integrable_const _)) hF.integral_prod_left
      filter_upwards with z
      simpa only [Pi.sub_apply, validatedOverlap, Model.observation] using
        integral_oriented_overlap_lower_bound_all (delta * Real.sqrt N) hs z.1.1
          (est (Model.observation lam z.1) z.2) (hest.2 _ _)
    _ = _ := (integral_prod _ hF).symm

theorem integral_validated_le_sqrt_one_sub_tensorMMSE {N k : ℕ} (hN : 0 < N)
    (lam delta rho a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (ha : a * rho = lam) (hb : b * rho = delta)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    (∫ z, validatedOverlap lam delta est z
      ∂((Model.experimentLaw N k).prod ν).prod (Model.noiseLaw N k)) ≤
      Real.sqrt (1 - Model.tensorMMSE N k rho) := by
  have hMix := measurePreserving_augmentedMix N k a b hab ν
  have hbridge (z : (Model.Vector N × Model.Tensor N k) × (Model.Tensor N k × A)) :
      validatedOverlap lam delta est
        (((z.1.1, a • z.1.2 + b • z.2.1), z.2.2), b • z.1.2 - a • z.2.1) =
      (inner ℝ (validationEstimator a b est (Model.observation rho z.1) z.2) z.1.1) ^ k := by
    unfold validatedOverlap validationEstimator
    rw [← mix_observation_first a b rho lam ha z.1.1 z.1.2 z.2.1,
      ← mix_observation_second a b rho delta hb z.1.1 z.1.2 z.2.1]
  calc
    _ = ∫ z, validatedOverlap lam delta est
        (((z.1.1, a • z.1.2 + b • z.2.1), z.2.2), b • z.1.2 - a • z.2.1)
          ∂(Model.experimentLaw N k).prod ((Model.noiseLaw N k).prod ν) := by
      rw [← hMix.map_eq]
      exact integral_map hMix.aemeasurable
        (measurable_validatedOverlap lam delta est hest).aestronglyMeasurable
    _ = ∫ z, (inner ℝ (validationEstimator a b est (Model.observation rho z.1) z.2) z.1.1) ^ k
        ∂(Model.experimentLaw N k).prod ((Model.noiseLaw N k).prod ν) :=
      integral_congr_ae (Filter.Eventually.of_forall hbridge)
    _ ≤ _ := PosteriorProofs.signed_overlap_le_sqrt_one_sub_tensorMMSE hN rho
      ((Model.noiseLaw N k).prod ν) (validationEstimator a b est)
      (validationEstimator_isUnitEstimator a b est hest)

/-- The complete finite validation bound, including arbitrary independent
auxiliary randomness. No asymptotic MMSE assertion is assumed. -/
theorem expectedOverlapPower_le_validation {N k : ℕ} (hN : 0 < N)
    (lam delta : ℝ) (hdelta : 0 < delta)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k lam est ν k ≤
      Real.sqrt (1 - Model.tensorMMSE N k (Real.sqrt (lam ^ 2 + delta ^ 2))) +
        2 / (delta * Real.sqrt N) := by
  let rho := Real.sqrt (lam ^ 2 + delta ^ 2)
  have hrho : 0 < rho := Real.sqrt_pos.2 (by nlinarith [sq_nonneg lam, sq_pos_of_pos hdelta])
  have hrho_sq : rho ^ 2 = lam ^ 2 + delta ^ 2 := Real.sq_sqrt (by positivity)
  have hab : (lam / rho) ^ 2 + (delta / rho) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hrho_sq, div_self (pow_ne_zero 2 hrho.ne')]
  have hlower := expectedOverlapPower_sub_le_validated hN lam delta hdelta ν est hest
  have hupper := integral_validated_le_sqrt_one_sub_tensorMMSE hN lam delta rho
    (lam / rho) (delta / rho) hab (div_mul_cancel₀ lam hrho.ne')
    (div_mul_cancel₀ delta hrho.ne') ν est hest
  change Model.expectedOverlapPower N k lam est ν k ≤
    Real.sqrt (1 - Model.tensorMMSE N k rho) + 2 / (delta * Real.sqrt N)
  linarith


end TensorPCA.OddValidationProofs
