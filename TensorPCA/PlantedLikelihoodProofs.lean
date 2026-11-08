-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NullNormalizedLikelihoodProofs
public import TensorPCA.FreeEnergyConcentrationProofs
public import TensorPCA.MaximumProofs
public import TensorPCA.CheckedReduction
public import TensorPCA.GibbsSmoothProofs

/-! The planted normalized log likelihood has a rotationally constant
conditional mean and the Gaussian fluctuation scale |lambda|/sqrt(N).
No asymptotic Bayesian value theorem is used for these finite facts. -/
@[expose] public section
namespace TensorPCA.PlantedLikelihoodProofs
open MeasureTheory ProbabilityTheory Set Filter Geometry
open scoped Topology RealInnerProductSpace ENNReal NNReal ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def normalizedLogLikelihood (N k : ℕ) (lam : ℝ) (y : Model.Tensor N k) : ℝ :=
  Statistical.nullLogLikelihood N k lam y/(N : ℝ)

theorem normalizedLogLikelihood_eq {N k : ℕ} (hN : 0 < N) (lam : ℝ) (y : Model.Tensor N k) :
    normalizedLogLikelihood N k lam y = Model.freeEnergy N k lam (-y)-lam^2/2 :=
  NullNormalizedLikelihoodProofs.normalizedNullLogLikelihood_eq hN lam y

theorem normalizedLogLikelihood_lipschitz {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    LipschitzWith (|lam|/Real.sqrt N).toNNReal (normalizedLogLikelihood N k lam) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [normalizedLogLikelihood_eq hN lam,dist_sub_right,dist_neg_neg] using
    (FreeEnergyConcentrationProofs.freeEnergy_lipschitz (k := k) hN lam).dist_le_mul (-x) (-y)

theorem shifted_normalizedLogLikelihood_lipschitz {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (shift : Model.Tensor N k) :
    LipschitzWith (|lam|/Real.sqrt N).toNNReal
      (fun w : Model.Tensor N k ↦ normalizedLogLikelihood N k lam (shift+w)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_add_left] using
    (normalizedLogLikelihood_lipschitz hN lam).dist_le_mul (shift+x) (shift+y)

theorem likelihoodRatio_tensorRotation {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (lam : ℝ) (y : Model.Tensor N k) :
    Model.likelihoodRatio N k lam (tensorRotation hN U y) = Model.likelihoodRatio N k lam y := by
  unfold Model.likelihoodRatio
  rw [← spherePrior_integral_comp_isometry U
    (fun x ↦ Real.exp (lam*Real.sqrt N*Model.score (tensorRotation hN U y) x-(N : ℝ)*lam^2/2))
    (GaussianChannelProofs.continuous_likelihoodWeight N k lam (tensorRotation hN U y))]
  simp_rw [score_tensorRotation hN U]

theorem normalizedLogLikelihood_tensorRotation {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (lam : ℝ) (y : Model.Tensor N k) :
    normalizedLogLikelihood N k lam (tensorRotation hN U y) = normalizedLogLikelihood N k lam y := by
  simp only [normalizedLogLikelihood,Statistical.nullLogLikelihood,likelihoodRatio_tensorRotation hN U]

theorem plantedLogLikelihood_mean_eq_of_unit {N k : ℕ} (hN : 0 < N)
    (x v : Model.Vector N) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) (lam : ℝ) :
    (∫ w, normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k x+w)
      ∂Model.noiseLaw N k) =
      ∫ w, normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k v+w)
        ∂Model.noiseLaw N k := by
  let U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := (ℝ ∙ (x-v))ᗮ.reflection
  have hu : U x = v := Submodule.reflection_sub (hx.trans hv.symm)
  let T := tensorRotation (k := k) hN U
  have hshift (w : Model.Tensor N k) :
      normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k v+T w) =
        normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k x+w) := by
    rw [← hu,← tensorRotation_feature hN U x,← T.map_smul,← T.map_add]
    exact normalizedLogLikelihood_tensorRotation hN U lam _
  have hmap : (Model.noiseLaw N k).map T = Model.noiseLaw N k := stdGaussian_map T
  have hF : Continuous (fun w : Model.Tensor N k ↦
      normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k v+w)) :=
    (shifted_normalizedLogLikelihood_lipschitz hN lam _).continuous
  have hi := integral_map (μ := Model.noiseLaw N k) T.continuous.measurable.aemeasurable
    hF.aestronglyMeasurable
  rw [hmap] at hi
  calc
    _ = ∫ w, normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k v+T w)
        ∂Model.noiseLaw N k := integral_congr_ae (.of_forall fun w ↦ (hshift w).symm)
    _ = _ := hi.symm

/-- Composition with a Lipschitz observable needs no false zero-at-origin
claim: first subtract its actual value at zero, then add it back. -/
theorem normalizedLogLikelihood_comp_memLp {Ω : Type*} [MeasurableSpace Ω]
    {N k : ℕ} (hN : 0 < N) (lam : ℝ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → Model.Tensor N k) (hF : MemLp F 2 μ) :
    MemLp (fun z ↦ normalizedLogLikelihood N k lam (F z)) 2 μ := by
  have hl : LipschitzWith (|lam|/Real.sqrt N).toNNReal
      (fun y : Model.Tensor N k ↦ normalizedLogLikelihood N k lam y-normalizedLogLikelihood N k lam 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using (normalizedLogLikelihood_lipschitz hN lam).dist_le_mul x y
  have hc := hl.comp_memLp (by simp) hF
  apply MemLp.ae_eq ?_ (hc.add (memLp_const (normalizedLogLikelihood N k lam 0)))
  exact .of_forall fun z ↦ by simp only [Function.comp_def,Pi.add_apply,sub_add_cancel]

theorem plantedLogLikelihood_memLp_two {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    MemLp (fun z ↦ normalizedLogLikelihood N k lam (Model.observation lam z))
      2 (Model.experimentLaw N k) :=
  normalizedLogLikelihood_comp_memLp hN lam _ _ (MaximumProofs.observation_memLp_two hN lam)

theorem plantedLogLikelihood_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z ↦ normalizedLogLikelihood N k lam (Model.observation lam z))
      (Model.experimentLaw N k) :=
  (plantedLogLikelihood_memLp_two hN lam).integrable (by norm_num)

theorem plantedLogLikelihood_mean_eq_freeEnergy {N k : ℕ} {lam : ℝ}
    (hlam : 0 ≤ lam) :
    (∫ z, normalizedLogLikelihood N k lam (Model.observation lam z) ∂Model.experimentLaw N k) =
      Statistical.sphericalBayesFreeEnergy N k (lam^2) := by
  simp only [normalizedLogLikelihood,Statistical.nullLogLikelihood,Statistical.sphericalBayesFreeEnergy,
    Real.sqrt_sq hlam,integral_div]

theorem plantedLogLikelihood_mean_eq_fixed_direction {N k : ℕ} (hN : 0 < N) {lam : ℝ}
    (hlam : 0 ≤ lam) (v : Model.Vector N) (hv : ‖v‖ = 1) :
    Statistical.sphericalBayesFreeEnergy N k (lam^2) =
      ∫ w, normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k v+w)
        ∂Model.noiseLaw N k := by
  rw [← plantedLogLikelihood_mean_eq_freeEnergy hlam]
  change (∫ z : Model.Vector N × Model.Tensor N k,
    normalizedLogLikelihood N k lam (Model.observation lam z)
      ∂(Model.spherePrior N).prod (Model.noiseLaw N k)) = _
  rw [integral_prod _ (plantedLogLikelihood_integrable hN lam)]
  calc
    _ = ∫ _x : Model.Vector N,
        (∫ w, normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k v+w)
          ∂Model.noiseLaw N k) ∂Model.spherePrior N := by
      apply integral_congr_ae
      filter_upwards [spherePrior_norm_ae hN] with x hx
      exact plantedLogLikelihood_mean_eq_of_unit hN x v hx hv lam
    _ = _ := by simp

theorem smooth_gaussian_lipschitz_variance_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf2 : MemLp f 2 (stdGaussian E)) {K : ℝ≥0} (hLip : LipschitzWith K f) :
    (∫ w, (f w-∫ z, f z ∂stdGaussian E)^2 ∂stdGaussian E) ≤ (K : ℝ)^2 := by
  have hb (w : E) : ‖fderiv ℝ f w‖^2 ≤ (K : ℝ)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hLip) 2
  have hC : Continuous (fun w : E ↦ ‖fderiv ℝ f w‖^2) :=
    (hf.continuous_fderiv (by norm_num)).norm.pow 2
  have hI : Integrable (fun w : E ↦ ‖fderiv ℝ f w‖^2) (stdGaussian E) := by
    apply (integrable_const ((K : ℝ)^2)).mono' hC.aestronglyMeasurable
    exact .of_forall fun w ↦ by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖fderiv ℝ f w‖)] using hb w
  have H := GaussianPoincareProofs.variance_stdGaussian_le_fderiv f hf hf2 hI
  rw [variance_eq_integral hf.continuous.measurable.aemeasurable] at H
  have hbound : (∫ w, ‖fderiv ℝ f w‖^2 ∂stdGaussian E) ≤ (K : ℝ)^2 := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hI (integrable_const ((K : ℝ)^2)) hb
  exact H.trans hbound

theorem shifted_plantedLogLikelihood_variance_le {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (shift : Model.Tensor N k) :
    (∫ w, (normalizedLogLikelihood N k lam (shift+w)-
      ∫ z, normalizedLogLikelihood N k lam (shift+z) ∂Model.noiseLaw N k)^2
        ∂Model.noiseLaw N k) ≤ lam^2/(N : ℝ) := by
  have hC : ContDiff ℝ ∞ (fun w : Model.Tensor N k ↦ normalizedLogLikelihood N k lam (shift+w)) := by
    have H : ContDiff ℝ ∞ (fun w : Model.Tensor N k ↦ Model.freeEnergy N k lam (-(shift+w))-lam^2/2) :=
      ((GibbsSmoothProofs.freeEnergy_contDiff_infty hN lam).comp (by fun_prop)).sub contDiff_const
    simpa only [normalizedLogLikelihood_eq hN lam] using H
  have hW : MemLp (fun w : Model.Tensor N k ↦ shift+w) 2 (Model.noiseLaw N k) :=
    (memLp_const shift).add (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) 2 (by norm_num))
  have hL2 := normalizedLogLikelihood_comp_memLp hN lam _ _ hW
  have H := smooth_gaussian_lipschitz_variance_le _ hC hL2
    (shifted_normalizedLogLikelihood_lipschitz hN lam shift)
  have hK : ((|lam|/Real.sqrt N).toNNReal : ℝ)^2 = lam^2/(N : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity),div_pow,sq_abs,Real.sq_sqrt (Nat.cast_nonneg N)]
  simpa only [Model.noiseLaw,hK] using H

theorem plantedLogLikelihood_centered_sq_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) (c : ℝ) :
    Integrable (fun z ↦ (normalizedLogLikelihood N k lam (Model.observation lam z)-c)^2)
      (Model.experimentLaw N k) := by
  have h := ((plantedLogLikelihood_memLp_two (k := k) hN lam).sub (memLp_const c)).integrable_norm_pow (by decide : 2 ≠ 0)
  simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using h

/-- The latent mixture contributes no variance of its conditional mean: the
actual Gaussian conditional means coincide at every unit planted direction. -/
theorem plantedLogLikelihood_variance_le {N k : ℕ} (hN : 0 < N) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ z, (normalizedLogLikelihood N k lam (Model.observation lam z)-
      Statistical.sphericalBayesFreeEnergy N k (lam^2))^2 ∂Model.experimentLaw N k) ≤ lam^2/(N : ℝ) := by
  let m := Statistical.sphericalBayesFreeEnergy N k (lam^2)
  have hSq : Integrable (fun z : Model.Vector N × Model.Tensor N k ↦
      (normalizedLogLikelihood N k lam (Model.observation lam z)-m)^2)
        ((Model.spherePrior N).prod (Model.noiseLaw N k)) :=
    plantedLogLikelihood_centered_sq_integrable (k := k) hN lam m
  have hbound : ∀ᵐ x : Model.Vector N ∂Model.spherePrior N,
      (∫ w : Model.Tensor N k, (normalizedLogLikelihood N k lam (Model.observation lam (x,w))-m)^2
        ∂Model.noiseLaw N k) ≤ lam^2/(N : ℝ) := by
    filter_upwards [spherePrior_norm_ae hN] with x hx
    have hm : m = ∫ w : Model.Tensor N k,
        normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k x+w)
          ∂Model.noiseLaw N k := plantedLogLikelihood_mean_eq_fixed_direction hN hlam x hx
    change (∫ w : Model.Tensor N k,
      (normalizedLogLikelihood N k lam ((lam*Real.sqrt N) • Model.feature k x+w)-m)^2
        ∂Model.noiseLaw N k) ≤ _
    rw [hm]
    exact shifted_plantedLogLikelihood_variance_le (k := k) hN lam _
  have H := integral_mono_ae hSq.integral_prod_left
    (integrable_const (lam^2/(N : ℝ))) hbound
  rw [integral_const,probReal_univ,one_smul] at H
  calc
    _ = ∫ x : Model.Vector N, ∫ w : Model.Tensor N k,
        (normalizedLogLikelihood N k lam (Model.observation lam (x,w))-m)^2
          ∂Model.noiseLaw N k ∂Model.spherePrior N := integral_prod _ hSq
    _ ≤ _ := H

end
end TensorPCA.PlantedLikelihoodProofs
