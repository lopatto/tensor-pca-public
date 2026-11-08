-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import TensorPCA.PosteriorProofs
public import TensorPCA.Statements
public import TensorPCA.LimitTools

/-!
# Planted maxima and Gaussian concentration

The fixed-direction tensor rotation identities live in Geometry. This module
uses the latent/noise product experiment, proves integrability, and
identifies its annealed expectation with the fixed-direction Gaussian mean.
No asymptotic ground-state formula is assumed.
-/
@[expose] public section

namespace TensorPCA.MaximumProofs
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal RealInnerProductSpace Topology
universe u

/-- The actual planted observation is square integrable under its experiment. -/
theorem observation_memLp_two {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    MemLp (Model.observation (N := N) (k := k) lam) 2 (Model.experimentLaw N k) := by
  have hs := (PosteriorProofs.latent_memLp_two (k := k) hN).const_smul (lam*Real.sqrt N)
  have hw := (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_snd (μ := Model.spherePrior N) (ν := Model.noiseLaw N k))
  exact hs.add hw

/-- The actual planted maximum has a finite second moment. -/
theorem plantedMaximum_memLp_two {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    MemLp (fun z ↦ Model.normalizedMaximum (Model.observation (N := N) (k := k) lam z))
      2 (Model.experimentLaw N k) := by
  simpa only [Function.comp_def] using
    (Geometry.normalizedMaximum_lipschitz (k := k) hN).comp_memLp
      (Geometry.normalizedMaximum_zero hN) (observation_memLp_two hN lam)

/-- Fubini applies to the genuine planted maximum. -/
theorem plantedMaximum_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Integrable (fun z ↦ Model.normalizedMaximum (Model.observation (N := N) (k := k) lam z))
      (Model.experimentLaw N k) :=
  (plantedMaximum_memLp_two hN lam).integrable (by norm_num)

/-- The annealed expectation is the Gaussian expectation at any deterministic
unit planted direction. The actual sphere support and rotational invariance
justify this identity; it is not a centering convention. -/
theorem expectedMaximum_eq_fixed_direction {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (v : Model.Vector N) (hv : ‖v‖ = 1) :
    Model.expectedMaximum N k lam =
      ∫ w, Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v+w)
        ∂Model.noiseLaw N k := by
  unfold Model.expectedMaximum
  change (∫ z : Model.Vector N × Model.Tensor N k,
    Model.normalizedMaximum (Model.observation lam z)
      ∂(Model.spherePrior N).prod (Model.noiseLaw N k)) = _
  rw [integral_prod _ (plantedMaximum_integrable hN lam)]
  calc
    _ = ∫ _x : Model.Vector N,
        (∫ w, Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v+w)
          ∂Model.noiseLaw N k) ∂Model.spherePrior N := by
      apply integral_congr_ae
      filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
      exact Geometry.plantedMaximum_mean_eq_of_unit hN x v hx hv lam
    _ = _ := by simp

/-- Exact Gaussian concentration after averaging the genuine planted signal,
centered at the actual annealed expectation in Model.expectedMaximum. -/
theorem plantedMaximum_gaussian_tail {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (t : ℝ) (ht : 0 < t) :
    Model.experimentLaw N k {z | |Model.normalizedMaximum (Model.observation lam z) -
      Model.expectedMaximum N k lam| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-(N : ℝ) * t^2 / 2)) := by
  have hF : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      |Model.normalizedMaximum (Model.observation lam z)-Model.expectedMaximum N k lam|) :=
    continuous_abs.measurable.comp
      (((Geometry.normalizedMaximum_lipschitz hN).continuous.measurable.comp
        (Model.measurable_observation N k lam)).sub measurable_const)
  have hset : MeasurableSet {z : Model.Vector N × Model.Tensor N k |
      |Model.normalizedMaximum (Model.observation lam z)-Model.expectedMaximum N k lam| > t} :=
    measurableSet_lt measurable_const hF
  change ((Model.spherePrior N).prod (Model.noiseLaw N k)) _ ≤ _
  rw [Measure.prod_apply hset]
  calc
    _ ≤ ∫⁻ _x : Model.Vector N,
        ENNReal.ofReal (2 * Real.exp (-(N : ℝ)*t^2/2)) ∂Model.spherePrior N := by
      apply lintegral_mono_ae
      filter_upwards [Geometry.spherePrior_norm_ae hN] with x hx
      change Model.noiseLaw N k {w | |Model.normalizedMaximum
        ((lam*Real.sqrt N) • Model.feature k x+w)-Model.expectedMaximum N k lam| > t} ≤ _
      rw [expectedMaximum_eq_fixed_direction hN lam x hx]
      exact Geometry.shiftedMaximum_gaussian_tail hN _ t ht
    _ = _ := by simp

/-- The genuine constrained maximum is covariant under simultaneous physical
and tensor rotations. This identity also covers empty slices. -/
theorem constrainedMaximum_tensorRotation {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (x : Model.Vector N)
    (w : Model.Tensor N k) (m : ℝ) :
    Model.constrainedMaximum lam (U x) (Geometry.tensorRotation hN U w) m =
      Model.constrainedMaximum lam x w m := by
  have he : (fun v ↦ lam*m^k + Model.score (Geometry.tensorRotation hN U w) v/Real.sqrt N) ''
      {v ∈ Model.unitSphere N | inner ℝ v (U x) = m} =
      (fun v ↦ lam*m^k + Model.score w v/Real.sqrt N) ''
        {v ∈ Model.unitSphere N | inner ℝ v x = m} := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨U.symm v, ⟨?_, ?_⟩, ?_⟩
      · change ‖U.symm v‖ = 1
        simpa using (show ‖v‖ = 1 from hv.1)
      · rw [← U.inner_map_map (U.symm v) x, U.apply_symm_apply]
        exact hv.2
      · dsimp only
        rw [← Geometry.score_tensorRotation hN U w (U.symm v), U.apply_symm_apply]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨U v, ⟨?_, ?_⟩, ?_⟩
      · change ‖U v‖ = 1
        simpa using (show ‖v‖ = 1 from hv.1)
      · rw [U.inner_map_map]
        exact hv.2
      · dsimp only
        rw [Geometry.score_tensorRotation hN U w v]
  exact congrArg sSup he

/-- Fixed-direction constrained Gaussian means agree for all unit planted
vectors; in particular the center does not depend on the realized signal. -/
theorem constrainedMaximum_mean_eq_of_unit {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    (x v : Model.Vector N) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1)
    (m : ℝ) (hm : |m| ≤ 1) :
    (∫ w, Model.constrainedMaximum lam x w m ∂Model.noiseLaw N k) =
      ∫ w, Model.constrainedMaximum lam v w m ∂Model.noiseLaw N k := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  let U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := (ℝ ∙ (x-v))ᗮ.reflection
  have hu : U x = v := Submodule.reflection_sub (hx.trans hv.symm)
  let T := Geometry.tensorRotation (k := k) hNpos U
  have hshift (w : Model.Tensor N k) : Model.constrainedMaximum lam v (T w) m =
      Model.constrainedMaximum lam x w m := by
    rw [← hu]
    exact constrainedMaximum_tensorRotation hNpos lam U x w m
  have hmap : (Model.noiseLaw N k).map T = Model.noiseLaw N k := stdGaussian_map T
  have hF : Continuous (fun w : Model.Tensor N k ↦ Model.constrainedMaximum lam v w m) :=
    (Geometry.constrainedMaximum_lipschitz hN lam v hv m hm).continuous
  have hi := integral_map (μ := Model.noiseLaw N k) T.continuous.measurable.aemeasurable
    hF.aestronglyMeasurable
  rw [hmap] at hi
  calc
    _ = ∫ w, Model.constrainedMaximum lam v (T w) m ∂Model.noiseLaw N k := by
      apply integral_congr_ae
      filter_upwards [] with w
      exact (hshift w).symm
    _ = _ := hi.symm

/-- Explicit finite-coordinate meaning of the induced tensor rotation. -/
theorem tensorRotation_apply {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (w : Model.Tensor N k)
    (q : Fin k → Fin N) :
    Geometry.tensorRotation hN U w q = ∑ i : Fin k → Fin N,
      w i * ∏ r, U ((EuclideanSpace.basisFun (Fin N) ℝ) (i r)) (q r) := by
  have hb (i : Fin k → Fin N) : Geometry.rotatedTensorBasis (k := k) hN U i =
      Geometry.productTensor (fun r ↦ U ((EuclideanSpace.basisFun (Fin N) ℝ) (i r))) := by
    simp [Geometry.rotatedTensorBasis, Module.Basis.coe_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
  have hs := (Geometry.rotatedTensorBasis (k := k) hN U).sum_repr_symm w
  change ((Geometry.rotatedTensorBasis (k := k) hN U).repr.symm w) q = _
  rw [← hs]
  change (PiLp.projₗ (p := 2) (𝕜 := ℝ) (fun _ : Fin k → Fin N ↦ ℝ) q)
    (∑ i, w i • Geometry.rotatedTensorBasis hN U i) = _
  rw [map_sum]
  simp only [map_smul, PiLp.projₗ_apply, hb, smul_eq_mul]
  rfl

/-- Rational coordinate formula for reflection, with the total zero-normal
convention already supplied by Mathlib's actual reflection definition. -/
theorem reflection_coordinate {N : ℕ} (d e : Model.Vector N) (q : Fin N) :
    ((ℝ ∙ d)ᗮ.reflection) e q = -(2*(inner ℝ d e/‖d‖^2)*d q-e q) := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [smul_eq_mul, mul_assoc]

private theorem measurable_reflection_coordinate {N k : ℕ}
    (v : Model.Vector N) (i q : Fin N) :
    Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      ((ℝ ∙ (z.1-v))ᗮ.reflection) ((EuclideanSpace.basisFun (Fin N) ℝ) i) q) := by
  simp_rw [reflection_coordinate]
  have hd : Continuous (fun z : Model.Vector N × Model.Tensor N k ↦ z.1-v) :=
    continuous_fst.sub continuous_const
  have ha : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
      inner ℝ (z.1-v) ((EuclideanSpace.basisFun (Fin N) ℝ) i)/‖z.1-v‖^2) :=
    (hd.inner continuous_const).measurable.div (hd.norm.measurable.pow_const 2)
  have hq : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦ (z.1-v) q) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) q).comp hd).measurable
  exact (((measurable_const.mul ha).mul hq).sub measurable_const).neg

/-- The noise tensor transported by the Householder reflection from the realized
signal toward a fixed reference unit direction. It is defined for every input. -/
noncomputable def reflectedNoise {N k : ℕ} (hN : 0 < N) (v : Model.Vector N)
    (z : Model.Vector N × Model.Tensor N k) : Model.Tensor N k :=
  Geometry.tensorRotation hN ((ℝ ∙ (z.1-v))ᗮ.reflection) z.2

/-- The full parameterized reflected-noise tensor is Borel measurable. -/
theorem measurable_reflectedNoise {N k : ℕ} (hN : 0 < N) (v : Model.Vector N) :
    Measurable (reflectedNoise (k := k) hN v) := by
  have heq : reflectedNoise (k := k) hN v = fun z ↦ WithLp.toLp 2
      (fun q : Fin k → Fin N ↦ ∑ i : Fin k → Fin N,
        z.2 i * ∏ r, ((ℝ ∙ (z.1-v))ᗮ.reflection)
          ((EuclideanSpace.basisFun (Fin N) ℝ) (i r)) (q r)) := by
    funext z
    ext q
    exact tensorRotation_apply hN _ z.2 q
  rw [heq]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin k → Fin N ↦ ℝ)).measurable.comp
  apply Measurable.of_eval
  intro q
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.mul
  · exact (PiLp.continuous_apply 2 (fun _ : Fin k → Fin N ↦ ℝ) i).measurable.comp measurable_snd
  · apply Finset.measurable_fun_prod
    intro r _
    exact measurable_reflection_coordinate v (i r) (q r)

/-- The transported Gaussian tensor has exactly the original tensor norm,
pointwise even away from the prior-supported unit sphere. -/
theorem norm_reflectedNoise {N k : ℕ} (hN : 0 < N) (v : Model.Vector N)
    (z : Model.Vector N × Model.Tensor N k) : ‖reflectedNoise hN v z‖ = ‖z.2‖ :=
  (Geometry.tensorRotation hN ((ℝ ∙ (z.1-v))ᗮ.reflection)).norm_map z.2

/-- Every finite moment of the parameterized reflected noise exists. -/
theorem reflectedNoise_memLp {N k : ℕ} (hN : 0 < N) (v : Model.Vector N)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (reflectedNoise (k := k) hN v) p (Model.experimentLaw N k) := by
  have hw : MemLp (fun z : Model.Vector N × Model.Tensor N k ↦ z.2) p
      (Model.experimentLaw N k) :=
    (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) p hp).comp_measurePreserving
      (measurePreserving_snd (μ := Model.spherePrior N) (ν := Model.noiseLaw N k))
  exact hw.of_le (measurable_reflectedNoise hN v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z ↦ (norm_reflectedNoise hN v z).le))

/-- The actual constrained maximum with the random planted signal has every
finite moment. Only a.e equality with its Borel Householder version is used. -/
theorem constrainedMaximum_experiment_memLp {N k : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (m : ℝ) (hm : |m| ≤ 1) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun z : Model.Vector N × Model.Tensor N k ↦ Model.constrainedMaximum lam z.1 z.2 m)
      p (Model.experimentLaw N k) := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  let i : Fin N := ⟨0, hNpos⟩
  let v : Model.Vector N := (EuclideanSpace.basisFun (Fin N) ℝ) i
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one i
  let F : Model.Tensor N k → ℝ := fun w ↦ Model.constrainedMaximum lam v w m
  let G : Model.Tensor N k → ℝ := fun w ↦ F w-F 0
  have hLip := Geometry.constrainedMaximum_lipschitz (k := k) hN lam v hv m hm
  have hG : LipschitzWith ((Real.sqrt N)⁻¹).toNNReal G := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [G, dist_sub_right] using hLip.dist_le_mul y z
  have hG0 : G 0 = 0 := sub_self _
  have H := hG.comp_memLp hG0 (reflectedNoise_memLp hNpos v p hp)
  have H2 : MemLp (fun z : Model.Vector N × Model.Tensor N k ↦
      (F (reflectedNoise hNpos v z)-F 0)+F 0) p (Model.experimentLaw N k) :=
    H.add (memLp_const (F 0))
  have hT : MemLp (fun z : Model.Vector N × Model.Tensor N k ↦
      Model.constrainedMaximum lam v (reflectedNoise hNpos v z) m) p (Model.experimentLaw N k) := by
    simpa only [sub_add_cancel, F] using H2
  have hs : ∀ᵐ z ∂Model.experimentLaw N k, ‖z.1‖ = 1 :=
    (Measure.quasiMeasurePreserving_fst).ae (Geometry.spherePrior_norm_ae hNpos)
  have heq : (fun z : Model.Vector N × Model.Tensor N k ↦ Model.constrainedMaximum lam z.1 z.2 m) =ᵐ[Model.experimentLaw N k]
      (fun z ↦ Model.constrainedMaximum lam v (reflectedNoise hNpos v z) m) := by
    filter_upwards [hs] with z hz
    let U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := (ℝ ∙ (z.1-v))ᗮ.reflection
    have hu : U z.1 = v := Submodule.reflection_sub (hz.trans hv.symm)
    have hrot := constrainedMaximum_tensorRotation hNpos lam U z.1 z.2 m
    rw [hu] at hrot
    exact hrot.symm
  exact MemLp.ae_eq heq.symm hT

/-- Fubini is justified for the genuine random-signal constrained maximum. -/
theorem constrainedMaximum_experiment_integrable {N k : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (m : ℝ) (hm : |m| ≤ 1) :
    Integrable (fun z : Model.Vector N × Model.Tensor N k ↦ Model.constrainedMaximum lam z.1 z.2 m)
      (Model.experimentLaw N k) :=
  (constrainedMaximum_experiment_memLp hN lam m hm 1 (by norm_num)).integrable le_rfl

/-- The actual annealed constrained center equals its Gaussian center at every
deterministic unit direction. -/
theorem constrainedMaximum_experiment_mean {N k : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (m : ℝ) (hm : |m| ≤ 1) (v : Model.Vector N) (hv : ‖v‖ = 1) :
    (∫ z : Model.Vector N × Model.Tensor N k,
      Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw N k) =
      ∫ w, Model.constrainedMaximum lam v w m ∂Model.noiseLaw N k := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  change (∫ z : Model.Vector N × Model.Tensor N k,
    Model.constrainedMaximum lam z.1 z.2 m
      ∂(Model.spherePrior N).prod (Model.noiseLaw N k)) = _
  rw [integral_prod _ (constrainedMaximum_experiment_integrable hN lam m hm)]
  calc
    _ = ∫ _x : Model.Vector N,
        (∫ w, Model.constrainedMaximum lam v w m ∂Model.noiseLaw N k) ∂Model.spherePrior N := by
      apply integral_congr_ae
      filter_upwards [Geometry.spherePrior_norm_ae hNpos] with x hx
      exact constrainedMaximum_mean_eq_of_unit hN lam x v hx hv m hm
    _ = _ := by simp

/-- Exact Gaussian tails for actual random-signal constrained maxima, centered
at the actual annealed mean. The event is null measurable under the experiment. -/
theorem constrainedMaximum_experiment_gaussian_tail {N k : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (m : ℝ) (hm : |m| ≤ 1) (t : ℝ) (ht : 0 < t) :
    Model.experimentLaw N k {z | |Model.constrainedMaximum lam z.1 z.2 m -
      ∫ u : Model.Vector N × Model.Tensor N k,
        Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw N k| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-(N : ℝ)*t^2/2)) := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  have hF : AEMeasurable (fun z : Model.Vector N × Model.Tensor N k ↦
      Model.constrainedMaximum lam z.1 z.2 m) (Model.experimentLaw N k) :=
    (constrainedMaximum_experiment_memLp hN lam m hm 2 (by norm_num)).aemeasurable
  have hset : NullMeasurableSet {z : Model.Vector N × Model.Tensor N k |
      |Model.constrainedMaximum lam z.1 z.2 m - ∫ u : Model.Vector N × Model.Tensor N k,
        Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw N k| > t}
      (Model.experimentLaw N k) :=
    (continuous_abs.measurable.comp_aemeasurable (hF.sub aemeasurable_const)).nullMeasurable
      measurableSet_Ioi
  change ((Model.spherePrior N).prod (Model.noiseLaw N k)) _ ≤ _
  rw [Measure.prod_apply₀ hset]
  calc
    _ ≤ ∫⁻ _x : Model.Vector N,
        ENNReal.ofReal (2 * Real.exp (-(N : ℝ)*t^2/2)) ∂Model.spherePrior N := by
      apply lintegral_mono_ae
      filter_upwards [Geometry.spherePrior_norm_ae hNpos] with x hx
      change Model.noiseLaw N k {w | |Model.constrainedMaximum lam x w m -
        ∫ u : Model.Vector N × Model.Tensor N k,
          Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw N k| > t} ≤ _
      rw [constrainedMaximum_experiment_mean hN lam m hm x hx]
      exact Geometry.constrainedMaximum_gaussian_tail hN lam x hx m hm t ht
    _ = _ := by simp

/-- Gaussian maximum tail bounds are summable along any fixed nonnegative
dimension offset. -/
theorem gaussian_tail_tsum_ne_top (offset : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, ENNReal.ofReal (2*Real.exp (-((n+offset : ℕ) : ℝ)*t^2/2))) ≠ ∞ := by
  have hc : -(t^2)/2 < 0 := by nlinarith [sq_pos_of_pos ht]
  have hg := Real.summable_exp_nat_mul_of_ge (c := -(t^2)/2) hc
    (f := fun n : ℕ ↦ (n : ℝ)+(offset : ℝ))
    (fun n ↦ le_add_of_nonneg_right (Nat.cast_nonneg offset))
  have hs : Summable (fun n : ℕ ↦ 2*Real.exp (-((n+offset : ℕ) : ℝ)*t^2/2)) := by
    apply (hg.mul_left 2).congr
    intro n
    congr 1
    congr 1
    push_cast
    ring
  exact hs.tsum_ofReal_ne_top

/-- The actual centered maximum has summable tails under every coupling of
physical experiments. No independence between dimensions is required. -/
theorem centeredMaximum_summable_tails {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : Statements.PhysicalSequence k Ω μ) (lam eps : ℝ) (heps : 0 < eps) :
    (∑' n : ℕ, μ {ω | eps ≤ |Statements.sampleMaximum E lam n ω -
      Model.expectedMaximum (n+1) k lam|}) ≠ ∞ := by
  apply ne_top_of_le_ne_top (gaussian_tail_tsum_ne_top 1 (eps/2) (half_pos heps))
  apply ENNReal.tsum_le_tsum
  intro n
  have hF : Measurable (fun z : Model.Vector (n+1) × Model.Tensor (n+1) k ↦
      |Model.normalizedMaximum (Model.observation lam z)-Model.expectedMaximum (n+1) k lam|) :=
    continuous_abs.measurable.comp
      (((Geometry.normalizedMaximum_lipschitz (Nat.succ_pos n)).continuous.measurable.comp
        (Model.measurable_observation (n+1) k lam)).sub measurable_const)
  have hset : MeasurableSet {z : Model.Vector (n+1) × Model.Tensor (n+1) k |
      eps/2 < |Model.normalizedMaximum (Model.observation lam z)-Model.expectedMaximum (n+1) k lam|} :=
    measurableSet_lt measurable_const hF
  calc
    _ ≤ μ ((E.sample n) ⁻¹' {z | eps/2 < |Model.normalizedMaximum (Model.observation lam z)-
        Model.expectedMaximum (n+1) k lam|}) := by
      apply measure_mono
      intro ω hω
      exact (half_lt_self heps).trans_le hω
    _ = Model.experimentLaw (n+1) k {z | eps/2 <
        |Model.normalizedMaximum (Model.observation lam z)-Model.expectedMaximum (n+1) k lam|} := by
      rw [← E.law n, Measure.map_apply (E.measurable n) hset]
    _ ≤ _ := plantedMaximum_gaussian_tail (Nat.succ_pos n) lam (eps/2) (half_pos heps)

/-- Gaussian fluctuations of the actual planted maximum vanish almost surely
under arbitrary cross-dimension couplings, for each fixed strength. -/
theorem sampleMaximum_centered_ae {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : Statements.PhysicalSequence k Ω μ) (lam : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleMaximum E lam n ω -
      Model.expectedMaximum (n+1) k lam) atTop (𝓝 0) := by
  have h := LimitTools.ae_tendsto_zero_of_summable_tails μ
    (fun n ω ↦ |Statements.sampleMaximum E lam n ω-Model.expectedMaximum (n+1) k lam|)
    (fun _ _ ↦ abs_nonneg _) (centeredMaximum_summable_tails E lam)
  exact h.mono (fun _ hω ↦ tendsto_zero_iff_norm_tendsto_zero.mpr hω)

/-- Centered constrained maxima have summable tails in the paper's dimensions
n+2, under every coupling of physical experiments. Null measurability, rather
than an assumed global Borel property of the constrained maximum, suffices. -/
theorem centeredConstrainedMaximum_summable_tails {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : Statements.PhysicalSequence k Ω μ)
    (lam m : ℝ) (hm : |m| ≤ 1) (eps : ℝ) (heps : 0 < eps) :
    (∑' n : ℕ, μ {ω | eps ≤ |Model.constrainedMaximum lam
      (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m -
      ∫ z : Model.Vector (n+2) × Model.Tensor (n+2) k,
        Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (n+2) k|}) ≠ ∞ := by
  apply ne_top_of_le_ne_top (gaussian_tail_tsum_ne_top 2 (eps/2) (half_pos heps))
  apply ENNReal.tsum_le_tsum
  intro n
  have hN : 2 ≤ n+2 := Nat.le_add_left 2 n
  have hF : AEMeasurable (fun z : Model.Vector (n+2) × Model.Tensor (n+2) k ↦
      Model.constrainedMaximum lam z.1 z.2 m) (Model.experimentLaw (n+2) k) :=
    (constrainedMaximum_experiment_memLp hN lam m hm 2 (by norm_num)).aemeasurable
  have hset : NullMeasurableSet {z : Model.Vector (n+2) × Model.Tensor (n+2) k |
      eps/2 < |Model.constrainedMaximum lam z.1 z.2 m -
        ∫ u : Model.Vector (n+2) × Model.Tensor (n+2) k,
          Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw (n+2) k|}
      (Model.experimentLaw (n+2) k) :=
    (continuous_abs.measurable.comp_aemeasurable (hF.sub aemeasurable_const)).nullMeasurable
      measurableSet_Ioi
  have hsetmap : NullMeasurableSet {z : Model.Vector (n+2) × Model.Tensor (n+2) k |
      eps/2 < |Model.constrainedMaximum lam z.1 z.2 m -
        ∫ u : Model.Vector (n+2) × Model.Tensor (n+2) k,
          Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw (n+2) k|}
      (μ.map (E.sample (n+1))) := by
    rw [E.law (n+1)]
    exact hset
  calc
    _ ≤ μ ((E.sample (n+1)) ⁻¹' {z | eps/2 < |Model.constrainedMaximum lam z.1 z.2 m -
        ∫ u : Model.Vector (n+2) × Model.Tensor (n+2) k,
          Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw (n+2) k|}) := by
      apply measure_mono
      intro ω hω
      exact (half_lt_self heps).trans_le hω
    _ = Model.experimentLaw (n+2) k {z | eps/2 < |Model.constrainedMaximum lam z.1 z.2 m -
        ∫ u : Model.Vector (n+2) × Model.Tensor (n+2) k,
          Model.constrainedMaximum lam u.1 u.2 m ∂Model.experimentLaw (n+2) k|} := by
      have hmap := Measure.map_apply₀ (E.measurable (n+1)).aemeasurable hsetmap
      rw [E.law (n+1)] at hmap
      exact hmap.symm
    _ ≤ _ := constrainedMaximum_experiment_gaussian_tail hN lam m hm (eps/2) (half_pos heps)

/-- Actual constrained Gaussian fluctuations vanish almost surely, for each
fixed strength and overlap, under arbitrary cross-dimension coupling. -/
theorem sampleConstrainedMaximum_centered_ae {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : Statements.PhysicalSequence k Ω μ)
    (lam m : ℝ) (hm : |m| ≤ 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Model.constrainedMaximum lam
      (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m -
      ∫ z : Model.Vector (n+2) × Model.Tensor (n+2) k,
        Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (n+2) k) atTop (𝓝 0) := by
  have h := LimitTools.ae_tendsto_zero_of_summable_tails μ
    (fun n ω ↦ |Model.constrainedMaximum lam (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m -
      ∫ z : Model.Vector (n+2) × Model.Tensor (n+2) k,
        Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (n+2) k|)
    (fun _ _ ↦ abs_nonneg _) (centeredConstrainedMaximum_summable_tails E lam m hm)
  exact h.mono (fun _ hω ↦ tendsto_zero_iff_norm_tendsto_zero.mpr hω)

end TensorPCA.MaximumProofs
