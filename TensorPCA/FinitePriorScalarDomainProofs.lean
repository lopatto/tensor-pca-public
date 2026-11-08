-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPosteriorSecondMomentProofs
public import TensorPCA.FinitePriorChannelProofs

/-! # The scalar RS potential beyond the prior second moment -/
@[expose] public section

namespace TensorPCA.FinitePriorScalarDomainProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianBoundedIMMSEProofs GaussianFiberChannelProofs GaussianTensorMomentProofs
open GaussianPosteriorSecondMomentProofs FinitePriorChannelProofs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

noncomputable def scalarSecondMoment (p : Measure S) (a : S → ℝ) : ℝ := ∫ s, a s^2 ∂p

noncomputable def embeddedScalarSignal (a : S → ℝ) (s : S) : Model.Vector 1 :=
  coordinateLine (0 : Fin 1) (a s)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem embeddedScalarSignal_norm (a : S → ℝ) (s : S) : ‖embeddedScalarSignal a s‖ = |a s| := by
  rw [embeddedScalarSignal, (coordinateLine (0 : Fin 1)).norm_map, Real.norm_eq_abs]

theorem embeddedScalar_freeEnergy (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (c : ℝ) :
    mixtureFreeEnergy p (fun s ↦ c • embeddedScalarSignal a s) =
      mixtureFreeEnergy p (fun s ↦ c*a s) := by
  obtain ⟨K,_,hK⟩ := finite_signal_bound (fun s ↦ c*a s)
  have hf2 : MemLp (fun s ↦ c*a s) 2 p :=
    MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable K (.of_forall hK)
  have h := mixtureFreeEnergy_isometricImage p (fun s ↦ c*a s) (measurable_of_finite _) hf2
    (coordinateLine (0 : Fin 1))
  convert h using 1
  congr 1
  funext s
  exact ((coordinateLine (0 : Fin 1)).map_smul c (a s)).symm

theorem continuous_scalarPotential (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (k : ℕ) (gamma : ℝ) : Continuous (scalarPotential p a k gamma) := by
  obtain ⟨K,hK,hAB⟩ := finite_signal_bound (embeddedScalarSignal a)
  have hd (c : ℝ) := hasDerivAt_mixtureFreeEnergy_scale p (embeddedScalarSignal a)
    (measurable_of_finite _) hK (.of_forall hAB) c
  simp_rw [embeddedScalar_freeEnergy] at hd
  have hc : Continuous (fun c ↦ mixtureFreeEnergy p (fun s ↦ c*a s)) :=
    Differentiable.continuous (fun c ↦ (hd c).differentiableAt)
  have hs : Continuous (fun q : ℝ ↦ Real.sqrt ((k:ℝ)*gamma*q^(k-1))) := by fun_prop
  unfold scalarPotential
  exact (hc.comp hs).sub (by fun_prop)

noncomputable def scalarPosteriorSecondMoment (p : Measure S) (a : S → ℝ) (strength : ℝ) : ℝ :=
  ∫ z : S × Model.Vector 1, ‖posteriorMean p
    (fun s ↦ Real.sqrt strength • embeddedScalarSignal a s) (embeddedScalarSignal a)
    (Real.sqrt strength • embeddedScalarSignal a z.1+z.2)‖^2 ∂p.prod (stdGaussian (Model.Vector 1))

theorem scalarPosteriorSecondMoment_le (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (strength : ℝ) :
    scalarPosteriorSecondMoment p a strength ≤ scalarSecondMoment p a := by
  obtain ⟨K,_,hK⟩ := finite_signal_bound (embeddedScalarSignal a)
  have hA2 : MemLp (embeddedScalarSignal a) 2 p :=
    MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable K (.of_forall hK)
  have h := integral_posteriorMean_norm_sq_le p
    (fun s ↦ Real.sqrt strength • embeddedScalarSignal a s) (measurable_of_finite _)
    (embeddedScalarSignal a) (measurable_of_finite _).stronglyMeasurable hA2
  simpa only [scalarPosteriorSecondMoment, embeddedScalarSignal_norm, sq_abs, scalarSecondMoment] using h

theorem scalar_sqrtFreeEnergy_hasDerivAt (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {strength : ℝ} (hs : 0 < strength) :
    HasDerivAt (fun u ↦ mixtureFreeEnergy p (fun s ↦ Real.sqrt u*a s))
      ((1/2:ℝ)*scalarPosteriorSecondMoment p a strength) strength := by
  obtain ⟨K,hK,hAB⟩ := finite_signal_bound (embeddedScalarSignal a)
  have h := hasDerivAt_mixtureFreeEnergy_sqrt p (embeddedScalarSignal a)
    (measurable_of_finite _) hK (.of_forall hAB) hs
  simp_rw [embeddedScalar_freeEnergy] at h
  exact h

theorem scalarPotential_hasDerivAt (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma q : ℝ} (hgamma : 0 < gamma) (hq : 0 < q) :
    HasDerivAt (scalarPotential p a k gamma)
      (((k:ℝ)*((k-1:ℕ):ℝ)*gamma*q^(k-2)/2)*
        (scalarPosteriorSecondMoment p a ((k:ℝ)*gamma*q^(k-1))-q)) q := by
  have hu : 0 < (k:ℝ)*gamma*q^(k-1) := by positivity
  have hd := (scalar_sqrtFreeEnergy_hasDerivAt p a hu).comp q
    ((hasDerivAt_pow (k-1) q).const_mul ((k:ℝ)*gamma))
  have hp := (hasDerivAt_pow k q).const_mul (((k-1:ℕ):ℝ)*gamma/2)
  have h := hd.sub hp
  convert h using 1
  · funext s
    dsimp only [scalarPotential, Function.comp_def, Pi.sub_apply]
    ring
  · have he : k-1-1 = k-2 := by omega
    have hpow : q^(k-1) = q^(k-2)*q := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he,hpow]
    ring

theorem scalarPotential_antitoneOn_above_secondMoment
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    AntitoneOn (scalarPotential p a k gamma) (Set.Ici (scalarSecondMoment p a)) := by
  by_cases hg0 : gamma = 0
  · subst gamma
    intro x _ y _ _
    simp only [scalarPotential, mul_zero, zero_mul, Real.sqrt_zero]
    exact le_rfl
  have hgp : 0 < gamma := lt_of_le_of_ne hgamma (Ne.symm hg0)
  have hrho : 0 ≤ scalarSecondMoment p a := integral_nonneg (fun s ↦ sq_nonneg (a s))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (continuous_scalarPotential p a k gamma).continuousOn
    (f' := fun q ↦ ((k:ℝ)*((k-1:ℕ):ℝ)*gamma*q^(k-2)/2)*
      (scalarPosteriorSecondMoment p a ((k:ℝ)*gamma*q^(k-1))-q))
  · intro q hq
    have hqr : scalarSecondMoment p a < q := by simpa only [interior_Ici, Set.mem_Ioi] using hq
    exact (scalarPotential_hasDerivAt p a hk hgp (lt_of_le_of_lt hrho hqr)).hasDerivWithinAt
  · intro q hq
    have hqr : scalarSecondMoment p a < q := by simpa only [interior_Ici, Set.mem_Ioi] using hq
    have hM := scalarPosteriorSecondMoment_le p a ((k:ℝ)*gamma*q^(k-1))
    have hq0 : 0 ≤ q := hrho.trans hqr.le
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem scalarPotential_le_at_secondMoment
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma q : ℝ} (hgamma : 0 ≤ gamma)
    (hq : scalarSecondMoment p a ≤ q) :
    scalarPotential p a k gamma q ≤ scalarPotential p a k gamma (scalarSecondMoment p a) :=
  scalarPotential_antitoneOn_above_secondMoment p a hk hgamma le_rfl hq hq

theorem exists_global_scalarMaximizer
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    ∃ m ∈ Set.Icc (0:ℝ) (scalarSecondMoment p a),
      ∀ q : ℝ, 0 ≤ q → scalarPotential p a k gamma q ≤ scalarPotential p a k gamma m := by
  have hrho : 0 ≤ scalarSecondMoment p a := integral_nonneg (fun s ↦ sq_nonneg (a s))
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hrho) (continuous_scalarPotential p a k gamma).continuousOn
  refine ⟨m,hm,fun q hq ↦ ?_⟩
  by_cases hqr : q ≤ scalarSecondMoment p a
  · exact hmax ⟨hq,hqr⟩
  · exact (scalarPotential_le_at_secondMoment p a hk hgamma (le_of_not_ge hqr)).trans
      (hmax ⟨hrho,le_rfl⟩)

theorem scalarPotential_sSup_eq_secondMoment
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    sSup (scalarPotential p a k gamma '' Set.Ici (0:ℝ)) =
      sSup (scalarPotential p a k gamma '' Set.Icc (0:ℝ) (scalarSecondMoment p a)) := by
  obtain ⟨m,hm,hmax⟩ := exists_global_scalarMaximizer p a hk hgamma
  have hfull : IsGreatest (scalarPotential p a k gamma '' Set.Ici (0:ℝ)) (scalarPotential p a k gamma m) :=
    ⟨⟨m,hm.1,rfl⟩,by rintro y ⟨q,hq,rfl⟩; exact hmax q hq⟩
  have hcompact : IsGreatest (scalarPotential p a k gamma '' Set.Icc (0:ℝ) (scalarSecondMoment p a))
      (scalarPotential p a k gamma m) :=
    ⟨⟨m,hm,rfl⟩,by rintro y ⟨q,hq,rfl⟩; exact hmax q hq.1⟩
  rw [hfull.isLUB.csSup_eq ⟨_,hfull.1⟩, hcompact.isLUB.csSup_eq ⟨_,hcompact.1⟩]

theorem scalarPotential_sSup_eq_unitInterval
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hrho : scalarSecondMoment p a ≤ 1) :
    sSup (scalarPotential p a k gamma '' Set.Ici (0:ℝ)) =
      sSup (scalarPotential p a k gamma '' Set.Icc (0:ℝ) 1) := by
  obtain ⟨m,hm,hmax⟩ := exists_global_scalarMaximizer p a hk hgamma
  have hfull : IsGreatest (scalarPotential p a k gamma '' Set.Ici (0:ℝ)) (scalarPotential p a k gamma m) :=
    ⟨⟨m,hm.1,rfl⟩,by rintro y ⟨q,hq,rfl⟩; exact hmax q hq⟩
  have hcompact : IsGreatest (scalarPotential p a k gamma '' Set.Icc (0:ℝ) 1)
      (scalarPotential p a k gamma m) :=
    ⟨⟨m,⟨hm.1,hm.2.trans hrho⟩,rfl⟩,by rintro y ⟨q,hq,rfl⟩; exact hmax q hq.1⟩
  rw [hfull.isLUB.csSup_eq ⟨_,hfull.1⟩, hcompact.isLUB.csSup_eq ⟨_,hcompact.1⟩]


end TensorPCA.FinitePriorScalarDomainProofs
