-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GroundState
public import TensorPCA.ScalarReduction
public import TensorPCA.Statements
public import TensorPCA.Statistical
public import TensorPCA.LimitTools
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith

/-! Reductions with explicit intermediate mathematical premises.
Unconditional principal theorems are exported in Paper.
The intermediate functions are the experiment's means, fluctuations,
log-likelihood moments, finite-channel derivatives and variational profiles. -/
@[expose] public section
namespace TensorPCA.Reduction
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology RealInnerProductSpace ENNReal
universe u v

/-- A deterministic mean limit plus centered sample fluctuations gives the
actual almost-sure maximum limit, without cross-dimension independence. -/
theorem maximum_at {k : ℕ} {lam : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : Statements.PhysicalSequence k Ω μ)
    (hmean : Tendsto (fun n ↦ Model.expectedMaximum (n+1) k lam) atTop
      (𝓝 (Scalar.mleValue k lam)))
    (hfluct : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleMaximum E lam n ω -
      Model.expectedMaximum (n+1) k lam) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleMaximum E lam n ω)
      atTop (𝓝 (Scalar.mleValue k lam)) :=
  hfluct.mono (fun _ h ↦ LimitTools.tendsto_of_vanishing_error h hmean)

/-- Both detection branches from concrete analytic likelihood obligations. -/
theorem detection
    (hsub : ∀ k : ℕ, 6 ≤ k → Even k → ∀ lam : ℝ, 0 ≤ lam → lam < Scalar.lambdaC k →
      Statistical.FiniteTVMomentBound k lam ∧ Statistical.NullLogSecondMomentLimit k lam)
    (hsuper : ∀ k : ℕ, 6 ≤ k → Even k → ∀ lam : ℝ, 0 ≤ lam → Scalar.lambdaC k < lam →
      ∃ C : ℝ, Statistical.FiniteTVVarianceBound k lam C ∧
        Statistical.NullNormalizedLogVarianceLimit k lam) : Statements.Detection := by
  intro k hk heven lam hlam
  constructor
  · intro hlt
    obtain ⟨hb, hm⟩ := hsub k hk heven lam hlam hlt
    exact Statistical.testingDistance_tendsto_zero_of_logSecondMoment hb hm
  · intro hgt
    obtain ⟨C, hb, hv⟩ := hsuper k hk heven lam hlam hgt
    exact Statistical.testingDistance_tendsto_one_of_logVariance hb hv

/-- Tensor-MMSE consequence of finite-channel I-MMSE and Bayesian derivative limits.
Proposition 5.8 in arXiv v2; Proposition 5.9 in the local revision. -/
theorem tensorMMSE
    (hchannel : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
      Statistical.FiniteIMMSE k lam)
    (hbayes : ∀ k : ℕ, 3 ≤ k → ∀ lam : ℝ, 0 < lam → lam ≠ Scalar.lambdaC k →
      Statistical.BayesianDerivativeLimit k lam) : Statements.TensorMMSE := by
  intro k hk lam hlam hne
  exact Statistical.tensorMMSE_tendsto_of_derivative_values
    (hchannel k hk lam hlam hne) (hbayes k hk lam hlam hne)

/-- A true finite-parameter minimizer plus admissibility of every family member
identifies the two genuine infima. No infimum equality is assumed. -/
theorem fourParameter_of_minimizer {k : ℕ} {m : ℝ}
    (hmin : Scalar.FourParameterMinimizer k m)
    (hfamily : ∀ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q →
      Scalar.AdmissibleProfile (Scalar.fourParameterProfile delta a b q)) :
    Scalar.FourParameterReduction k m := by
  obtain ⟨delta, a, b, q, hparam, hadm, hleast⟩ := hmin
  let v := Scalar.parisiFunctional (Scalar.xiSlice k m) 0
    (Scalar.fourParameterProfile delta a b q)
  have hfull : IsLeast {w : ℝ | ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧
      w = Scalar.parisiFunctional (Scalar.xiSlice k m) 0 p} v := by
    refine ⟨⟨_, hadm, rfl⟩, ?_⟩
    rintro w ⟨p, hp, rfl⟩
    exact hleast p hp
  have hsmall : IsLeast {w : ℝ | ∃ delta a b q : ℝ,
      Scalar.FourParameterAdmissible delta a b q ∧ w =
      Scalar.parisiFunctional (Scalar.xiSlice k m) 0
        (Scalar.fourParameterProfile delta a b q)} v := by
    refine ⟨⟨delta, a, b, q, hparam, rfl⟩, ?_⟩
    rintro w ⟨d, a, b, q, hp, rfl⟩
    exact hleast _ (hfamily d a b q hp)
  unfold Scalar.FourParameterReduction Scalar.variationalValue Scalar.fourParameterValue
  rw [hfull.csInf_eq, hsmall.csInf_eq]

/-- RS evaluation and an actual structural minimizer imply both variational
conclusions. The functional and both infima retain their full meanings. -/
theorem variational
    (hrs : ∀ k : ℕ, 3 ≤ k → Scalar.RSVariationalLaw k)
    (hmin : ∀ k : ℕ, 3 ≤ k → ∀ m : ℝ, |m| < 1 → Scalar.FourParameterMinimizer k m)
    (hfamily : ∀ delta a b q : ℝ, Scalar.FourParameterAdmissible delta a b q →
      Scalar.AdmissibleProfile (Scalar.fourParameterProfile delta a b q)) :
    Statements.VariationalConclusions := by
  intro k hk
  constructor
  · intro lam _ m hm hlarge
    unfold Scalar.energy Scalar.rsEnergy
    rw [hrs k hk m hm hlarge]
  · intro m hm
    exact fourParameter_of_minimizer (hmin k hk m hm) hfamily

/-- Gaussian slice decomposition and a genuine finite-mixture ground-state
limit imply the canonical expected slice limit. -/
theorem constrained_mean_at {k : ℕ} {lam m : ℝ}
    (hground : GroundState.SliceGroundLimit k m)
    (hslice : GroundState.SliceDecomposition k lam m) :
    Tendsto (fun n ↦ ∫ z, Model.constrainedMaximum lam z.1 z.2 m
      ∂Model.experimentLaw (n+2) k) atTop (𝓝 (Scalar.energy k lam m)) := by
  apply LimitTools.tendsto_of_vanishing_error hslice
  exact tendsto_const_nhds.add hground

/-- The expected limit is derived, not assumed as the constrained principal
conclusion. Centered fluctuations supply its almost-sure counterpart. -/
theorem constrained_at {k : ℕ} {lam m : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : Statements.PhysicalSequence k Ω μ)
    (hground : GroundState.SliceGroundLimit k m)
    (hslice : GroundState.SliceDecomposition k lam m)
    (hfluct : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Model.constrainedMaximum lam
      (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m -
      ∫ z, Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (n+2) k)
      atTop (𝓝 0)) :
    (Tendsto (fun n ↦ ∫ z, Model.constrainedMaximum lam z.1 z.2 m
      ∂Model.experimentLaw (n+2) k) atTop (𝓝 (Scalar.energy k lam m))) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ Model.constrainedMaximum lam
      (E.sample (n+1) ω).1 (E.sample (n+1) ω).2 m)
      atTop (𝓝 (Scalar.energy k lam m))) := by
  have hm := constrained_mean_at hground hslice
  exact ⟨hm, hfluct.mono (fun _ h ↦ LimitTools.tendsto_of_vanishing_error h hm)⟩

/-- Globality is logical glue from upper comparison, the pure baseline,
critical/supercritical matching, and strict subcritical branch separation. -/
theorem landscape_global_at {k : ℕ} {lam : ℝ}
    (hupper : ∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤ Scalar.mleValue k lam)
    (hzero : Scalar.energy k lam 0 = Scalar.gs k)
    (hmatch : Scalar.lambdaC k ≤ lam → Scalar.mleValue k lam =
      Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)))
    (hbelow : lam < Scalar.lambdaC k →
      Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) < Scalar.gs k) :
    ((∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤
      Scalar.energy k lam (Real.sqrt (Scalar.qS k lam))) ↔ Scalar.lambdaC k ≤ lam) := by
  constructor
  · intro h
    by_contra hn
    have hg := h 0 (by constructor <;> norm_num)
    rw [hzero] at hg
    exact (not_lt_of_ge hg) (hbelow (lt_of_not_ge hn))
  · intro h m hm
    rw [← hmatch h]
    exact hupper m hm

/-- Zero is global throughout the full subcritical/critical physical range. -/
theorem zero_global_at {k : ℕ} {lam : ℝ} (hlam : lam ≤ Scalar.lambdaC k)
    (hupper : ∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤ Scalar.mleValue k lam)
    (hzero : Scalar.energy k lam 0 = Scalar.gs k) :
    ∀ m ∈ Icc (-1 : ℝ) 1, Scalar.energy k lam m ≤ Scalar.energy k lam 0 := by
  intro m hm
  rw [hzero]
  simpa only [Scalar.mleValue, if_pos hlam] using hupper m hm

/-- Finite posterior/validation-channel bounds provide actual upper envelopes.
The odd-order sign error and zero-signal estimates belong to these finite
bounds, not to a restatement of the final limsup. -/
theorem estimator_bounds_at {k : ℕ} {lam : ℝ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] (ν : ∀ n, Measure (A n))
    (est : ∀ n, Model.Estimator (n+1) k (A n))
    (hlowerK : ∀ n, 0 ≤ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k)
    (hlowerOne : ∀ n, 0 ≤ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) 1)
    (hK : ∀ eps : ℝ, 0 < eps → ∃ g : ℕ → ℝ,
      (∀ᶠ n in atTop, Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k ≤ g n) ∧
      Tendsto g atTop (𝓝 ((Real.sqrt (Scalar.qStar k lam)) ^ k + eps)))
    (hOne : ∀ eps : ℝ, 0 < eps → ∃ g : ℕ → ℝ,
      (∀ᶠ n in atTop, Model.expectedOverlapPower (n+1) k lam (est n) (ν n) 1 ≤ g n) ∧
      Tendsto g atTop (𝓝 (Real.sqrt (Scalar.qStar k lam) + eps))) :
    Filter.limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k)
      atTop ≤ (Real.sqrt (Scalar.qStar k lam)) ^ k ∧
    Filter.limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) 1)
      atTop ≤ Real.sqrt (Scalar.qStar k lam) :=
  ⟨LimitTools.limsup_le_of_eventual_upper_envelopes hlowerK hK,
    LimitTools.limsup_le_of_eventual_upper_envelopes hlowerOne hOne⟩

/-- The derivative limit used by I-MMSE follows from actual Bayesian value
limits at a countable set of positive strengths and the finite convex secants.
No MMSE convergence or derivative convergence is assumed. -/
theorem bayesian_derivative_at {k : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hvalues : ∀ gamma : ℝ, 0 < gamma →
      Tendsto (fun n ↦ Statistical.sphericalBayesFreeEnergy (n+1) k gamma)
        atTop (𝓝 (Statistical.bayesianLimit k gamma)))
    (hsecants : ∀ j : ℕ, ∀ᶠ n in atTop,
      (Statistical.sphericalBayesFreeEnergy (n+1) k (lam^2) -
        Statistical.sphericalBayesFreeEnergy (n+1) k
          (lam^2-LimitTools.secantStep (lam^2) j)) / LimitTools.secantStep (lam^2) j ≤
          deriv (Statistical.sphericalBayesFreeEnergy (n+1) k) (lam^2) ∧
      deriv (Statistical.sphericalBayesFreeEnergy (n+1) k) (lam^2) ≤
        (Statistical.sphericalBayesFreeEnergy (n+1) k
          (lam^2+LimitTools.secantStep (lam^2) j) -
            Statistical.sphericalBayesFreeEnergy (n+1) k (lam^2)) /
              LimitTools.secantStep (lam^2) j)
    (hscalar : HasDerivAt (Statistical.bayesianLimit k)
      ((1/2 : ℝ)*Scalar.qStar k lam^k) (lam^2)) :
    Statistical.BayesianDerivativeLimit k lam := by
  have ha : 0 < lam^2 := sq_pos_of_pos hlam
  apply LimitTools.secantDerivativeStability _ _ _ _ _ ha (hvalues _ ha)
  · intro j
    apply hvalues
    have hd : (1 : ℝ) < (j : ℝ)+2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    have hlt : LimitTools.secantStep (lam^2) j < lam^2 := div_lt_self ha hd
    exact sub_pos.mpr hlt
  · intro j
    apply hvalues
    exact add_pos ha (div_pos ha (by positivity))
  · exact hsecants
  · exact hscalar

/-- Actual posterior-risk envelopes and finite validation inequalities give
both estimator limsup bounds. This specializes the generic envelope lemma to
explicit MMSE functions; no estimator asymptotic is a premise. -/
theorem estimator_of_finite_bounds {k : ℕ} {lam : ℝ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] (ν : ∀ n, Measure (A n))
    (est : ∀ n, Model.Estimator (n+1) k (A n))
    (hfinite : Statistical.FiniteEstimatorBounds k lam ν est)
    (hcontrol : Statistical.ValidationEnvelopeControl k lam) :
    Filter.limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) k)
      atTop ≤ (Real.sqrt (Scalar.qStar k lam))^k ∧
    Filter.limsup (fun n ↦ Model.expectedOverlapPower (n+1) k lam (est n) (ν n) 1)
      atTop ≤ Real.sqrt (Scalar.qStar k lam) := by
  apply estimator_bounds_at ν est
  · intro n
    exact integral_nonneg (fun _ ↦ pow_nonneg (abs_nonneg _) _)
  · intro n
    exact integral_nonneg (fun _ ↦ pow_nonneg (abs_nonneg _) _)
  · intro eps heps
    obtain ⟨delta, a, b, hd, hne, ha, hla, hb, hlb⟩ := hcontrol eps heps
    refine ⟨fun n ↦ Statistical.validationEnvelope (n+1) k lam delta +
      ((Real.sqrt (Scalar.qStar k lam))^k+eps-a), ?_, ?_⟩
    · exact Eventually.of_forall (fun n ↦ (hfinite delta hd hne n).1.trans
        (le_add_of_nonneg_right (sub_nonneg.mpr hla)))
    · simpa only [add_sub_cancel] using ha.add_const
        ((Real.sqrt (Scalar.qStar k lam))^k+eps-a)
  · intro eps heps
    obtain ⟨delta, a, b, hd, hne, ha, hla, hb, hlb⟩ := hcontrol eps heps
    refine ⟨fun n ↦ Statistical.validationRootEnvelope (n+1) k lam delta +
      (Real.sqrt (Scalar.qStar k lam)+eps-b), ?_, ?_⟩
    · exact Eventually.of_forall (fun n ↦ (hfinite delta hd hne n).2.trans
        (le_add_of_nonneg_right (sub_nonneg.mpr hlb)))
    · simpa only [add_sub_cancel] using hb.add_const
        (Real.sqrt (Scalar.qStar k lam)+eps-b)

/-- Finite nearest-limit classification inequalities and mean-square control
of the actual maximum statistic imply finite-strength testing. -/
theorem finite_testing_at {k r : ℕ} (strengths : Fin (r+1) → ℝ)
    (tests : ∀ n : ℕ, Model.Tensor (n+1) k → Fin (r+1))
    (hmeas : ∀ n, Measurable (tests n)) (C : ℝ)
    (hfinite : ∀ i n,
      (Model.observationLaw (n+1) k (strengths i)).real {y | tests n y ≠ i} ≤
        C * Statistical.maximumMeanSquare (n+1) k (strengths i))
    (hms : ∀ i, Tendsto (fun n ↦ Statistical.maximumMeanSquare (n+1) k (strengths i))
      atTop (𝓝 0)) :
    (∀ n, Measurable (tests n)) ∧ ∀ i,
      Tendsto (fun n ↦ (Model.observationLaw (n+1) k (strengths i)).real
        {y | tests n y ≠ i}) atTop (𝓝 0) := by
  refine ⟨hmeas, fun i ↦ ?_⟩
  have hu : Tendsto (fun n ↦ C*Statistical.maximumMeanSquare (n+1) k (strengths i))
      atTop (𝓝 0) := by simpa using (hms i).const_mul C
  exact tendsto_const_nhds.squeeze hu (fun _ ↦ measureReal_nonneg) (hfinite i)

/-- The derivative of the sample maximum is a signed kth overlap. -/
noncomputable def overlapSlope {k : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {E : Statements.PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    (R : Statements.EstimatorCoupling E A ν) (lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (inner ℝ (R.estimator n (Model.observation lam (E.sample n ω))
    (R.auxiliary n ω)) (E.sample n ω).1)^k

/-- Countably many value events and the actual finite envelope secants imply
positive-strength overlap. The generic secant criterion and power inversion
are proved; no overlap convergence is an input. -/
theorem positive_overlap_at {k : ℕ} (hk : 0 < k) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Statements.PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    (R : Statements.EstimatorCoupling E A ν)
    (hvalues : ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ Statements.sampleMaximum E t n ω) atTop (𝓝 (Scalar.mleValue k t)))
    (hsecants : ∀ᵐ ω ∂μ, ∀ j : ℕ, ∀ᶠ n in atTop,
      (Statements.sampleMaximum E lam n ω -
        Statements.sampleMaximum E (lam-LimitTools.secantStep lam j) n ω) /
        LimitTools.secantStep lam j ≤ overlapSlope R lam n ω ∧
      overlapSlope R lam n ω ≤
        (Statements.sampleMaximum E (lam+LimitTools.secantStep lam j) n ω -
          Statements.sampleMaximum E lam n ω) / LimitTools.secantStep lam j)
    (hderiv : Scalar.ValueDerivative k lam) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleOverlap R lam n ω)
      atTop (𝓝 (Real.sqrt (Scalar.qStar k lam))) := by
  have hleft : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      Tendsto (fun n ↦ Statements.sampleMaximum E (lam-LimitTools.secantStep lam j) n ω)
        atTop (𝓝 (Scalar.mleValue k (lam-LimitTools.secantStep lam j))) := by
    apply ae_all_iff.mpr
    intro j
    apply hvalues
    exact sub_pos.mpr (div_lt_self hlam (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]))
  have hright : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      Tendsto (fun n ↦ Statements.sampleMaximum E (lam+LimitTools.secantStep lam j) n ω)
        atTop (𝓝 (Scalar.mleValue k (lam+LimitTools.secantStep lam j))) := by
    apply ae_all_iff.mpr
    intro j
    apply hvalues
    exact add_pos hlam (div_pos hlam (by positivity))
  filter_upwards [hvalues lam hlam, hleft, hright, hsecants] with ω hc hl hr hb
  have hd := LimitTools.secantDerivativeStability
    (fun n t ↦ Statements.sampleMaximum E t n ω) (Scalar.mleValue k)
    (fun n ↦ overlapSlope R lam n ω) lam
    ((Real.sqrt (Scalar.qStar k lam))^k) hlam hc hl hr hb hderiv
  apply LimitTools.nonnegative_power_limit hk
    (fun n ↦ abs_nonneg _) (Real.sqrt_nonneg _) 
  simpa only [overlapSlope, Statements.sampleOverlap, abs_pow,
    abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) k)] using hd.abs

/-- The zero-strength endpoint follows from summable actual overlap tails,
which the spherical fourth moment supplies. No independence across n is used. -/
theorem zero_overlap_at {k : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Statements.PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    (R : Statements.EstimatorCoupling E A ν)
    (htails : ∀ eps : ℝ, 0 < eps →
      (∑' n : ℕ, μ {ω | eps ≤ Statements.sampleOverlap R 0 n ω}) ≠ ∞)
    (hqzero : Scalar.qStar k 0 = 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleOverlap R 0 n ω)
      atTop (𝓝 (Real.sqrt (Scalar.qStar k 0))) := by
  rw [hqzero, Real.sqrt_zero]
  exact LimitTools.ae_tendsto_zero_of_summable_tails μ
    (fun n ω ↦ Statements.sampleOverlap R 0 n ω) (fun _ _ ↦ abs_nonneg _) htails

/-- Expected overlap attainment is bounded convergence plus the actual finite
joint-law transport identity. No expected-overlap limit is assumed. -/
theorem attainment_at {k : ℕ} {lam : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Statements.PhysicalSequence k Ω μ} {A : ℕ → Type v}
    [∀ n, MeasurableSpace (A n)] {ν : ∀ n, Measure (A n)}
    (R : Statements.EstimatorCoupling E A ν)
    (has : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Statements.sampleOverlap R lam n ω)
      atTop (𝓝 (Real.sqrt (Scalar.qStar k lam))))
    (hmeas : ∀ n, AEStronglyMeasurable (Statements.sampleOverlap R lam n) μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Statements.sampleOverlap R lam n ω‖ ≤ 1)
    (htransport : ∀ n, Model.expectedOverlapPower (n+1) k lam
      (R.estimator n) (ν n) 1 = ∫ ω, Statements.sampleOverlap R lam n ω ∂μ) :
    Tendsto (fun n ↦ Model.expectedOverlapPower (n+1) k lam
      (R.estimator n) (ν n) 1) atTop (𝓝 (Real.sqrt (Scalar.qStar k lam))) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
    hmeas (integrable_const 1) hbound has
  simpa only [htransport, integral_const, probReal_univ, one_smul] using h

/-- Strictness comes from genuine continuous-neighborhood and derivative-sign
facts, rather than assuming the strict local maximum itself. -/
theorem landscape_local_at {k : ℕ} {lam : ℝ}
    (hx : Real.sqrt (Scalar.qS k lam) ∈ Icc (-1 : ℝ) 1)
    (hsigns : ∃ eps : ℝ, 0 < eps ∧
      ContinuousOn (Scalar.energy k lam)
        (Icc (Real.sqrt (Scalar.qS k lam)-eps) (Real.sqrt (Scalar.qS k lam)+eps)) ∧
      (∀ x ∈ Ioo (Real.sqrt (Scalar.qS k lam)-eps) (Real.sqrt (Scalar.qS k lam)),
        0 < deriv (Scalar.energy k lam) x) ∧
      (∀ x ∈ Ioo (Real.sqrt (Scalar.qS k lam)) (Real.sqrt (Scalar.qS k lam)+eps),
        deriv (Scalar.energy k lam) x < 0)) :
    Statements.StrictLocalMaximumOn (Scalar.energy k lam) (Real.sqrt (Scalar.qS k lam)) := by
  obtain ⟨eps, heps, hc, hp, hn⟩ := hsigns
  exact ⟨hx, eps, heps, fun y _ hne hy ↦
    LimitTools.strict_local_max_of_deriv_sign_change heps hc hp hn y hne hy⟩

end TensorPCA.Reduction
