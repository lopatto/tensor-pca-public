-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumExpectedUpperProofs
public import TensorPCA.EnergyBranchProofs

/-! The physical pure maximum has a lower mean bound from Bayesian values and finite planted-maximum derivative integration. No count moment or
physical ground-state baseline is assumed. -/
@[expose] public section
namespace TensorPCA.PureGroundLowerFromBayesianProofs
open MeasureTheory ProbabilityTheory Set Filter
open MaximumDerivativeProofs MaximumIntegralLimitProofs MaximumExpectedUpperProofs
open ScalarStationaryProofs ScalarBranchProofs
open scoped Topology RealInnerProductSpace
noncomputable section

/-- The selected stable branch fills the interval from the turning point to1
and is strictly increasing; hence it tends to1 at large strength. -/
theorem qS_tendsto_one (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (Scalar.qS k) atTop (𝓝 1) := by
  have ht := turningPoint_mem_Ioo k hk
  apply tendsto_order.mpr
  constructor
  · intro c hc
    let q := (max c (turningPoint k)+1)/2
    have hmax : max c (turningPoint k) < 1 := max_lt hc ht.2
    have hq : q ∈ Ioo (turningPoint k) 1 := by
      dsimp only [q]
      constructor <;> linarith [le_max_right c (turningPoint k)]
    have hcq : c < q := by
      dsimp only [q]
      linarith [le_max_left c (turningPoint k)]
    have hImage : q ∈ Scalar.qS k '' Ioi (Scalar.lambdaS k) := by
      rw [image_qS k hk]
      exact hq
    obtain ⟨lam0,hlam0,heq⟩ := hImage
    filter_upwards [eventually_gt_atTop lam0] with lam hlam
    have H := strictMonoOn_qS k hk hlam0 (hlam0.trans hlam) hlam
    rw [heq] at H
    exact hcq.trans H
  · intro c hc
    filter_upwards [eventually_gt_atTop (Scalar.lambdaS k)] with lam hlam
    exact (qS_spec k hk hlam).1.1.2.trans hc

/-- Only an upper approach to the signal strength is needed. The RS energy
representation has signal at most lambda and noise tending to zero. -/
theorem mleValue_sub_strength_eventually_lt (k : ℕ) (hk : 3 ≤ k)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ lam : ℝ in atTop, Scalar.mleValue k lam-lam < eps := by
  have hInside : Tendsto (fun lam : ℝ ↦ (k : ℝ)*(1-Scalar.qS k lam)) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
        (qS_tendsto_one k hk)).const_mul (k : ℝ)
  have hNoise : Tendsto (fun lam : ℝ ↦ Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hInside
  filter_upwards [eventually_gt_atTop (Scalar.lambdaC k),
    hNoise.eventually (Iio_mem_nhds heps)] with lam hlam hsmall
  have hstable := (ScalarStationaryProofs.lambdaS_lt_lambdaC k hk).trans hlam
  have hq := (qS_spec k hk hstable).1.1
  have hq0 : 0 ≤ Scalar.qS k lam := ((turningPoint_mem_Ioo k hk).1.trans hq.1).le
  have hroot := EnergyBranchProofs.sqrt_qS_mem_rsDomain k hk hstable
  have hvalue : Scalar.mleValue k lam =
      lam*(Real.sqrt (Scalar.qS k lam))^k+Real.sqrt ((k : ℝ)*(1-Scalar.qS k lam)) := by
    rw [EnergyBranchProofs.secondaryBranch_matches_mleValue k hk hstable hlam.le,
      EnergyBranchProofs.energy_eq_rsEnergy k hk lam hroot,Scalar.rsEnergy,Real.sq_sqrt hq0]
  have hpow : (Real.sqrt (Scalar.qS k lam))^k ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr hq.2.le)
  have hlam0 := (ScalarStaticRatioProofs.lambdaC_pos k hk).trans hlam
  have hSignal := mul_le_mul_of_nonneg_left hpow hlam0.le
  rw [hvalue]
  linarith

/-- Testing the true unit planted direction in the actual finite supremum
gives this lower bound, without any noise maximum limit. -/
theorem strength_le_expectedMaximum {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    lam ≤ Model.expectedMaximum N k lam := by
  obtain ⟨v,hv⟩ := Geometry.unitSphere_nonempty hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hnorm : ‖Model.feature k v‖ = 1 := Geometry.feature_unit_norm v hv
  have hself : inner ℝ (Model.feature k v) (Model.feature k v) = 1 := by
    rw [real_inner_self_eq_norm_sq,hnorm]
    norm_num
  have hinner : Integrable (fun w : Model.Tensor N k ↦ inner ℝ (Model.feature k v) w)
      (Model.noiseLaw N k) :=
    ((IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) 2 (by norm_num)).const_inner
      (Model.feature k v)).integrable one_le_two
  have hmean : (∫ w : Model.Tensor N k, inner ℝ (Model.feature k v) w ∂Model.noiseLaw N k) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ (Model.feature k v))
  have hLower (w : Model.Tensor N k) :
      lam+inner ℝ (Model.feature k v) w/Real.sqrt N ≤
        Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v+w) := by
    unfold Model.normalizedMaximum
    apply (le_div_iff₀ hs).mpr
    calc
      _ = lam*Real.sqrt N+inner ℝ (Model.feature k v) w := by field_simp [hs.ne']
      _ = Model.score ((lam*Real.sqrt N) • Model.feature k v+w) v := by
        rw [Model.score,inner_add_right,inner_smul_right,hself,mul_one]
      _ ≤ _ := le_csSup (Geometry.score_image_bddAbove _) ⟨v,hv,rfl⟩
  have hInt : Integrable (fun w : Model.Tensor N k ↦ lam+inner ℝ (Model.feature k v) w/Real.sqrt N)
      (Model.noiseLaw N k) := (integrable_const lam).add (hinner.div_const _)
  have hEq : (∫ w : Model.Tensor N k, lam+inner ℝ (Model.feature k v) w/Real.sqrt N
      ∂Model.noiseLaw N k) = lam := by
    rw [integral_add (integrable_const lam) (hinner.div_const _),integral_const,
      probReal_univ,one_smul,integral_div,hmean,zero_div,add_zero]
  rw [MaximumProofs.expectedMaximum_eq_fixed_direction hN lam v hv]
  calc
    lam = _ := hEq.symm
    _ ≤ _ := integral_mono hInt ((Geometry.shiftedMaximum_memLp hN
      ((lam*Real.sqrt N) • Model.feature k v) 2 (by norm_num)).integrable one_le_two) hLower

/-- The physical pure lower mean bound follows from Bayesian values alone.
The finite derivative integral is controlled before adding any noise baseline,
so no pure or mixed physical ground-state limit occurs in the hypotheses. -/
theorem eventually_expectedMaximum_zero_lower_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, Scalar.gs k-eps ≤ Model.expectedMaximum (n+1) k 0 := by
  have hkeq : k-1+1 = k := by omega
  obtain ⟨lam,hsmall,hlam⟩ := ((mleValue_sub_strength_eventually_lt k hk (half_pos heps)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  let I := fun n : ℕ ↦ ∫ t in (0 : ℝ)..lam, selectedSlope (n+1) (k-1) (Nat.succ_pos n) t
  have hIupper : atTop.IsBoundedUnder (· ≤ ·) I :=
    isBoundedUnder_of ⟨lam,fun n ↦ (abs_le.mp
      (selectedSlope_integral_abs_le (n+1) (k-1) (Nat.succ_pos n) hlam)).2⟩
  have hIntegral : limsup I atTop ≤ Scalar.mleValue k lam-Scalar.gs k := by
    have H := integrated_selectedSlope_limsup_le_of_values (k-1) (by omega)
      (by simpa only [hkeq] using hvalues) hlam
    have H' : limsup I atTop ≤
        ∫ t in (0 : ℝ)..lam, (Real.sqrt (Scalar.qStar k t))^k := by
      simpa only [I,hkeq] using H
    have hId : Scalar.mleValue k lam = Scalar.gs k+
        ∫ t in (0 : ℝ)..lam, (Real.sqrt (Scalar.qStar k t))^k :=
      ScalarValueProofs.valueIdentity k hk hlam
    exact H'.trans_eq (by linarith only [hId])
  have hEvent := eventually_lt_add_pos_of_limsup_le hIupper hIntegral (half_pos heps)
  filter_upwards [hEvent] with n hn
  have hFinite := expectedMaximum_integral_identity (n+1) (k-1) (Nat.succ_pos n) 0 lam
  rw [hkeq] at hFinite
  have hPlant := strength_le_expectedMaximum (k := k) (Nat.succ_pos n) lam
  dsimp only [I] at hn
  linarith only [hn,hFinite,hPlant,hsmall]

end
end TensorPCA.PureGroundLowerFromBayesianProofs
