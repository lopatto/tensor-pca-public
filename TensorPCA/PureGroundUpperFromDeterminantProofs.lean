-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureIntensityDecayProofs
public import TensorPCA.PureCriticalCountWitnessProofs
public import TensorPCA.GroundUpperProofs

/-! Pure upper-bound reduction from the ordinary-GOE first-mean estimate. Every other input is proved for the Model law:
finite Kac--Rice, maximum witness, Gaussian coarse upper and concentration.
The determinant estimate is an explicit proof parameter of this reduction. -/
@[expose] public section
namespace TensorPCA.PureGroundUpperFromDeterminantProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open RetainedCountProofs SphericalMarkedWindows SphericalGaussianJet GOEPhysicalPotential
open PureIntensityDecayProofs PureCriticalCountWitnessProofs
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000


lemma null_mean_eq_integral {N k : ℕ} (_hN : 0 < N) :
    Model.expectedMaximum N k 0 = ∫ W, Model.normalizedMaximum W ∂Model.noiseLaw N k := by
  unfold Model.expectedMaximum Model.observation Model.experimentLaw
  simp only [zero_mul,zero_smul,zero_add]
  rw [integral_fun_snd]
  simp

lemma pure_feature_increment_le {N k : ℕ} {x y : Model.Vector N}
    (hx : x ∈ Model.unitSphere N) (hy : y ∈ Model.unitSphere N) :
    ‖Model.feature k x-Model.feature k y‖ ≤ Real.sqrt (k : ℝ)*‖x-y‖ := by
  have hxn : ‖x‖=1 := hx
  have hyn : ‖y‖=1 := hy
  have hr : inner ℝ x y ∈ Icc (-1 : ℝ) 1 := by
    have H := abs_real_inner_le_norm x y
    rw [hxn,hyn,one_mul] at H
    exact abs_le.mp H
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sub_sq_real,Geometry.feature_unit_norm x hx,Geometry.feature_unit_norm y hy,
    Geometry.feature_inner,mul_pow,Real.sq_sqrt (Nat.cast_nonneg k),norm_sub_sq_real,hxn,hyn]
  nlinarith [GroundUpperProofs.one_sub_pow_le_mul k hr]

lemma null_mean_coarse_upper {N k : ℕ} (hN : 0 < N) :
    (∫ W, Model.normalizedMaximum W ∂Model.noiseLaw N k) ≤ Real.sqrt (k : ℝ) := by
  let : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  let : CompactSpace (Model.unitSphere N) := isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  let a : Model.unitSphere N → Model.Tensor N k := fun x => Model.feature k x.val
  let z : Model.unitSphere N → Model.Vector N := fun x => x.val
  have H := GaussianMaximumComparisonProofs.expected_supremum_le_linear_bound a z
    ((Model.continuous_feature N k).comp continuous_subtype_val) continuous_subtype_val
    (L := Real.sqrt (k : ℝ)) (Real.sqrt_nonneg _) (fun x => x.property)
    (fun x y => pure_feature_increment_le x.property y.property)
  have hsup (W : Model.Tensor N k) : sSup (Model.score W '' Model.unitSphere N) =
      ⨆ x : Model.unitSphere N, inner ℝ (Model.feature k x) W := by
    rw [iSup,Set.image_eq_range]
    rfl
  unfold Model.normalizedMaximum Model.noiseLaw
  rw [integral_div]
  simp_rw [hsup]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mpr
  simpa only [a,z,Fintype.card_fin] using H

lemma null_gaussian_tail {N k : ℕ} (hN : 0 < N) (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {W | |Model.normalizedMaximum W-
      ∫ V, Model.normalizedMaximum V ∂Model.noiseLaw N k| > t} ≤
        ENNReal.ofReal (2*Real.exp (-(N : ℝ)*t^2/2)) := by
  simpa only [zero_add] using Geometry.shiftedMaximum_gaussian_tail hN (0 : Model.Tensor N k) t ht

lemma coarse_null_upper_tail (n k : ℕ) :
    Model.noiseLaw (n+2) k {W | Real.sqrt (k : ℝ)+1 < Model.normalizedMaximum W} ≤
      ENNReal.ofReal (2*Real.exp (-((n+2 : ℕ) : ℝ)*(1 : ℝ)^2/2)) := by
  have hm := null_mean_coarse_upper (k := k) (show 0<n+2 by omega)
  apply (measure_mono ?_).trans (null_gaussian_tail (k := k) (by omega) 1 zero_lt_one)
  intro W hW
  change Real.sqrt (k : ℝ)+1 < Model.normalizedMaximum W at hW
  change |Model.normalizedMaximum W-(∫ V, Model.normalizedMaximum V ∂Model.noiseLaw (n+2) k)| > 1
  exact (show 1 < Model.normalizedMaximum W-
    ∫ V, Model.normalizedMaximum V ∂Model.noiseLaw (n+2) k by linarith).trans_le (le_abs_self _)

lemma exp_neg_dimension_mul_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-((n+2 : ℕ) : ℝ)*c)) atTop (𝓝 (0 : ℝ)) := by
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.atTop_mul_const hc) using 1
  funext n
  change Real.exp (-((n+2 : ℕ) : ℝ)*c)=Real.exp (-(((n+2 : ℕ) : ℝ)*c))
  congr 1
  ring

lemma gaussian_tail_bound_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (2*Real.exp (-((n+2 : ℕ) : ℝ)*t^2/2)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hreal : Tendsto (fun n : ℕ => 2*Real.exp (-((n+2 : ℕ) : ℝ)*t^2/2))
      atTop (𝓝 (0 : ℝ)) := by
    convert (exp_neg_dimension_mul_tendsto (t^2/2) (by positivity)).const_mul (2 : ℝ) using 1
    · funext n
      congr 1
      congr 1
      ring
    · ring
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal

/-- The actual pure null upper probability tends to zero once the genuine
compact-uniform ordinary determinant estimate is supplied. -/
theorem null_upper_probability_tendsto_of_detMean_upper (k : ℕ) (hk : 3 ≤ k) (D : ℝ)
    (hdet : ∀ Z : ℝ, 0 ≤ Z → ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, |r| ≤ Z →
      physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) r ≤
        Real.exp ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
          SemicirclePotential.potential (r/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => Model.noiseLaw (n+2) k
      {W | Scalar.gs k+δ < Model.normalizedMaximum W}) atTop (𝓝 (0 : ℝ≥0∞)) := by
  let M := Real.sqrt (k : ℝ)+1
  obtain ⟨c,hc,hwindow⟩ := eventually_pure_intensity_window_exp_le k hk D δ M hδ
    (hdet ((k : ℝ)*M) (by dsimp [M];positivity))
  have hexp : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-((n+2 : ℕ) : ℝ)*c)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (exp_neg_dimension_mul_tendsto c hc)
  have hfirst : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-((n+2 : ℕ) : ℝ)*c))*
      ENNReal.ofReal (M-(Scalar.gs k+δ))) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hexp (Or.inr ENNReal.ofReal_ne_top)
  have hsum := hfirst.add (gaussian_tail_bound_tendsto 1 zero_lt_one)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hsum) (.of_forall (fun _ => zero_le)) ?_
  filter_upwards [hwindow] with n hn
  have hsplit : Model.noiseLaw (n+2) k {W | Scalar.gs k+δ < Model.normalizedMaximum W} ≤
      Model.noiseLaw (n+2) k {W | Scalar.gs k+δ < Model.normalizedMaximum W ∧ Model.normalizedMaximum W ≤ M} +
      Model.noiseLaw (n+2) k {W | M < Model.normalizedMaximum W} := by
    apply (measure_mono ?_).trans (measure_union_le _ _)
    intro W hW
    by_cases hM : Model.normalizedMaximum W ≤ M
    · exact Or.inl ⟨hW,hM⟩
    · exact Or.inr (lt_of_not_ge hM)
  exact hsplit.trans (add_le_add
    ((maximum_window_probability_le_intensity n k (by omega) (Scalar.gs k+δ) M).trans hn)
    (coarse_null_upper_tail n k))

/-- Actual Gaussian concentration upgrades vanishing upper probability to
an upper bound for the true expectation, without a variance hypothesis. -/
theorem eventually_null_mean_upper_of_upper_probability (k : ℕ) (g : ℝ)
    (hprob : ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => Model.noiseLaw (n+2) k
      {W | g+δ < Model.normalizedMaximum W}) atTop (𝓝 (0 : ℝ≥0∞)))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (∫ W, Model.normalizedMaximum W ∂Model.noiseLaw (n+2) k) ≤ g+eps := by
  have hh : 0 < eps/2 := by positivity
  have hp := (hprob (eps/2) hh).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞)<1/4))
  have hc := (gaussian_tail_bound_tendsto (eps/2) hh).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞)<1/4))
  filter_upwards [hp,hc] with n hn hcn
  by_contra hmean
  have hm : g+eps < ∫ W, Model.normalizedMaximum W ∂Model.noiseLaw (n+2) k := lt_of_not_ge hmean
  let A : Set (Model.Tensor (n+2) k) := {W | g+eps/2 < Model.normalizedMaximum W}
  let B : Set (Model.Tensor (n+2) k) := {W | |Model.normalizedMaximum W-
    ∫ V, Model.normalizedMaximum V ∂Model.noiseLaw (n+2) k| > eps/2}
  have hcover : (univ : Set (Model.Tensor (n+2) k)) ⊆ A ∪ B := by
    intro W _
    by_cases hW : g+eps/2 < Model.normalizedMaximum W
    · exact Or.inl hW
    · apply Or.inr
      change |Model.normalizedMaximum W-(∫ V, Model.normalizedMaximum V ∂Model.noiseLaw (n+2) k)| > eps/2
      have hw : Model.normalizedMaximum W ≤ g+eps/2 := le_of_not_gt hW
      exact (show eps/2 < -(Model.normalizedMaximum W-
        ∫ V, Model.normalizedMaximum V ∂Model.noiseLaw (n+2) k) by linarith).trans_le (neg_le_abs _)
  have htail := null_gaussian_tail (k := k) (show 0<n+2 by omega) (eps/2) hh
  have hsum : (1 : ℝ≥0∞) ≤ Model.noiseLaw (n+2) k A+Model.noiseLaw (n+2) k B := by
    calc
      1 = Model.noiseLaw (n+2) k univ := by simp
      _ ≤ Model.noiseLaw (n+2) k (A ∪ B) := measure_mono hcover
      _ ≤ _ := measure_union_le _ _
  have hsmall := ENNReal.add_lt_add hn (htail.trans_lt hcn)
  have hquarter : (1/4 : ℝ≥0∞)+(1/4)<1 := by
    rw [ENNReal.div_add_div_same]
    apply (ENNReal.div_lt_iff (Or.inl (by norm_num : (4 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))).mpr
    norm_num
  exact not_lt_of_ge hsum (hsmall.trans hquarter)

/-- The exact one-sided pure-null expectation input used by the checked MLE
reduction follows from the genuine ordinary matrix first-mean upper alone.
All other analytic/probabilistic prerequisites are discharged above. -/
theorem eventually_expectedMaximum_zero_upper_of_detMean_upper (k : ℕ) (hk : 3 ≤ k) (D : ℝ)
    (hdet : ∀ Z : ℝ, 0 ≤ Z → ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, |r| ≤ Z →
      physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) r ≤
        Real.exp ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
          SemicirclePotential.potential (r/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps := by
  have H := eventually_null_mean_upper_of_upper_probability k (Scalar.gs k)
    (fun δ hδ => null_upper_probability_tendsto_of_detMean_upper k hk D hdet δ hδ) eps heps
  have hplus : ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+2) k 0 ≤ Scalar.gs k+eps := by
    filter_upwards [H] with n hn
    rw [null_mean_eq_integral (show 0<n+2 by omega)]
    exact hn
  have hshift := (tendsto_sub_atTop_nat 1).eventually hplus
  filter_upwards [hshift,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have heq : n-1+2=n+1 := by omega
  simpa only [heq] using hn


end
end TensorPCA.PureGroundUpperFromDeterminantProofs
