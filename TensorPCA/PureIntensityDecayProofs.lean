-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureIntensityUpperProofs
public import TensorPCA.RetainedCountProofs.SphericalGeometricPrefactorBounds

/-! The shared ordinary-GOE first-mean upper implies exponential decay
of the pure Kac--Rice intensity above the scalar ground value.
The determinant estimate is an explicit proof parameter of this intensity bound. -/
@[expose] public section
namespace TensorPCA.PureIntensityDecayProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open RetainedCountProofs SphericalMarkedWindows SphericalModel SphericalGaussianJet
open SphericalSequentialRegression SphereChartVolume GOEPhysicalPotential
open PureComplexityProofs PureIntensityUpperProofs
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The intensity itself is finite, so its real part does not hide infinity. -/
lemma pureCriticalIntensity_ne_top (n k : ℕ) (hk : 2 ≤ k) (e : ℝ) :
    pureCriticalIntensity n k hk 1 zero_lt_one 1 e ≠ ⊤ := by
  unfold pureCriticalIntensity physicalValuePdf
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (sphereKRPrefactor_ne_top _ _ _) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

/-- Uniform exponential smallness on any fixed bounded-shift window above
the ground constant, from an explicit ordinary matrix determinant estimate. -/
theorem eventually_pureCriticalIntensity_exp_le (k : ℕ) (hk : 3 ≤ k)
    (Z D δ : ℝ) (hδ : 0 < δ)
    (hmean : ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, |r| ≤ Z →
      physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) r ≤
        Real.exp ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
          SemicirclePotential.potential (r/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ e : ℝ,
      Scalar.gs k+δ ≤ e → |(k : ℝ)*e| ≤ Z →
        (pureCriticalIntensity n k (by omega) 1 zero_lt_one 1 e).toReal ≤
          Real.exp (-(n+2 : ℕ)*c) := by
  obtain ⟨B,hB,harea⟩ := manuscriptRoundVolume_log_error_bound
  let a := pureComplexitySlope k
  have ha : 0 < a := pureComplexitySlope_pos k hk
  let eps := a*δ/4
  have heps : 0 < eps := by dsimp [eps]; positivity
  let C := Real.log (k : ℝ)/2+D+B
  have hlim : Tendsto (fun n : ℕ => (Real.log (n+2 : ℝ)/(n+2 : ℝ))/2+C/(n+2 : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div,add_zero] using
      (log_dimension_div_tendsto.div_const 2).add (constant_div_dimension_tendsto C)
  have hsmall := hlim.eventually (gt_mem_nhds heps)
  refine ⟨a*δ/2,by positivity,?_⟩
  filter_upwards [hmean eps heps,hsmall] with n hn hs
  intro e he hshift
  have hN : (0 : ℝ) < (n+2 : ℕ) := by positivity
  have hsmall' : Real.log (n+2 : ℕ)/2+C < (n+2 : ℕ)*eps := by
    rw [mul_comm ((n+2 : ℕ) : ℝ) eps]
    apply (div_lt_iff₀ hN).mp
    have heq : (Real.log (n+2 : ℕ)/2+C)/(n+2 : ℕ) =
        (Real.log (n+2 : ℕ)/(n+2 : ℕ))/2+C/(n+2 : ℕ) := by ring
    rw [heq]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hs
  have hc := pureComplexity_upper_linear k hk (show Scalar.gs k ≤ e by linarith)
  have hmargin := mul_le_mul_of_nonneg_left (show δ ≤ e-Scalar.gs k by linarith) ha.le
  have hc' : pureComplexity k e ≤ -a*δ := by dsimp only [a] at *; linarith
  have hscaled := mul_le_mul_of_nonneg_left hc' hN.le
  have harea' := (abs_le.mp (harea n)).2
  have H := pureCriticalIntensity_upper_of_detMean_upper n k hk e eps D (hn _ hshift)
  apply H.trans
  apply Real.exp_le_exp.mpr
  dsimp only [C,eps] at hsmall' ⊢
  nlinarith

/-- The scalar ground constant is positive in every required degree. -/
lemma gs_pos (k : ℕ) (hk : 3 ≤ k) : 0 < Scalar.gs k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hz := (ScalarThresholdProofs.zK_spec k hk).1
  rw [PureVariationalProofs.gs_eq_normalized k hk]
  exact div_pos (add_pos hk0 hz) (Real.sqrt_pos.mpr (mul_pos hk0 (by linarith)))

/-- Integrating the pointwise estimate gives the true finite-window count
intensity bound; all ENNReal infinities are controlled explicitly. -/
theorem eventually_pure_intensity_window_exp_le (k : ℕ) (hk : 3 ≤ k)
    (D δ M : ℝ) (hδ : 0 < δ)
    (hmean : ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, |r| ≤ (k : ℝ)*M →
      physicalMean n (n+2) ((k : ℝ)*((k : ℝ)-1)) r ≤
        Real.exp ((n+2 : ℕ)*(Real.log ((k : ℝ)*((k : ℝ)-1))/2+
          SemicirclePotential.potential (r/Real.sqrt ((k : ℝ)*((k : ℝ)-1)))+eps)+D)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (∫⁻ e in Ioc (Scalar.gs k+δ) M, pureCriticalIntensity n k (by omega) 1 zero_lt_one 1 e) ≤
        ENNReal.ofReal (Real.exp (-(n+2 : ℕ)*c))*ENNReal.ofReal (M-(Scalar.gs k+δ)) := by
  obtain ⟨c,hc,hbound⟩ := eventually_pureCriticalIntensity_exp_le k hk ((k : ℝ)*M) D δ hδ hmean
  refine ⟨c,hc,?_⟩
  filter_upwards [hbound] with n hn
  have H := setLIntegral_mono (μ := volume)
    (f := fun e => pureCriticalIntensity n k (by omega) 1 zero_lt_one 1 e)
    (s := Ioc (Scalar.gs k+δ) M)
    (measurable_const (a := ENNReal.ofReal (Real.exp (-(n+2 : ℕ)*c)))) ?_
  · simpa only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc] using H
  · intro e he
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
    have he0 : 0 < e := by linarith [gs_pos k hk,he.1]
    have hshift : |(k : ℝ)*e| ≤ (k : ℝ)*M := by
      rw [abs_of_pos (mul_pos hk0 he0)]
      exact mul_le_mul_of_nonneg_left he.2 hk0.le
    exact (ENNReal.le_ofReal_iff_toReal_le (pureCriticalIntensity_ne_top n k (by omega) e)
      (Real.exp_pos _).le).mpr (hn e he.1.le hshift)


end
end TensorPCA.PureIntensityDecayProofs
