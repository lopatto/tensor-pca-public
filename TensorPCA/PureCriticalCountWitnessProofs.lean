-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureFieldNormalizationProofs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import TensorPCA.RetainedCountProofs.SphericalCountIntensity
public import TensorPCA.RetainedCountProofs.SphericalLocalMaxima

/-! An attained pure Gaussian maximum supplies a literal critical point
in its value window. The count is the original-disorder ENNReal sum. The
sphere Fermat argument is deterministic; no Morse/nonzero-Hessian premise
is required for this first-moment upper implication. -/
@[expose] public section
namespace TensorPCA.PureCriticalCountWitnessProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open RetainedCountProofs SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalForm HardSphereDynamics WholeFieldRegression
open PureFieldNormalizationProofs
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The literal expected pure value-window count is its proper scalar
Gaussian/Kac--Rice intensity, for every measurable window. -/
theorem actual_pure_value_count_intensity (n k : ℕ) (hk : 2 ≤ k)
    (I : Set ℝ) (hI : MeasurableSet I) :
    let μ := FiniteMixture.pure k hk 1 zero_lt_one
    let c := centerCoefficients (mixtureCoefficients μ) 1
    (∫⁻ J, actualValueWindowCount (n+1) c I (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
        ∫⁻ e in I, pureCriticalIntensity n k hk 1 zero_lt_one 1 e := by
  let K : Set (EuclideanSpace ℝ (Fin 2)) := {b | b 0 ∈ I}
  have hK : MeasurableSet K := hI.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have hwin : pureScoreWindow k K=I := by ext e; rfl
  have H := actual_pure_count_intensity n k hk 1 zero_lt_one zero_lt_one K hK
  dsimp only at H ⊢
  rw [hwin] at H
  apply (lintegral_congr (fun J => ?_)).trans H
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount,hwin]

/-- Any attained active-block maximum in `(a,b]` gives a point in the actual
critical-point subtype counted by the original source value-window count. -/
theorem one_le_value_count_of_maximum_mem (n k : ℕ) (hk : 2 ≤ k)
    (J : Disorder (n+2) (FiniteMixture.pure k hk 1 zero_lt_one).maxDegree)
    {a b : ℝ}
    (ha : a < Model.normalizedMaximum (WithLp.toLp 2 (J (pureDegree k hk))))
    (hb : Model.normalizedMaximum (WithLp.toLp 2 (J (pureDegree k hk))) ≤ b) :
    1 ≤ actualValueWindowCount (n+1)
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1)
      (Ioc a b) (fun _ _ => 1) J := by
  let N := n+2
  have hN : 0 < N := by omega
  let W : Model.Tensor N k := WithLp.toLp 2 (J (pureDegree k hk))
  let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure k hk 1 zero_lt_one)) 1
  obtain ⟨x,hx,hmax⟩ := Geometry.exists_maximizer hN W
  let y := Real.sqrt (N : ℝ) • x
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hy : ‖y‖^2=(N : ℝ) := by
    change ‖Real.sqrt (N : ℝ) • x‖^2=(N : ℝ)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs,(show ‖x‖=1 from hx),mul_one,
      Real.sq_sqrt (Nat.cast_nonneg N)]
  have hsourceMax : IsMaxOn (field c J) {z : Model.Vector N | ‖z‖^2=(N : ℝ)} y := by
    intro z hz
    rw [← sqrt_smul_unitSphere_image hN] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    change field c J (Real.sqrt (N : ℝ) • u) ≤ field c J y
    dsimp only [y,c]
    rw [field_pure_sqrt_smul hN k hk J u,field_pure_sqrt_smul hN k hk J x]
    exact mul_le_mul_of_nonneg_left (hmax u hu) hs.le
  have hcrit : surfaceGradient (field c J) y=0 := by
    apply surfaceGradient_eq_zero_of_sphere_localMax hN.ne' _ y
      ((onSphere_iff_norm_sq y).mpr hy) ((field_contDiff c J).differentiable (by simp) y)
    simpa only [onSphere_iff_norm_sq] using hsourceMax.isLocalMaxOn
  have hsup : sSup (Model.score W '' Model.unitSphere N)=Model.score W x := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro v ⟨u,hu,rfl⟩
    exact hmax u hu
  have hvalue : actualValue c J y=Model.normalizedMaximum W := by
    unfold actualValue
    dsimp only [y,c]
    rw [field_pure_sqrt_smul hN k hk J x,Model.normalizedMaximum,hsup]
    apply (div_eq_div_iff (Nat.cast_pos.mpr hN).ne' hs.ne').mpr
    have H := congrArg (fun t : ℝ => t*Model.score W x) (Real.sq_sqrt (Nat.cast_nonneg N))
    nlinarith
  have hmem : actualValue c J y ∈ Ioc a b := by rw [hvalue];exact ⟨ha,hb⟩
  exact ENNReal.le_tsum (f := fun z : {z : Vector (n+2) |
    ‖z‖^2=(n+2 : ℕ) ∧ surfaceGradient (field c J) z=0 ∧ actualValue c J z ∈ Ioc a b} => (1 : ℝ≥0∞))
    ⟨y,hy,hcrit,hmem⟩

/-- The actual Model maximum in a bounded interval is controlled by the
literal first critical-count moment under the genuine source disorder law. -/
theorem maximum_window_probability_le_intensity (n k : ℕ) (hk : 2 ≤ k) (a b : ℝ) :
    Model.noiseLaw (n+2) k {W | a < Model.normalizedMaximum W ∧ Model.normalizedMaximum W ≤ b} ≤
      ∫⁻ e in Ioc a b, pureCriticalIntensity n k hk 1 zero_lt_one 1 e := by
  let μ := FiniteMixture.pure k hk 1 zero_lt_one
  let c := centerCoefficients (mixtureCoefficients μ) 1
  have hF : Measurable (Model.normalizedMaximum (N := n+2) (k := k)) :=
    (Geometry.normalizedMaximum_lipschitz (by omega)).continuous.measurable
  have hs : MeasurableSet {W : Model.Tensor (n+2) k |
      a < Model.normalizedMaximum W ∧ Model.normalizedMaximum W ≤ b} :=
    (measurableSet_lt measurable_const hF).inter (measurableSet_le hF measurable_const)
  have hprob := (pureBlock_hasLaw (n+2) k hk).measure_eq hs
  have hm := (actual_value_window_kacRice (n+1) (by omega) μ zero_lt_one
    (Ioc a b) measurableSet_Ioc (fun _ _ => 1) measurable_const).1
  have H := meas_le_lintegral₀ hm (s := {J : Disorder (n+2) μ.maxDegree |
      a < Model.normalizedMaximum (WithLp.toLp 2 (J (pureDegree k hk))) ∧
        Model.normalizedMaximum (WithLp.toLp 2 (J (pureDegree k hk))) ≤ b})
    (fun J hJ => one_le_value_count_of_maximum_mem n k hk J hJ.1 hJ.2)
  exact hprob.symm.le.trans (H.trans_eq (actual_pure_value_count_intensity n k hk (Ioc a b) measurableSet_Ioc))


end
end TensorPCA.PureCriticalCountWitnessProofs
