-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumProofs
public import TensorPCA.Statistical
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Gaussian maximum concentration gives a finite second-moment bound. -/
@[expose] public section
namespace TensorPCA.MaximumMSEProofs
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem integral_sq_le_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {c : ℝ} (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 < t → μ {w | t < |X w|} ≤ ENNReal.ofReal (2*Real.exp (-c*t^2/2))) :
    (∫ w, (X w)^2 ∂μ) ≤ 4/c := by
  let T : ℝ → ℝ := fun t => μ.real {w | t < (X w)^2}
  have hTanti : Antitone T := by
    intro a b hab
    exact measureReal_mono (fun w hw => hab.trans_lt hw)
  have hbound (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : T t ≤ 2*Real.exp ((-c/2)*t) := by
    have hsqrt := Real.sqrt_pos.mpr ht
    have hevent : {w | t < (X w)^2} = {w | Real.sqrt t < |X w|} := by
      ext w
      have habs := abs_nonneg (X w)
      have hsqabs := sq_abs (X w)
      have hsqt := Real.sq_sqrt ht.le
      constructor <;> intro h <;> dsimp at * <;> nlinarith
    have hh := htail (Real.sqrt t) hsqrt
    rw [← hevent, Real.sq_sqrt ht.le] at hh
    have hr := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (2*Real.exp (-c*t/2)) ≠ ∞) hh
    have he : 0 ≤ 2*Real.exp (-c*t/2) := by positivity
    have hr' : T t ≤ 2*Real.exp (-c*t/2) := by
      simpa only [T, measureReal_def, ENNReal.toReal_ofReal he] using hr
    have heq : -c*t/2 = (-c/2)*t := by ring
    simpa only [heq] using hr'
  have hu : IntegrableOn (fun t : ℝ => 2*Real.exp ((-c/2)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -c/2 < 0) 0).const_mul 2
  have hT : IntegrableOn T (Ioi 0) := hu.mono' hTanti.measurable.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs]
      have hn : 0 ≤ T t := measureReal_nonneg
      rw [abs_of_nonneg hn]
      exact hbound t ht)
  calc
    (∫ w, (X w)^2 ∂μ) = ∫ t in Ioi 0, T t :=
      hX.integrable_sq.integral_eq_integral_meas_lt (Eventually.of_forall (fun _ => sq_nonneg _))
    _ ≤ ∫ t in Ioi 0, 2*Real.exp ((-c/2)*t) := integral_mono_ae hT hu (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht)
    _ = 4/c := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c/2 < 0) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp [hc.ne']
      norm_num

/-- The actual planted maximum has a dimension-uniform centered second moment. -/
theorem centeredMaximum_sq_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    (∫ z, (Model.normalizedMaximum (Model.observation lam z)-Model.expectedMaximum N k lam)^2
      ∂Model.experimentLaw N k) ≤ 4/(N : ℝ) := by
  have hX := (MaximumProofs.plantedMaximum_memLp_two (k := k) hN lam).sub
    (memLp_const (Model.expectedMaximum N k lam))
  apply integral_sq_le_of_gaussian_tail (Model.experimentLaw N k) hX (Nat.cast_pos.mpr hN)
  intro t ht
  exact MaximumProofs.plantedMaximum_gaussian_tail hN lam t ht

/-- The true maximum mean-square error is bounded by Gaussian fluctuations and
the square of the actual annealed mean error. -/
theorem maximumMeanSquare_le {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    Statistical.maximumMeanSquare N k lam ≤ 8/(N : ℝ)+
      2*(Model.expectedMaximum N k lam-Scalar.mleValue k lam)^2 := by
  have hM := (Geometry.normalizedMaximum_lipschitz (k := k) hN).continuous.measurable
  have hsq : Measurable (fun y : Model.Tensor N k => (Model.normalizedMaximum y-Scalar.mleValue k lam)^2) :=
    (hM.sub measurable_const).pow_const 2
  unfold Statistical.maximumMeanSquare Model.observationLaw
  rw [integral_map (Model.measurable_observation N k lam).aemeasurable hsq.aestronglyMeasurable]
  have hLp := MaximumProofs.plantedMaximum_memLp_two (k := k) hN lam
  have hcenter := (hLp.sub (memLp_const (Model.expectedMaximum N k lam))).integrable_sq
  have htarget := (hLp.sub (memLp_const (Scalar.mleValue k lam))).integrable_sq
  have hi := integral_mono htarget
    ((hcenter.const_mul 2).add (integrable_const (2*(Model.expectedMaximum N k lam-Scalar.mleValue k lam)^2)))
    (fun z => by
      dsimp only [Pi.sub_apply, Pi.add_apply]
      nlinarith [sq_nonneg (Model.normalizedMaximum (Model.observation lam z)-
        2*Model.expectedMaximum N k lam+Scalar.mleValue k lam)])
  dsimp only [Pi.sub_apply, Pi.add_apply] at hi hcenter htarget
  rw [integral_add (hcenter.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hi
  have h8 : (8 : ℝ)/(N : ℝ) = 2*(4/(N : ℝ)) := by ring
  apply hi.trans
  rw [h8]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (centeredMaximum_sq_le (k := k) hN lam) (by norm_num : (0 : ℝ) ≤ 2)) le_rfl

/-- A mean-maximum limit and the proved finite Gaussian bound suffice
for mean-square consistency. No classification conclusion is an input. -/
theorem maximumMeanSquare_tendsto {k : ℕ} {lam : ℝ}
    (hmean : Tendsto (fun n : ℕ => Model.expectedMaximum (n+1) k lam)
      atTop (𝓝 (Scalar.mleValue k lam))) :
    Tendsto (fun n : ℕ => Statistical.maximumMeanSquare (n+1) k lam) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfirst := hN.const_div_atTop (8 : ℝ)
  have hsecond := ((hmean.sub (tendsto_const_nhds (x := Scalar.mleValue k lam))).pow 2).const_mul (2 : ℝ)
  have hu : Tendsto (fun n : ℕ => 8/((n+1 : ℕ) : ℝ)+
      2*(Model.expectedMaximum (n+1) k lam-Scalar.mleValue k lam)^2) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, sub_self, zero_pow two_ne_zero, mul_zero, add_zero] using
      hfirst.add hsecond
  apply tendsto_const_nhds.squeeze hu
  · intro n
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro n
    exact maximumMeanSquare_le (Nat.succ_pos n) lam

end
end TensorPCA.MaximumMSEProofs
