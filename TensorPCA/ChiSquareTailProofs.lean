-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.RadialTailBounds
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Gaussian radial tails by polar integration and elementary radial windows.
The surface-area constant cancels by Gaussian probability normalization. -/
@[expose] public section
namespace TensorPCA.ChiSquareTailProofs
open MeasureTheory ProbabilityTheory Set Filter RadialTailBounds
open scoped Topology ENNReal BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem integral_density_radial (f : ℝ → ℝ) :
    (∫ x : E, GaussianDensityProofs.density x*f ‖x‖) =
      ((Module.finrank ℝ E : ℝ)*volume.real (Metric.ball (0 : E) 1)*
        GaussianDensityProofs.normalizer E)*
        ∫ r in Ioi (0 : ℝ), radialDensity (Module.finrank ℝ E-1) r*f r := by
  have hfun : (fun x : E ↦ GaussianDensityProofs.density x*f ‖x‖) =
      (fun x : E ↦ GaussianDensityProofs.normalizer E*(Real.exp (-‖x‖^2/2)*f ‖x‖)) := by
    funext x
    unfold GaussianDensityProofs.density
    rw [show -(1/2 : ℝ)*‖x‖^2 = -‖x‖^2/2 by ring]
    ring
  rw [hfun, integral_const_mul]
  have hpol := integral_fun_norm_addHaar (E := E) (F := ℝ) (volume : Measure E)
    (fun r : ℝ ↦ Real.exp (-r^2/2)*f r)
  rw [hpol]
  simp only [nsmul_eq_mul, smul_eq_mul]
  have hi : (∫ r in Ioi (0 : ℝ), r^(Module.finrank ℝ E-1)*(Real.exp (-r^2/2)*f r)) =
      ∫ r in Ioi (0 : ℝ), radialDensity (Module.finrank ℝ E-1) r*f r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _hr
    unfold radialDensity
    ring
  rw [hi]
  ring

theorem stdGaussian_norm_tail_ratio {s : ℝ} (hs : 0 < s) :
    (stdGaussian E).real {x : E | s ≤ ‖x‖} =
      (∫ r in Ici s, radialDensity (Module.finrank ℝ E-1) r)/
        radialNormalizer (Module.finrank ℝ E-1) := by
  let A : ℝ := (Module.finrank ℝ E : ℝ)*volume.real (Metric.ball (0 : E) 1)*
    GaussianDensityProofs.normalizer E
  have hnormal : A*radialNormalizer (Module.finrank ℝ E-1) = 1 := by
    have h := integral_density_radial (E := E) (fun _r ↦ (1 : ℝ))
    simp only [mul_one] at h
    exact h.symm.trans GaussianDensityProofs.density_integral
  have hset : MeasurableSet {x : E | s ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hprob : (stdGaussian E).real {x : E | s ≤ ‖x‖} =
      ∫ x in {x : E | s ≤ ‖x‖}, GaussianDensityProofs.density x := by
    rw [← setIntegral_one_eq_measureReal, GaussianDensityProofs.stdGaussian_eq_withDensity]
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      (GaussianDensityProofs.density_continuous.measurable.ennreal_ofReal.aemeasurable.restrict)
      (Eventually.of_forall fun _x ↦ ENNReal.ofReal_lt_top) (fun _x : E ↦ (1 : ℝ)) hset]
    apply setIntegral_congr_fun hset
    intro x _hx
    simp only [ENNReal.toReal_ofReal (GaussianDensityProofs.density_pos x).le, smul_eq_mul, mul_one]
  have hind : (∫ x in {x : E | s ≤ ‖x‖}, GaussianDensityProofs.density x) =
      ∫ x : E, GaussianDensityProofs.density x*((Ici s).indicator (fun _r : ℝ ↦ (1 : ℝ))) ‖x‖ := by
    rw [← integral_indicator hset]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by
      by_cases hx : s ≤ ‖x‖ <;> simp [Set.indicator, hx]
  have htail : (∫ r in Ioi (0 : ℝ), radialDensity (Module.finrank ℝ E-1) r*
      ((Ici s).indicator (fun _r : ℝ ↦ (1 : ℝ))) r) =
      ∫ r in Ici s, radialDensity (Module.finrank ℝ E-1) r := by
    have hi : (fun r : ℝ ↦ radialDensity (Module.finrank ℝ E-1) r*
        ((Ici s).indicator (fun _r : ℝ ↦ (1 : ℝ))) r) =
        (Ici s).indicator (radialDensity (Module.finrank ℝ E-1)) := by
      funext r
      by_cases hr : s ≤ r <;> simp [Set.indicator, hr]
    rw [hi, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hsub : Ici s ∩ Ioi (0 : ℝ) = Ici s :=
      inter_eq_left.mpr (fun _r hr ↦ hs.trans_le hr)
    rw [hsub]
  have hvalue : (stdGaussian E).real {x : E | s ≤ ‖x‖} =
      A*(∫ r in Ici s, radialDensity (Module.finrank ℝ E-1) r) := by
    rw [hprob, hind, integral_density_radial, htail]
  apply (eq_div_iff (radialNormalizer_pos _).ne').mpr
  rw [hvalue]
  calc
    _ = (A*radialNormalizer (Module.finrank ℝ E-1))*
        (∫ r in Ici s, radialDensity (Module.finrank ℝ E-1) r) := by ring
    _ = _ := by rw [hnormal]; ring
end Polar

theorem stdGaussian_norm_sq_tail_ratio {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    (stdGaussian (EuclideanSpace ℝ (Fin N))).real {x | (N : ℝ)*b ≤ ‖x‖^2} =
      (∫ r in Ici (Real.sqrt ((N : ℝ)*b)), radialDensity (N-1) r)/radialNormalizer (N-1) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hs : 0 < Real.sqrt ((N : ℝ)*b) := Real.sqrt_pos.mpr (mul_pos hn hb0)
  have hset : {x : EuclideanSpace ℝ (Fin N) | (N : ℝ)*b ≤ ‖x‖^2} =
      {x | Real.sqrt ((N : ℝ)*b) ≤ ‖x‖} := by
    ext x
    have he : (Real.sqrt ((N : ℝ)*b))^2 = (N : ℝ)*b := Real.sq_sqrt (mul_nonneg hn.le hb0.le)
    constructor
    · intro hx
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp (he.trans_le hx)
    · intro hx
      exact he.symm.trans_le ((sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mpr hx)
  rw [hset]
  simpa only [finrank_euclideanSpace_fin] using
    (stdGaussian_norm_tail_ratio (E := EuclideanSpace ℝ (Fin N)) hs)

/-- Lemma A.8 for the actual finite standard Gaussian vector. The constant is
universal in both dimension and the deviation parameter; b=1 is included too. -/
theorem chiSquare_tail_lower {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    0 < (stdGaussian (EuclideanSpace ℝ (Fin N))).real {x | (N : ℝ)*b ≤ ‖x‖^2} ∧
      -(1/2 : ℝ)*(b-1-Real.log b)-2*Real.log b/(N : ℝ)-
        tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      (1/(N : ℝ))*Real.log ((stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x | (N : ℝ)*b ≤ ‖x‖^2}) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hprob := stdGaussian_norm_sq_tail_ratio hN hb
  have hlower := radialTail_ratio_lower hN hb
  rw [← hprob] at hlower
  have hp := (Real.exp_pos _).trans_le hlower
  refine ⟨hp, ?_⟩
  have hlog := (Real.le_log_iff_exp_le hp).mpr hlower
  have hd := div_le_div_of_nonneg_right hlog hn.le
  convert hd using 1 <;> field_simp [hn.ne']

theorem chiSquare_tail_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ b : ℝ, 1 < b →
      -(1/2 : ℝ)*(b-1-Real.log b)-2*Real.log b/(N : ℝ)-
        C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      (1/(N : ℝ))*Real.log ((stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x | (N : ℝ)*b ≤ ‖x‖^2}) :=
  ⟨tailLogConstant, tailLogConstant_pos, fun _N hN _b hb ↦ (chiSquare_tail_lower hN hb.le).2⟩

theorem norm_sq_eq_sum_sq {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    ‖x‖^2 = ∑ i : Fin N, (x i)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two]

/-- Coordinate form: the coordinates of the canonical finite Gaussian vector
are independent standard normals, and this is the manuscript's S_N event. -/
theorem chiSquare_sum_tail_lower {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    0 < (stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x | 1 ≤ (∑ i : Fin N, (x i)^2)/(b*(N : ℝ))} ∧
      -(1/2 : ℝ)*(b-1-Real.log b)-2*Real.log b/(N : ℝ)-
        tailLogConstant*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      (1/(N : ℝ))*Real.log ((stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x | 1 ≤ (∑ i : Fin N, (x i)^2)/(b*(N : ℝ))}) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hset : {x : EuclideanSpace ℝ (Fin N) | 1 ≤ (∑ i : Fin N, (x i)^2)/(b*(N : ℝ))} =
      {x | (N : ℝ)*b ≤ ‖x‖^2} := by
    ext x
    change (1 : ℝ) ≤ (∑ i : Fin N, (x i)^2)/(b*(N : ℝ)) ↔ (N : ℝ)*b ≤ ‖x‖^2
    rw [le_div_iff₀ (mul_pos hb0 hn), one_mul, ← norm_sq_eq_sum_sq]
    constructor <;> intro hx <;> nlinarith
  simpa only [hset] using chiSquare_tail_lower hN hb

end
end TensorPCA.ChiSquareTailProofs
