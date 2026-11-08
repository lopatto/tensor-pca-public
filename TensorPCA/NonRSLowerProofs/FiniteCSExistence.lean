-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSDefinitions
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Lower semicontinuity and attainment for the complete extended finite-temperature CS
functional. Compactness is that of the standard weak probability-measure space; no
minimizer or compact cutoff is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem profile_continuous (beta : ℝ) (nu : Trial) : Continuous (profile beta nu) := by
  change Continuous (fun t => beta * hatCDF (nu : Measure Overlap) t)
  exact continuous_const.mul (hatCDF_continuous _)

theorem continuous_secondDeriv_slice (k : ℕ) (m : ℝ) :
    Continuous (deriv (deriv (Scalar.xiSlice k m))) := by
  have H : ContDiff ℝ (1 + 1) (Scalar.xiSlice k m) := by
    unfold Scalar.xiSlice
    fun_prop
  exact H.deriv'.continuous_deriv_one

theorem entropyExcess_measurable (beta : ℝ) (nu : Trial) :
    Measurable (entropyExcess beta nu) := by
  have hp := profile_continuous beta nu
  unfold entropyExcess
  fun_prop

theorem continuous_entropyExcess_eval (beta t : ℝ) :
    Continuous (fun nu : Trial => entropyExcess beta nu t) := by
  unfold entropyExcess
  apply (ENNReal.continuous_sub_right _).comp
  exact (ENNReal.continuous_ofReal.comp (continuous_profile_eval beta t)).fun_inv

/-- Fatou applied to the neighborhood filter. The probability trial space is
metrizable, so this filter is countably generated. -/
theorem lowerSemicontinuous_lintegral {A X : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (mu : Measure X)
    (f : A → X → ℝ≥0∞) (hmeas : ∀ a, Measurable (f a))
    (hcont : ∀ x, Continuous (fun a => f a x)) :
    LowerSemicontinuous (fun a => ∫⁻ x, f a x ∂mu) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro a
  have heq (x : X) : f a x = liminf (fun b => f b x) (𝓝 a) :=
    ((hcont x).continuousAt.tendsto.liminf_eq).symm
  calc
    (∫⁻ x, f a x ∂mu) = ∫⁻ x, liminf (fun b => f b x) (𝓝 a) ∂mu := by
      apply lintegral_congr
      intro x
      exact heq x
    _ ≤ _ := lintegral_liminf_le hmeas

theorem entropy_lowerSemicontinuous (beta : ℝ) : LowerSemicontinuous (entropy beta) :=
  lowerSemicontinuous_lintegral (volume.restrict (Ico (0 : ℝ) 1))
    (entropyExcess beta) (entropyExcess_measurable beta) (continuous_entropyExcess_eval beta)

theorem energy_lowerSemicontinuous (k : ℕ) (beta m : ℝ) :
    LowerSemicontinuous (energy k beta m) := by
  have hint : LowerSemicontinuous (fun nu : Trial =>
      ∫⁻ t in Ico (0 : ℝ) 1,
        ENNReal.ofReal (deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t)) := by
    apply lowerSemicontinuous_lintegral
    · intro nu
      exact ENNReal.continuous_ofReal.measurable.comp
        (((continuous_secondDeriv_slice k m).mul (profile_continuous beta nu)).measurable)
    · intro t
      exact ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_profile_eval beta t))
  have hboundary : Continuous (fun nu : Trial =>
      ENNReal.ofReal (deriv (Scalar.xiSlice k m) 0 * profile beta nu 0)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_profile_eval beta 0))
  exact hint.add hboundary.lowerSemicontinuous

theorem rawFunctional_lowerSemicontinuous (k : ℕ) (beta m : ℝ) :
    LowerSemicontinuous (rawFunctional k beta m) :=
  (energy_lowerSemicontinuous k beta m).add (entropy_lowerSemicontinuous beta)

/-- A trial attains the complete extended infimum. The finiteness of its value and the
support geometry are separate subsequent conclusions.
-/
theorem exists_minimizer (k : ℕ) (beta m : ℝ) :
    ∃ nu : Trial, rawFunctional k beta m nu = rawValue k beta m ∧
      ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau := by
  have hne : (univ : Set Trial).Nonempty := ⟨diracTrial ⟨0, by norm_num⟩, mem_univ _⟩
  obtain ⟨nu, hnu, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne isCompact_trials
    ((rawFunctional_lowerSemicontinuous k beta m).lowerSemicontinuousOn univ)
  have hleast : IsLeast (range (rawFunctional k beta m)) (rawFunctional k beta m nu) := by
    refine ⟨⟨nu, rfl⟩, ?_⟩
    rintro _ ⟨tau, rfl⟩
    exact hmin (mem_univ tau)
  exact ⟨nu, hleast.csInf_eq.symm, fun tau => hmin (mem_univ tau)⟩


end
end TensorPCA.NonRSLowerProofs.FiniteCS
