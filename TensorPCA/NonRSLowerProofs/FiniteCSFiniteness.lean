-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSExistence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Finiteness and positivity for finite-temperature CS minimizers. The finite
competitor is the probability atom at zero.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem energy_ne_top (k : ℕ) (beta m : ℝ) (nu : Trial) :
    energy k beta m nu ≠ ∞ := by
  have hc : Continuous (fun t => deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t) :=
    (continuous_secondDeriv_slice k m).mul (profile_continuous beta nu)
  have hi : IntegrableOn (fun t => deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t)
      (Ico (0 : ℝ) 1) := hc.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hp := hi.pos_part
  have hf : (∫⁻ t in Ico (0 : ℝ) 1,
      ENNReal.ofReal (deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t)) ≠ ∞ := by
    have hh := (lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable
      (.of_forall fun t => le_max_right _ (0 : ℝ))).mpr hp
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero] using hh
  exact ENNReal.add_ne_top.mpr ⟨hf, ENNReal.ofReal_ne_top⟩

theorem rawFunctional_dirac_zero_ne_top (k : ℕ) (beta m : ℝ) :
    rawFunctional k beta m (diracTrial ⟨0, by norm_num⟩) ≠ ∞ := by
  rw [rawFunctional, entropy_dirac_zero, add_zero]
  exact energy_ne_top k beta m _

theorem rawValue_ne_top (k : ℕ) (beta m : ℝ) : rawValue k beta m ≠ ∞ := by
  apply ne_top_of_le_ne_top (rawFunctional_dirac_zero_ne_top k beta m)
  exact sInf_le ⟨_, rfl⟩

theorem exists_finite_minimizer (k : ℕ) (beta m : ℝ) :
    ∃ nu : Trial, rawFunctional k beta m nu = rawValue k beta m ∧
      rawFunctional k beta m nu ≠ ∞ ∧
      ∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau := by
  obtain ⟨nu, heq, hmin⟩ := exists_minimizer k beta m
  exact ⟨nu, heq, heq ▸ rawValue_ne_top k beta m, hmin⟩

end
end TensorPCA.NonRSLowerProofs.FiniteCS
