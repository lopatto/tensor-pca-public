-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.VariationalProofs
public import TensorPCA.NonRSLowerProofs.FiniteCSKernel
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Tactic.FunProp

/-! Finite-temperature spherical CS trial data. A trial is a probability measure on the
closed overlap interval. Its integrated CDF profile has terminal value zero; it is
distinct from a positive-floor zero-temperature profile. Entropy uses the extended
inverse and truncated subtraction, so vanishing profiles below one are penalized
rather than interpreted by the real-number convention 1/0=0.

The raw functional is twice the CS free energy divided by beta. Its energy is written as
a nonnegative extended integral; on the manuscript domain beta>0, m in [-1,1], its
polynomial weights are nonnegative. Equality with the ordinary cutoff formula is proved
separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section

abbrev Trial := ProbabilityMeasure Overlap

/-- beta times the integrated CDF, including both endpoint atoms. -/
def profile (beta : ℝ) (nu : Trial) (t : ℝ) : ℝ :=
  beta * ∫ q : Overlap, kernel t q ∂(nu : Measure Overlap)

/-- The nonnegative entropy excess on [0,1); all inverses are extended. -/
def entropyExcess (beta : ℝ) (nu : Trial) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (profile beta nu t))⁻¹ -
    (ENNReal.ofReal (beta * (1 - t)))⁻¹

def entropy (beta : ℝ) (nu : Trial) : ℝ≥0∞ :=
  ∫⁻ t in Ico (0 : ℝ) 1, entropyExcess beta nu t

/-- The derivative-at-zero boundary contribution is retained.
-/
def energy (k : ℕ) (beta m : ℝ) (nu : Trial) : ℝ≥0∞ :=
  (∫⁻ t in Ico (0 : ℝ) 1,
    ENNReal.ofReal (deriv (deriv (Scalar.xiSlice k m)) t * profile beta nu t)) +
    ENNReal.ofReal (deriv (Scalar.xiSlice k m) 0 * profile beta nu 0)

def rawFunctional (k : ℕ) (beta m : ℝ) (nu : Trial) : ℝ≥0∞ :=
  energy k beta m nu + entropy beta nu

/-- The complete extended infimum, without a supplied minimizer. -/
def rawValue (k : ℕ) (beta m : ℝ) : ℝ≥0∞ :=
  sInf (range (rawFunctional k beta m))

def diracTrial (q : Overlap) : Trial := ⟨Measure.dirac q, inferInstance⟩

theorem isCompact_trials : IsCompact (univ : Set Trial) := isCompact_univ

theorem continuous_profile_eval (beta t : ℝ) :
    Continuous (fun nu : Trial => profile beta nu t) :=
  continuous_const.mul (ProbabilityMeasure.continuous_integral_continuousMap (kernel t))

theorem profile_dirac (beta t : ℝ) (q : Overlap) :
    profile beta (diracTrial q) t = beta * (1 - max t (q : ℝ)) := by
  simp [profile, diracTrial, kernel]

theorem profile_one (beta : ℝ) (nu : Trial) : profile beta nu 1 = 0 := by
  have heq : kernel (1 : ℝ) = (0 : C(Overlap, ℝ)) := by
    ext q
    simp only [kernel, ContinuousMap.coe_mk, ContinuousMap.coe_zero, Pi.zero_apply,
      max_eq_left q.property.2, sub_self]
  simp only [profile, heq, ContinuousMap.coe_zero, Pi.zero_apply, integral_zero, mul_zero]

theorem entropy_dirac_zero (beta : ℝ) :
    entropy beta (diracTrial ⟨0, by norm_num⟩) = 0 := by
  unfold entropy
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  simp only [entropyExcess, profile_dirac, max_eq_left ht.1, tsub_self, Pi.zero_apply]

end
end TensorPCA.NonRSLowerProofs.FiniteCS
