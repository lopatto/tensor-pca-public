-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSFiniteness

/-! Finite entropy forces strict positivity at every overlap below one, not merely
almost everywhere. The antitonicity of the integrated CDF is what upgrades finite
extended reciprocal cost to a pointwise statement.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem profile_bounds {beta : ℝ} (hbeta : 0 ≤ beta) (nu : Trial)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ profile beta nu t ∧ profile beta nu t ≤ beta * (1 - t) :=
  scaled_hatCDF_bounds (nu : Measure Overlap) hbeta ht

theorem profile_antitone {beta : ℝ} (hbeta : 0 ≤ beta) (nu : Trial) :
    Antitone (profile beta nu) :=
  scaled_hatCDF_antitone (nu : Measure Overlap) hbeta

theorem entropyExcess_eq_top_of_profile_zero {beta t : ℝ} (hbeta : 0 < beta)
    (nu : Trial) (ht : t < 1) (hp : profile beta nu t = 0) :
    entropyExcess beta nu t = ∞ := by
  have hb : ENNReal.ofReal (beta * (1 - t)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (mul_pos hbeta (sub_pos.mpr ht))).ne'
  have hi : (ENNReal.ofReal (beta * (1 - t)))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hb
  simp [entropyExcess, hp, hi]

theorem profile_pos_of_entropy_ne_top {beta : ℝ} (hbeta : 0 < beta) (nu : Trial)
    (hfinite : entropy beta nu ≠ ∞) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    0 < profile beta nu t := by
  have hn := (profile_bounds hbeta.le nu ⟨ht.1, ht.2.le⟩).1
  by_contra hpos
  have hp : profile beta nu t = 0 := le_antisymm (le_of_not_gt hpos) hn
  have hz : volume {u ∈ Ico (0 : ℝ) 1 | entropyExcess beta nu u = ∞} = 0 :=
    measure_eq_top_of_setLIntegral_ne_top (entropyExcess_measurable beta nu).aemeasurable hfinite
  have hsub : Ioo t 1 ⊆ {u ∈ Ico (0 : ℝ) 1 | entropyExcess beta nu u = ∞} := by
    intro u hu
    refine ⟨⟨ht.1.trans hu.1.le, hu.2⟩, ?_⟩
    have hpu : profile beta nu u = 0 := le_antisymm
      ((profile_antitone hbeta.le nu hu.1.le).trans hp.le)
      (profile_bounds hbeta.le nu ⟨ht.1.trans hu.1.le, hu.2.le⟩).1
    exact entropyExcess_eq_top_of_profile_zero hbeta nu hu.2 hpu
  have hh : volume (Ioo t 1) ≤
      volume {u ∈ Ico (0 : ℝ) 1 | entropyExcess beta nu u = ∞} := measure_mono hsub
  rw [hz] at hh
  have hpositive : 0 < volume (Ioo t 1) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr ht.2)
  exact (not_le_of_gt hpositive) hh

theorem profile_pos_of_rawFunctional_ne_top (k : ℕ) {beta : ℝ} (hbeta : 0 < beta)
    (m : ℝ) (nu : Trial) (hfinite : rawFunctional k beta m nu ≠ ∞)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : 0 < profile beta nu t := by
  apply profile_pos_of_entropy_ne_top hbeta nu _ ht
  exact (ENNReal.add_ne_top.mp hfinite).2

end
end TensorPCA.NonRSLowerProofs.FiniteCS
