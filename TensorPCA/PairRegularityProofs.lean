-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairGibbsProofs

/-! Positive-window regularity for the literal constrained thermal partition. -/
@[expose] public section
namespace TensorPCA.PairRegularityProofs
open Set MeasureTheory ProbabilityTheory ThermalReplicaProofs FreeEnergyProofs PairGibbsProofs
open scoped ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pairWindowLaw (N : ℕ) (u eta : ℝ) : Measure (Model.Vector N × Model.Vector N) :=
  ((Model.spherePrior N).prod (Model.spherePrior N)).restrict (Coupled.pairWindow N u eta)

instance pairWindowLaw_isFiniteMeasure (N : ℕ) (u eta : ℝ) :
    IsFiniteMeasure (pairWindowLaw N u eta) := by
  unfold pairWindowLaw
  infer_instance

def pairLinear (N k : ℕ) (xy : Model.Vector N × Model.Vector N) :
    Model.Tensor N k →L[ℝ] ℝ := thermalLinear N k 1 xy.1+thermalLinear N k 1 xy.2

theorem pairLinear_continuous (N k : ℕ) : Continuous (pairLinear N k) :=
  ((thermalLinear_continuous N k 1).comp continuous_fst).add
    ((thermalLinear_continuous N k 1).comp continuous_snd)

theorem pairLinear_apply (N k : ℕ) (lam : ℝ) (xy : Model.Vector N × Model.Vector N)
    (w : Model.Tensor N k) :
    pairLinear N k xy (lam • w) =
      -lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2) := by
  simp only [pairLinear, ContinuousLinearMap.add_apply, thermalLinear_base_apply]
  ring

theorem pairLinear_bound {N k : ℕ} (hN : 0 < N) (u eta : ℝ) :
    ∀ᵐ xy ∂pairWindowLaw N u eta, ‖pairLinear N k xy‖ ≤ 2*Real.sqrt N := by
  apply ae_restrict_of_ae
  apply (Measure.ae_prod_iff_ae_ae (isClosed_le (pairLinear_continuous N k).norm
    continuous_const).measurableSet).mpr
  filter_upwards [base_bound (k := k) hN] with x hx
  filter_upwards [base_bound (k := k) hN] with y hy
  exact (norm_add_le _ _).trans (by linarith)

theorem pairPartition_eq_moment (N k : ℕ) (lam u eta : ℝ) (w : Model.Tensor N k) :
    Coupled.pairPartition N k lam u eta w =
      GaussianSpinInterpolation.moment (pairWindowLaw N u eta) (fun _ ↦ 1)
        (pairLinear N k) (lam • w) := by
  unfold Coupled.pairPartition pairWindowLaw GaussianSpinInterpolation.moment
    GaussianSpinInterpolation.weight
  rw [integral_indicator (pairWindow_measurableSet N u eta)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xy ↦ by simp only [one_mul, pairLinear_apply])

theorem pairWindowLaw_neZero (N : ℕ) (u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) : NeZero (pairWindowLaw N u eta) := by
  constructor
  intro h
  exact hm (Measure.restrict_eq_zero.mp h)

theorem pairPartition_pos {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (w : Model.Tensor N k) :
    0 < Coupled.pairPartition N k lam u eta w := by
  letI := pairWindowLaw_neZero N u eta hm
  rw [pairPartition_eq_moment]
  exact GaussianSpinInterpolation.moment_one_pos (pairWindowLaw N u eta) (pairLinear N k)
    (pairLinear_continuous N k).measurable (pairLinear_bound hN u eta) (lam • w)

theorem pairPartition_log_abs_le {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (w : Model.Tensor N k) :
    |Real.log (Coupled.pairPartition N k lam u eta w)| ≤
      |Real.log ((pairWindowLaw N u eta).real univ)|+
        (2*Real.sqrt N*|lam|)*‖w‖ := by
  let ν := pairWindowLaw N u eta
  letI := pairWindowLaw_neZero N u eta hm
  let A := (2*Real.sqrt N)*‖lam • w‖
  have hb := pairLinear_bound (k := k) hN u eta
  have hv : ∀ᵐ xy ∂ν, |pairLinear N k xy (lam • w)| ≤ A := by
    filter_upwards [hb] with xy hxy
    exact ((pairLinear N k xy).le_opNorm (lam • w)).trans
      (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
  have hi : Integrable (fun xy ↦ Real.exp (pairLinear N k xy (lam • w))) ν := by
    have H := GaussianSpinInterpolation.weight_integrable ν (fun _ ↦ 1) (pairLinear N k)
        measurable_const (pairLinear_continuous N k).measurable
          (hb.mono (fun xy hxy ↦ ⟨by norm_num, hxy⟩) :
            ∀ᵐ xy ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖pairLinear N k xy‖ ≤ 2*Real.sqrt N) (lam • w)
    unfold GaussianSpinInterpolation.weight at H
    simpa only [one_mul] using H
  have hlo := integral_mono_ae (integrable_const (Real.exp (-A))) hi
    (hv.mono (fun xy hxy ↦ Real.exp_le_exp.mpr (abs_le.mp hxy).1))
  have hhi := integral_mono_ae hi (integrable_const (Real.exp A))
    (hv.mono (fun xy hxy ↦ Real.exp_le_exp.mpr (abs_le.mp hxy).2))
  simp only [integral_const, smul_eq_mul] at hlo hhi
  have heq := pairPartition_eq_moment N k lam u eta w
  simp only [GaussianSpinInterpolation.moment, GaussianSpinInterpolation.weight, one_mul] at heq
  rw [← heq] at hlo hhi
  have hlolog := Real.log_le_log (mul_pos (measureReal_univ_pos (μ := ν)) (Real.exp_pos (-A))) hlo
  have hhilog := Real.log_le_log (pairPartition_pos hN lam u eta hm w) hhi
  rw [Real.log_mul (measureReal_univ_pos (μ := ν)).ne' (Real.exp_pos (-A)).ne',
    Real.log_exp] at hlolog
  rw [Real.log_mul (measureReal_univ_pos (μ := ν)).ne' (Real.exp_pos A).ne',
    Real.log_exp] at hhilog
  have H : |Real.log (Coupled.pairPartition N k lam u eta w)| ≤
      |Real.log (ν.real univ)|+A := abs_le.mpr ⟨by
    linarith [neg_abs_le (Real.log (ν.real univ))], by
    linarith [le_abs_self (Real.log (ν.real univ))]⟩
  simpa only [A, norm_smul, Real.norm_eq_abs, mul_assoc] using H

theorem log_pairPartition_continuous {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) :
    Continuous (fun w ↦ Real.log (Coupled.pairPartition N k lam u eta w)) := by
  letI := pairWindowLaw_neZero N u eta hm
  have heq : (fun w ↦ Real.log (Coupled.pairPartition N k lam u eta w)) =
      (fun w ↦ GaussianSpinInterpolation.logPartition (pairWindowLaw N u eta)
        (pairLinear N k) (lam • w)) := by
    funext w
    rw [pairPartition_eq_moment]
    rfl
  rw [heq]
  exact (GaussianSpinInterpolation.logPartition_contDiff (pairWindowLaw N u eta)
    (pairLinear N k) (pairLinear_continuous N k).measurable
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (pairLinear_bound hN u eta)).continuous.comp
        (continuous_const_smul lam)

theorem log_pairPartition_memLp {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w ↦ Real.log (Coupled.pairPartition N k lam u eta w)) p
      (Model.noiseLaw N k) := by
  have hc : MemLp (fun _ : Model.Tensor N k ↦
      |Real.log ((pairWindowLaw N u eta).real univ)|) p (Model.noiseLaw N k) := memLp_const _
  have hn := ((IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) p hp).norm).const_smul
    (2*Real.sqrt N*|lam|)
  apply (hc.add hn).mono' (log_pairPartition_continuous hN lam u eta hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w ↦ by
    simpa only [Real.norm_eq_abs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq] using
      pairPartition_log_abs_le hN lam u eta hm w)

theorem positiveWindowRegularity : Coupled.PositiveWindowRegularity := by
  intro N k hN lam u eta _hlam _hu _heta hm
  have hNp : 0 < N := by omega
  refine ⟨pairPartition_pos hNp lam u eta hm, ?_⟩
  exact ((log_pairPartition_memLp hNp lam u eta hm 1 (by norm_num)).integrable le_rfl).div_const _

end
end TensorPCA.PairRegularityProofs
