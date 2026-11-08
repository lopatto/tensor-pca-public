-- SPDX-License-Identifier: Apache-2.0
/- Attributed actual semicircle clipping proof adapted from
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/SemicircleClipping.lean. The exact clipped-log definitions,
   domination and pointwise DCT argument are retained. Direct compact-support
   integrability and an explicit compact directed-cover argument replace broad
   Jacobi and Dini imports. No empirical spectral convergence is assumed.
   See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SpectralTraceLipschitz
public import TensorPCA.RetainedCountProofs.SemicircleInsidePotential
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SemicircleClipping
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SemicirclePotential SpectralTraceLipschitz
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

def clippedPotential (k rho : ℝ) : ℝ := ∫ t, clippedLog k rho t ∂SemicirclePotential.law

lemma clippedLog_integrable (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (clippedLog k rho) SemicirclePotential.law := by
  have hi : IntegrableOn (clippedLog k rho) (Icc (-2 : ℝ) 2) SemicirclePotential.law :=
    (clippedLog_lipschitz k hrho).continuous.integrableOn_Icc
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr law_supported)] at hi
  exact hi

lemma clippedPotential_lipschitz {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith ⟨1/rho, by positivity⟩ (fun k => clippedPotential k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro k l
  rw [Real.dist_eq]
  change ‖clippedPotential k rho-clippedPotential l rho‖ ≤ (1/rho)*|k-l|
  unfold clippedPotential
  rw [← integral_sub (clippedLog_integrable k hrho) (clippedLog_integrable l hrho)]
  have h := norm_integral_le_of_norm_le_const (μ := SemicirclePotential.law)
    (f := fun t => clippedLog k rho t-clippedLog l rho t)
    (C := (1/rho)*|k-l|) (ae_of_all _ fun t => by
      have ht := (clippedLog_lipschitz t hrho).dist_le_mul k l
      change |clippedLog t rho k-clippedLog t rho l| ≤ (1/rho)*|k-l| at ht
      simpa only [Real.norm_eq_abs, clippedLog, abs_sub_comm t k,
        abs_sub_comm t l] using ht)
  simpa only [probReal_univ, mul_one] using h

lemma clippedPotential_continuous {rho : ℝ} (hrho : 0 < rho) :
    Continuous (fun k => clippedPotential k rho) :=
  (clippedPotential_lipschitz hrho).continuous

lemma log_clipped_abs_le {d rho : ℝ} (hd : 0<d) (hrho : 0<rho) (hrho1 : rho≤1) :
    |Real.log (max d rho)|≤|Real.log d| := by
  by_cases h : rho≤d
  · rw [max_eq_left h]
  · have hdr : d<rho := lt_of_not_ge h
    rw [max_eq_right hdr.le]
    have hld : Real.log d≤0 := Real.log_nonpos hd.le (hdr.le.trans hrho1)
    have hlr : Real.log rho≤0 := Real.log_nonpos hrho.le hrho1
    rw [abs_of_nonpos hld,abs_of_nonpos hlr]
    exact neg_le_neg (Real.log_le_log hd hdr.le)

def clippingRadius (n : ℕ) : ℝ := 1/(n+1 : ℝ)

lemma clippingRadius_pos (n : ℕ) : 0<clippingRadius n := by unfold clippingRadius;positivity
lemma clippingRadius_le_one (n : ℕ) : clippingRadius n≤1 := by
  unfold clippingRadius
  apply (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mpr
  norm_num
lemma clippingRadius_tendsto : Tendsto clippingRadius atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  exact hn.const_div_atTop 1

lemma clippingRadius_antitone : Antitone clippingRadius := by
  intro n m hnm
  unfold clippingRadius
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

lemma scalar_clipping_limit (k t : ℝ) (hkt : k≠t) :
    Tendsto (fun n => clippedLog k (clippingRadius n) t) atTop (𝓝 (Real.log |k-t|)) := by
  unfold clippedLog
  have hd : |k-t|≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr hkt)
  have hm := (tendsto_const_nhds (x := |k-t|)).max clippingRadius_tendsto
  have hm' : Tendsto (fun n => max |k-t| (clippingRadius n)) atTop (𝓝 |k-t|) := by
    simpa only [show max |k-t| (0:ℝ)=|k-t| from max_eq_left (abs_nonneg (k-t))] using hm
  exact Real.continuousAt_log hd |>.tendsto.comp hm'

lemma clippedPotential_tendsto (k : ℝ) :
    Tendsto (fun n => clippedPotential k (clippingRadius n)) atTop (𝓝 (potential k)) := by
  let _ : NullSingletonClass SemicirclePotential.law := by
    unfold SemicirclePotential.law
    infer_instance
  have hae : ∀ᵐ t ∂SemicirclePotential.law,k≠t := by
    simpa only [ne_comm] using SemicirclePotential.law.ae_ne k
  have hmeas (n : ℕ) : AEStronglyMeasurable (clippedLog k (clippingRadius n)) SemicirclePotential.law :=
    (clippedLog_lipschitz k (clippingRadius_pos n)).continuous.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t ∂SemicirclePotential.law,
      ‖clippedLog k (clippingRadius n) t‖≤|Real.log (|k-t|)| := by
    filter_upwards [hae] with t ht
    exact log_clipped_abs_le (abs_pos.mpr (sub_ne_zero.mpr ht))
      (clippingRadius_pos n) (clippingRadius_le_one n)
  have hlim : ∀ᵐ t ∂SemicirclePotential.law,
      Tendsto (fun n => clippedLog k (clippingRadius n) t) atTop (𝓝 (Real.log |k-t|)) := by
    filter_upwards [hae] with t ht
    exact scalar_clipping_limit k t ht
  rw [← integralPotential_eq_potential k]
  exact tendsto_integral_of_dominated_convergence _ hmeas (log_abs_integrable k).abs hbound hlim

lemma clippedPotential_antitone (k : ℝ) : Antitone (fun n => clippedPotential k (clippingRadius n)) := by
  intro n m hnm
  exact integral_mono (clippedLog_integrable k (clippingRadius_pos m))
    (clippedLog_integrable k (clippingRadius_pos n)) fun t =>
      Real.log_le_log (lt_of_lt_of_le (clippingRadius_pos m) (le_max_right _ _))
        (max_le_max le_rfl (clippingRadius_antitone hnm))

lemma potential_le_clippedPotential (k : ℝ) (n : ℕ) :
    potential k ≤ clippedPotential k (clippingRadius n) := by
  apply le_of_tendsto (clippedPotential_tendsto k)
  filter_upwards [eventually_ge_atTop n] with m hnm
  exact clippedPotential_antitone k hnm

/-- Genuine removal of clipping, uniform on every compact set of real shifts. -/
theorem clippedPotential_uniform_on_compact {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n k => clippedPotential k (clippingRadius n)) potential atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let U : ℕ → Set ℝ := fun n => {k | clippedPotential k (clippingRadius n) < potential k+ε}
  have hUo (n : ℕ) : IsOpen (U n) :=
    isOpen_lt (clippedPotential_continuous (clippingRadius_pos n))
      (potential_continuous.add continuous_const)
  have hsU : S ⊆ ⋃ n, U n := by
    intro k hk
    obtain ⟨n, hn⟩ := ((clippedPotential_tendsto k).eventually
      (gt_mem_nhds (lt_add_of_pos_right (potential k) hε))).exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hUd : Directed (· ⊆ ·) U := by
    intro n m
    refine ⟨max n m, ?_, ?_⟩
    · intro k hk
      exact lt_of_le_of_lt (clippedPotential_antitone k (le_max_left n m)) hk
    · intro k hk
      exact lt_of_le_of_lt (clippedPotential_antitone k (le_max_right n m)) hk
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo hsU hUd
  filter_upwards [eventually_ge_atTop n] with m hnm
  intro k hk
  have hupper : clippedPotential k (clippingRadius m) < potential k+ε :=
    lt_of_le_of_lt (clippedPotential_antitone k hnm) (hn hk)
  rw [Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (potential_le_clippedPotential k m))]
  linarith

end
end TensorPCA.RetainedCountProofs.SemicircleClipping
