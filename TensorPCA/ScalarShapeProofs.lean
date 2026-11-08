-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarPhiProofs

/-! Remaining local-shape assertions in the scalar classification lemma. -/
@[expose] public section
namespace TensorPCA.ScalarShapeProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs ScalarPhiProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem beta_le_turningPoint (k : ℕ) (hk : 3 ≤ k) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    beta k q ≤ beta k (turningPoint k) := by
  have ht := turningPoint_mem_Ioo k hk
  by_cases hle : q ≤ turningPoint k
  · exact (strictMonoOn_beta_left k hk).monotoneOn ⟨hq.1, hle⟩ ⟨ht.1.le, le_rfl⟩ hle
  · have hge := (lt_of_not_ge hle).le
    exact (strictAntiOn_beta_right k hk).antitoneOn ⟨le_rfl, ht.2.le⟩ ⟨hge, hq.2⟩ hge

theorem phi_deriv_factor_pos (k : ℕ) (hk : 3 ≤ k) {lam q : ℝ}
    (hlam : 0 < lam) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < (k : ℝ)*((k : ℝ)-1)*lam^2*q^(k-2) /
      (1+lam^2*(k : ℝ)*q^(k-1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkm : 0 < (k : ℝ)-1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hq0 := hq.1
  positivity

theorem deriv_neg_of_beta_lt (k : ℕ) (hk : 3 ≤ k) {lam q : ℝ}
    (hlam : 0 < lam) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hb : ((k : ℝ)*lam^2)*beta k q < 1) :
    deriv (Scalar.f k lam) q < 0 ∧ deriv (Scalar.phi k lam) q < 0 := by
  have hh : q*(((k : ℝ)*lam^2)*beta k q-1) < 0 :=
    mul_neg_of_pos_of_neg hq.1 (sub_neg.mpr hb)
  rw [(hasDerivAt_f k hk lam hq.2).deriv, (hasDerivAt_phi k hk lam hq.1.le).deriv]
  exact ⟨div_neg_of_neg_of_pos hh (sub_pos.mpr hq.2),
    mul_neg_of_pos_of_neg (phi_deriv_factor_pos k hk hlam hq) hh⟩

theorem deriv_pos_of_beta_gt (k : ℕ) (hk : 3 ≤ k) {lam q : ℝ}
    (hlam : 0 < lam) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hb : 1 < ((k : ℝ)*lam^2)*beta k q) :
    0 < deriv (Scalar.f k lam) q ∧ 0 < deriv (Scalar.phi k lam) q := by
  have hh : 0 < q*(((k : ℝ)*lam^2)*beta k q-1) :=
    mul_pos hq.1 (sub_pos.mpr hb)
  rw [(hasDerivAt_f k hk lam hq.2).deriv, (hasDerivAt_phi k hk lam hq.1.le).deriv]
  exact ⟨div_pos hh (sub_pos.mpr hq.2), mul_pos (phi_deriv_factor_pos k hk hlam hq) hh⟩

/-- Both actual scalar potentials strictly decrease below the spinodal. -/
theorem subspinodal_strictAnti (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : 0 < lam) (hsub : lam < Scalar.lambdaS k) :
    StrictAntiOn (Scalar.f k lam) (Ico (0 : ℝ) 1) ∧
      StrictAntiOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ht := turningPoint_mem_Ioo k hk
  have hBt : 0 < beta k (turningPoint k) := mul_pos (pow_pos ht.1 _) (sub_pos.mpr ht.2)
  have hsq := (sq_lt_sq₀ hlam.le (lambdaS_pos k hk).le).mpr hsub
  rw [lambdaS_sq k hk] at hsq
  have hbound : ((k : ℝ)*lam^2)*beta k (turningPoint k) < 1 := by
    have hh := (lt_div_iff₀ (mul_pos hk0 hBt)).mp hsq
    nlinarith
  have hneg (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) := deriv_neg_of_beta_lt k hk hlam hq
    ((mul_le_mul_of_nonneg_left (beta_le_turningPoint k hk ⟨hq.1.le, hq.2.le⟩)
      (mul_nonneg hk0.le (sq_nonneg lam))).trans_lt hbound)
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
      ((continuousOn_f k hk lam).mono (fun q hq => hq.2))
    intro q hq
    have hq' : q ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using hq
    exact (hneg q hq').1
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_phi k hk lam)
    intro q hq
    have hq' : q ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hq
    exact (hneg q hq').2

theorem phi_stationary_monotonicity (k : ℕ) (hk : 3 ≤ k) {lam u : ℝ}
    (hlam : Scalar.lambdaS k < lam) (hu : u ∈ Ioo (0 : ℝ) (turningPoint k))
    (hueq : ((k : ℝ)*lam^2)*beta k u = 1) :
    StrictAntiOn (Scalar.phi k lam) (Icc (0 : ℝ) u) ∧
    StrictMonoOn (Scalar.phi k lam) (Icc u (Scalar.qS k lam)) ∧
    StrictAntiOn (Scalar.phi k lam) (Icc (Scalar.qS k lam) 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hcoeff : 0 < (k : ℝ)*lam^2 := mul_pos hk0 (sq_pos_of_pos hlam0)
  have ht := turningPoint_mem_Ioo k hk
  have hs := (qS_spec k hk hlam).1
  have hseq : ((k : ℝ)*lam^2)*beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using hs.2
  refine ⟨?_, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuousOn_phi k hk lam).mono (fun q hq => ⟨hq.1, hq.2.trans (hu.2.trans ht.2).le⟩))
    intro q hq
    have hq' : 0 < q ∧ q < u := by simpa only [interior_Icc, mem_Ioo] using hq
    have hb := (strictMonoOn_beta_left k hk) ⟨hq'.1.le, (hq'.2.trans hu.2).le⟩
      ⟨hu.1.le, hu.2.le⟩ hq'.2
    apply (deriv_neg_of_beta_lt k hk hlam0 ⟨hq'.1, hq'.2.trans (hu.2.trans ht.2)⟩ ?_).2
    have hh := mul_lt_mul_of_pos_left hb hcoeff
    simpa only [hueq] using hh
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_phi k hk lam).mono (fun q hq => ⟨hu.1.le.trans hq.1, hq.2.trans hs.1.2.le⟩))
    intro q hq
    have hq' : u < q ∧ q < Scalar.qS k lam := by simpa only [interior_Icc, mem_Ioo] using hq
    apply (deriv_pos_of_beta_gt k hk hlam0 ⟨hu.1.trans hq'.1, hq'.2.trans hs.1.2⟩ ?_).2
    by_cases hqt : q ≤ turningPoint k
    · have hb := (strictMonoOn_beta_left k hk) ⟨hu.1.le, hu.2.le⟩
        ⟨(hu.1.trans hq'.1).le, hqt⟩ hq'.1
      have hh := mul_lt_mul_of_pos_left hb hcoeff
      simpa only [hueq] using hh
    · have hb := (strictAntiOn_beta_right k hk)
        ⟨(lt_of_not_ge hqt).le, (hq'.2.trans hs.1.2).le⟩ ⟨hs.1.1.le, hs.1.2.le⟩ hq'.2
      have hh := mul_lt_mul_of_pos_left hb hcoeff
      simpa only [hseq] using hh
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuousOn_phi k hk lam).mono (fun q hq =>
        ⟨((ht.1.trans hs.1.1).le.trans hq.1), hq.2⟩))
    intro q hq
    have hq' : Scalar.qS k lam < q ∧ q < 1 := by simpa only [interior_Icc, mem_Ioo] using hq
    have hb := (strictAntiOn_beta_right k hk) ⟨hs.1.1.le, hs.1.2.le⟩
      ⟨(hs.1.1.trans hq'.1).le, hq'.2.le⟩ hq'.1
    apply (deriv_neg_of_beta_lt k hk hlam0 ⟨ht.1.trans (hs.1.1.trans hq'.1), hq'.2⟩ ?_).2
    have hh := mul_lt_mul_of_pos_left hb hcoeff
    simpa only [hseq] using hh

theorem qS_self_consistency (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    Scalar.qS k lam = lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1) /
      (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1)) := by
  have hs := (qS_spec k hk hlam).1
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans hs.1.1
  have hD : 1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1) ≠ 0 := ne_of_gt (by positivity)
  have hp : (Scalar.qS k lam)^(k-1) = (Scalar.qS k lam)^(k-2)*Scalar.qS k lam := by
    rw [← pow_succ]
    congr 1
    omega
  apply (eq_div_iff hD).mpr
  rw [hp]
  nlinarith [congrArg (fun x : ℝ => x*Scalar.qS k lam) hs.2]

/-- Three strict monotonicity intervals certify the interior valley and peak
by explicit strict inequalities throughout a neighborhood of each point. -/
theorem strict_local_extrema_of_shape {F : ℝ → ℝ} {u s : ℝ}
    (hu : 0 < u) (hus : u < s) (hs : s < 1)
    (hleft : StrictAntiOn F (Icc (0 : ℝ) u))
    (hmiddle : StrictMonoOn F (Icc u s)) (hright : StrictAntiOn F (Ico s 1)) :
    (∀ᶠ q in 𝓝 u, q ≠ u → F u < F q) ∧
      (∀ᶠ q in 𝓝 s, q ≠ s → F q < F s) := by
  constructor
  · filter_upwards [Ioo_mem_nhds hu hus] with q hq
    intro hne
    by_cases hqu : q < u
    · exact hleft ⟨hq.1.le, hqu.le⟩ ⟨hu.le, le_rfl⟩ hqu
    · have huq : u < q := lt_of_le_of_ne (le_of_not_gt hqu) (Ne.symm hne)
      exact hmiddle ⟨le_rfl, hus.le⟩ ⟨huq.le, hq.2.le⟩ huq
  · filter_upwards [Ioo_mem_nhds hus hs] with q hq
    intro hne
    by_cases hqs : q < s
    · exact hmiddle ⟨hq.1.le, hqs.le⟩ ⟨hus.le, le_rfl⟩ hqs
    · have hsq : s < q := lt_of_le_of_ne (le_of_not_gt hqs) (Ne.symm hne)
      exact hright ⟨le_rfl, hs⟩ ⟨hsq.le, hq.2⟩ hsq

/-- Literal shared strict local minimum/maximum assertion of Lemma A.4. -/
theorem stationary_local_extrema (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    ∃ u ∈ Ioo (0 : ℝ) (turningPoint k), ((k : ℝ)*lam^2)*beta k u = 1 ∧
      (∀ᶠ q in 𝓝 u, q ≠ u →
        Scalar.f k lam u < Scalar.f k lam q ∧ Scalar.phi k lam u < Scalar.phi k lam q) ∧
      (∀ᶠ q in 𝓝 (Scalar.qS k lam), q ≠ Scalar.qS k lam →
        Scalar.f k lam q < Scalar.f k lam (Scalar.qS k lam) ∧
          Scalar.phi k lam q < Scalar.phi k lam (Scalar.qS k lam)) := by
  obtain ⟨u, hu, hueq⟩ := exists_unstableStationaryPoint k hk hlam
  have hs := (qS_spec k hk hlam).1
  have hus := hu.2.trans hs.1.1
  obtain ⟨hfl, hfm, hfr⟩ := f_stationary_monotonicity k hk hlam hu hueq
  obtain ⟨hpl, hpm, hpr⟩ := phi_stationary_monotonicity k hk hlam hu hueq
  obtain ⟨hfu, hfs⟩ := strict_local_extrema_of_shape hu.1 hus hs.1.2 hfl hfm hfr
  obtain ⟨hpu, hps⟩ := strict_local_extrema_of_shape hu.1 hus hs.1.2 hpl hpm
    (hpr.mono (fun q hq => ⟨hq.1, hq.2.le⟩))
  refine ⟨u, hu, hueq, ?_, ?_⟩
  · filter_upwards [hfu, hpu] with q hf hp
    intro hne
    exact ⟨hf hne, hp hne⟩
  · filter_upwards [hfs, hps] with q hf hp
    intro hne
    exact ⟨hf hne, hp hne⟩

end
end TensorPCA.ScalarShapeProofs
