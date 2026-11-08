-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarSelectionProofs

/-! Continuity and differential calculus of the stable stationary branch. -/
@[expose] public section
namespace TensorPCA.ScalarBranchProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def stationaryStrength (k : ℕ) (q : ℝ) : ℝ := Real.sqrt (1/((k : ℝ)*beta k q))

theorem stationaryStrength_spec (k : ℕ) (hk : 3 ≤ k) {q : ℝ}
    (hq : q ∈ Ioo (turningPoint k) 1) :
    Scalar.lambdaS k < stationaryStrength k q ∧
      Scalar.StableStationaryPoint k (stationaryStrength k q) q := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ht := turningPoint_mem_Ioo k hk
  have hq0 := ht.1.trans hq.1
  have hBq : 0 < beta k q := mul_pos (pow_pos hq0 _) (sub_pos.mpr hq.2)
  have hBt : 0 < beta k (turningPoint k) :=
    mul_pos (pow_pos ht.1 _) (sub_pos.mpr ht.2)
  have hsq : (stationaryStrength k q)^2 = 1/((k : ℝ)*beta k q) :=
    Real.sq_sqrt (one_div_pos.mpr (mul_pos hk0 hBq)).le
  have hnonneg : 0 ≤ stationaryStrength k q := Real.sqrt_nonneg _
  have hlt : Scalar.lambdaS k < stationaryStrength k q := by
    apply (sq_lt_sq₀ (lambdaS_pos k hk).le hnonneg).mp
    rw [lambdaS_sq k hk, hsq]
    apply (div_lt_div_iff₀ (mul_pos hk0 hBt) (mul_pos hk0 hBq)).mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_left
      ((strictAntiOn_beta_right k hk) ⟨le_rfl, ht.2.le⟩ ⟨hq.1.le, hq.2.le⟩ hq.1) hk0
  refine ⟨hlt, hq, ?_⟩
  have heq : ((k : ℝ)*(stationaryStrength k q)^2)*beta k q = 1 := by
    rw [hsq]
    field_simp [hk0.ne', hBq.ne']
  simpa only [beta, mul_assoc] using heq

theorem beta_qS (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    beta k (Scalar.qS k lam) = 1/((k : ℝ)*lam^2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hs := (qS_spec k hk hlam).1
  have heq : ((k : ℝ)*lam^2)*beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using hs.2
  apply (eq_div_iff (mul_pos hk0 (sq_pos_of_pos hlam0)).ne').mpr
  simpa only [mul_comm] using heq

theorem strictMonoOn_qS (k : ℕ) (hk : 3 ≤ k) :
    StrictMonoOn (Scalar.qS k) (Ioi (Scalar.lambdaS k)) := by
  intro lam hlam mu hmu hlt
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hmu0 := (lambdaS_pos k hk).trans hmu
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := (qS_spec k hk hlam).1
  have ht := (qS_spec k hk hmu).1
  have hsq : lam^2 < mu^2 := (sq_lt_sq₀ hlam0.le hmu0.le).mpr hlt
  have hb : beta k (Scalar.qS k mu) < beta k (Scalar.qS k lam) := by
    rw [beta_qS k hk hmu, beta_qS k hk hlam]
    apply (div_lt_div_iff₀ (mul_pos hk0 (sq_pos_of_pos hmu0))
      (mul_pos hk0 (sq_pos_of_pos hlam0))).mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_left hsq hk0
  by_contra hn
  have hle : Scalar.qS k mu ≤ Scalar.qS k lam := le_of_not_gt hn
  have ha := (strictAntiOn_beta_right k hk).antitoneOn
    ⟨ht.1.1.le, ht.1.2.le⟩ ⟨hs.1.1.le, hs.1.2.le⟩ hle
  exact (not_le_of_gt hb) ha

theorem image_qS (k : ℕ) (hk : 3 ≤ k) :
    Scalar.qS k '' Ioi (Scalar.lambdaS k) = Ioo (turningPoint k) 1 := by
  ext q
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    exact (qS_spec k hk hlam).1.1
  · intro hq
    have hs := stationaryStrength_spec k hk hq
    refine ⟨stationaryStrength k q, hs.1, ?_⟩
    exact ((qS_spec k hk hs.1).2 q hs.2).symm

theorem continuousAt_qS (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) : ContinuousAt (Scalar.qS k) lam := by
  apply (strictMonoOn_qS k hk).continuousAt_of_image_mem_nhds (Ioi_mem_nhds hlam)
  rw [image_qS k hk]
  exact isOpen_Ioo.mem_nhds (qS_spec k hk hlam).1.1

theorem betaDeriv_qS_neg (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    (Scalar.qS k lam)^(k-3)*((k : ℝ)-2-((k : ℝ)-1)*Scalar.qS k lam) < 0 := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hs := (qS_spec k hk hlam).1
  have hpos := (turningPoint_mem_Ioo k hk).1.trans hs.1.1
  have hlinear : (k : ℝ)-2-((k : ℝ)-1)*Scalar.qS k lam < 0 := by
    have hh := (div_lt_iff₀ (by linarith : 0 < (k : ℝ)-1)).mp hs.1.1
    nlinarith
  exact mul_neg_of_pos_of_neg (pow_pos hpos _) hlinear

theorem hasDerivAt_qS_raw (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    HasDerivAt (Scalar.qS k)
      ((-2/((k : ℝ)*lam^3)) /
        ((Scalar.qS k lam)^(k-3)*((k : ℝ)-2-((k : ℝ)-1)*Scalar.qS k lam))) lam := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hcoeff : (k : ℝ)*lam^2 ≠ 0 := (mul_pos hk0 (sq_pos_of_pos hlam0)).ne'
  have htarget : HasDerivAt (fun mu : ℝ => 1/((k : ℝ)*mu^2))
      (-2/((k : ℝ)*lam^3)) lam := by
    convert (hasDerivAt_const lam (1 : ℝ)).div
      (((hasDerivAt_id lam).pow 2).const_mul (k : ℝ)) hcoeff using 1
    · funext mu
      rfl
    · dsimp
      field_simp [hk0.ne', hlam0.ne']
      ring
  apply HasDerivAt.of_comp_left (continuousAt_qS k hk hlam)
    (hasDerivAt_beta k hk _) htarget (ne_of_lt (betaDeriv_qS_neg k hk hlam))
  filter_upwards [Ioi_mem_nhds hlam] with mu hmu
  exact beta_qS k hk hmu

/-- The exact scalar derivative from the manuscript, with positive denominator. -/
theorem hasDerivAt_qS (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    HasDerivAt (Scalar.qS k)
      (2*Scalar.qS k lam*(1-Scalar.qS k lam) /
        (lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2)))) lam := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hs := (qS_spec k hk hlam).1
  have hpos := (turningPoint_mem_Ioo k hk).1.trans hs.1.1
  have hlinear : 0 < ((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2) := by
    have hh := (div_lt_iff₀ (by linarith : 0 < (k : ℝ)-1)).mp hs.1.1
    nlinarith
  have hp : (Scalar.qS k lam)^(k-2) = (Scalar.qS k lam)^(k-3)*Scalar.qS k lam := by
    rw [← pow_succ]
    congr 1
    omega
  have heq := hs.2
  rw [hp] at heq
  have heq' : (k : ℝ)*lam^2*(Scalar.qS k lam)^(k-3)*Scalar.qS k lam*
      (1-Scalar.qS k lam) = 1 := by simpa only [mul_assoc] using heq
  have hprod : Scalar.qS k lam*(1-Scalar.qS k lam) =
      1/((k : ℝ)*lam^2*(Scalar.qS k lam)^(k-3)) := by
    apply (eq_div_iff (mul_pos (mul_pos hk0 (sq_pos_of_pos hlam0))
      (pow_pos hpos _)).ne').mpr
    nlinarith [heq']
  have hlinneg : (k : ℝ)-2-((k : ℝ)-1)*Scalar.qS k lam =
      -(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2)) := by ring
  convert hasDerivAt_qS_raw k hk hlam using 1
  rw [hlinneg]
  calc
    2*Scalar.qS k lam*(1-Scalar.qS k lam) /
        (lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2))) =
      2*(Scalar.qS k lam*(1-Scalar.qS k lam)) /
        (lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2))) := by ring
    _ = _ := by
      rw [hprod]
      field_simp [hk0.ne', hlam0.ne', (pow_pos hpos (k-3)).ne', hlinear.ne']

/-- The selected stable branch is smooth on its complete manuscript domain. -/
theorem contDiffOn_qS (k : ℕ) (hk : 3 ≤ k) :
    ContDiffOn ℝ ∞ (Scalar.qS k) (Ioi (Scalar.lambdaS k)) := by
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero =>
      apply contDiffOn_zero.mpr
      intro lam hlam
      exact (continuousAt_qS k hk hlam).continuousWithinAt
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, by simp, ?_⟩
      · intro lam hlam
        exact (hasDerivAt_qS k hk hlam).differentiableAt.differentiableWithinAt
      · have hden (lam : ℝ) (hlam : lam ∈ Ioi (Scalar.lambdaS k)) :
            lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2)) ≠ 0 := by
          have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
          have hlam0 := (lambdaS_pos k hk).trans hlam
          have hs := (qS_spec k hk hlam).1
          have hh := (div_lt_iff₀ (by linarith : 0 < (k : ℝ)-1)).mp hs.1.1
          exact (mul_pos hlam0 (by nlinarith)).ne'
        have hd : ContDiffOn ℝ (n : ℕ∞ω)
            (fun lam : ℝ => 2*Scalar.qS k lam*(1-Scalar.qS k lam) /
              (lam*(((k : ℝ)-1)*Scalar.qS k lam-((k : ℝ)-2))))
            (Ioi (Scalar.lambdaS k)) :=
          ((contDiffOn_const.mul ih).mul (contDiffOn_const.sub ih)).div
            (contDiffOn_id.mul ((contDiffOn_const.mul ih).sub contDiffOn_const)) hden
        exact hd.congr (fun lam hlam => (hasDerivAt_qS k hk hlam).deriv)

end
end TensorPCA.ScalarBranchProofs
