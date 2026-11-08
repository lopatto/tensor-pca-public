-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarStationaryProofs

/-! Global scalar selection laws, retaining the reviewed supremum definitions. -/
@[expose] public section
namespace TensorPCA.ScalarSelectionProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem strictMonoOn_beta_left (k : ℕ) (hk : 3 ≤ k) :
    StrictMonoOn (beta k) (Icc (0 : ℝ) (turningPoint k)) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ht := turningPoint_mem_Ioo k hk
  have hc : Continuous (beta k) := by unfold beta; fun_prop
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.continuousOn
  intro q hq
  have hq' : 0 < q ∧ q < turningPoint k := by
    simpa only [interior_Icc, mem_Ioo] using hq
  have hlinear : 0 < (k : ℝ)-2-((k : ℝ)-1)*q := by
    have hleft := (lt_div_iff₀ (by linarith : 0 < (k : ℝ)-1)).mp hq'.2
    nlinarith
  rw [(hasDerivAt_beta k hk q).deriv]
  exact mul_pos (pow_pos hq'.1 _) hlinear

theorem exists_unstableStationaryPoint (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    ∃ u ∈ Ioo (0 : ℝ) (turningPoint k), ((k : ℝ)*lam^2)*beta k u = 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 : 0 < lam := (lambdaS_pos k hk).trans hlam
  have ht := turningPoint_mem_Ioo k hk
  have hBt : 0 < beta k (turningPoint k) :=
    mul_pos (pow_pos ht.1 _) (sub_pos.mpr ht.2)
  have hcoeff : 0 < (k : ℝ)*lam^2 := mul_pos hk0 (sq_pos_of_pos hlam0)
  have htarget : 0 < 1/((k : ℝ)*lam^2) := one_div_pos.mpr hcoeff
  have hsq := (sq_lt_sq₀ (lambdaS_pos k hk).le hlam0.le).mpr hlam
  rw [lambdaS_sq k hk] at hsq
  have hbelow : 1/((k : ℝ)*lam^2) < beta k (turningPoint k) := by
    apply (div_lt_iff₀ hcoeff).mpr
    have hh := (div_lt_iff₀ (mul_pos hk0 hBt)).mp hsq
    nlinarith
  have hc : ContinuousOn (beta k) (Icc (0 : ℝ) (turningPoint k)) := by
    unfold beta
    fun_prop
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc ht.1.le hc
    ⟨by simpa only [beta, zero_pow (by omega : k-2 ≠ 0), zero_mul] using htarget.le,
      hbelow.le⟩
  have hulo : 0 < u := by
    by_contra hn
    have hueq : u = 0 := le_antisymm (le_of_not_gt hn) hu.1
    rw [hueq] at heq
    simp only [beta, zero_pow (by omega : k-2 ≠ 0), zero_mul] at heq
    linarith
  have huhi : u < turningPoint k := by
    by_contra hn
    have hueq : u = turningPoint k := le_antisymm hu.2 (le_of_not_gt hn)
    rw [hueq] at heq
    linarith
  refine ⟨u, ⟨hulo, huhi⟩, ?_⟩
  rw [heq]
  exact mul_one_div_cancel hcoeff.ne'

theorem hasDerivAt_f (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {q : ℝ} (hq : q < 1) :
    HasDerivAt (Scalar.f k lam)
      (q * (((k : ℝ)*lam^2)*beta k q - 1)/(1-q)) q := by
  have hlin : HasDerivAt (fun x : ℝ => 1-x) (-1) q := by
    simpa only [id_eq] using! (hasDerivAt_id q).const_sub (1 : ℝ)
  have hlog := hlin.log (ne_of_gt (sub_pos.mpr hq))
  have hpow := ((hasDerivAt_id q).pow k).const_mul (lam^2)
  have hpowq : q^(k-1) = q^(k-2)*q := by
    rw [← pow_succ]
    congr 1
    omega
  convert (hpow.add hlog).add (hasDerivAt_id q) using 1
  · funext x
    rfl
  · dsimp
    unfold beta
    rw [hpowq]
    field_simp [(sub_pos.mpr hq).ne']
    ring

theorem continuousOn_f (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    ContinuousOn (Scalar.f k lam) (Iio 1) := by
  intro q hq
  exact (hasDerivAt_f k hk lam hq).continuousAt.continuousWithinAt

theorem criticalOverlap_lt_qS (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) : criticalOverlap k < Scalar.qS k lam := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 : 0 < lam := (lambdaC_pos k hk).trans hlam
  have hstable := (qS_spec k hk ((lambdaS_lt_lambdaC k hk).trans hlam)).1
  have hcrit := criticalOverlap_stable k hk
  have hc0 : 0 < beta k (criticalOverlap k) :=
    mul_pos (pow_pos (criticalOverlap_mem_Ioo k hk).1 _)
      (sub_pos.mpr (criticalOverlap_mem_Ioo k hk).2)
  have hsq : (Scalar.lambdaC k)^2 < lam^2 :=
    (sq_lt_sq₀ (lambdaC_pos k hk).le hlam0.le).mpr hlam
  have hs : ((k : ℝ)*lam^2)*beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using hstable.2
  have hc : ((k : ℝ)*(Scalar.lambdaC k)^2)*beta k (criticalOverlap k) = 1 := by
    simpa only [beta, mul_assoc] using hcrit.2
  have hb : beta k (Scalar.qS k lam) < beta k (criticalOverlap k) := by
    have hprod := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hsq hk0) hc0
    rw [hc] at hprod
    apply (mul_lt_mul_iff_right₀ (mul_pos hk0 (sq_pos_of_pos hlam0))).mp
    simpa only [mul_comm (beta k (Scalar.qS k lam)),
      mul_comm (beta k (criticalOverlap k))] using hs.trans_lt hprod
  by_contra hn
  have hle : Scalar.qS k lam ≤ criticalOverlap k := le_of_not_gt hn
  have ha := (strictAntiOn_beta_right k hk).antitoneOn
    ⟨hstable.1.1.le, hstable.1.2.le⟩ ⟨hcrit.1.1.le, hcrit.1.2.le⟩ hle
  exact (not_le_of_gt hb) ha

theorem f_criticalOverlap_pos (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) : 0 < Scalar.f k lam (criticalOverlap k) := by
  have hsq : (Scalar.lambdaC k)^2 < lam^2 :=
    (sq_lt_sq₀ (lambdaC_pos k hk).le ((lambdaC_pos k hk).trans hlam).le).mpr hlam
  have hp : 0 < (criticalOverlap k)^k := pow_pos (criticalOverlap_mem_Ioo k hk).1 _
  have hd : Scalar.f k lam (criticalOverlap k) =
      Scalar.f k (Scalar.lambdaC k) (criticalOverlap k) +
        (lam^2-(Scalar.lambdaC k)^2)*(criticalOverlap k)^k := by
    unfold Scalar.f
    ring
  rw [hd, f_zero_at_criticalOverlap k hk, zero_add]
  exact mul_pos (sub_pos.mpr hsq) hp

/-- The two actual stationary roots partition the scalar potential into its
three monotonicity intervals. Endpoints are included whenever physically valid. -/
theorem f_stationary_monotonicity (k : ℕ) (hk : 3 ≤ k) {lam u : ℝ}
    (hlam : Scalar.lambdaS k < lam) (hu : u ∈ Ioo (0 : ℝ) (turningPoint k))
    (hueq : ((k : ℝ)*lam^2)*beta k u = 1) :
    StrictAntiOn (Scalar.f k lam) (Icc (0 : ℝ) u) ∧
    StrictMonoOn (Scalar.f k lam) (Icc u (Scalar.qS k lam)) ∧
    StrictAntiOn (Scalar.f k lam) (Ico (Scalar.qS k lam) 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have hcoeff : 0 < (k : ℝ)*lam^2 := mul_pos hk0 (sq_pos_of_pos hlam0)
  have ht := turningPoint_mem_Ioo k hk
  have hs := (qS_spec k hk hlam).1
  have hseq : ((k : ℝ)*lam^2)*beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using hs.2
  have hneg (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
      (hb : ((k : ℝ)*lam^2)*beta k q < 1) : deriv (Scalar.f k lam) q < 0 := by
    rw [(hasDerivAt_f k hk lam hq.2).deriv]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq.1 (by linarith))
      (sub_pos.mpr hq.2)
  have hpos (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
      (hb : 1 < ((k : ℝ)*lam^2)*beta k q) : 0 < deriv (Scalar.f k lam) q := by
    rw [(hasDerivAt_f k hk lam hq.2).deriv]
    exact div_pos (mul_pos hq.1 (by linarith)) (sub_pos.mpr hq.2)
  refine ⟨?_, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact (continuousOn_f k hk lam).mono (fun q hq => hq.2.trans_lt (hu.2.trans ht.2))
    · intro q hq
      have hq' : 0 < q ∧ q < u := by simpa only [interior_Icc, mem_Ioo] using hq
      have hb := (strictMonoOn_beta_left k hk) ⟨hq'.1.le, (hq'.2.trans hu.2).le⟩
        ⟨hu.1.le, hu.2.le⟩ hq'.2
      apply hneg q ⟨hq'.1, hq'.2.trans (hu.2.trans ht.2)⟩
      have hh := mul_lt_mul_of_pos_left hb hcoeff
      simpa only [hueq] using hh
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact (continuousOn_f k hk lam).mono (fun q hq => hq.2.trans_lt hs.1.2)
    · intro q hq
      have hq' : u < q ∧ q < Scalar.qS k lam := by
        simpa only [interior_Icc, mem_Ioo] using hq
      apply hpos q ⟨hu.1.trans hq'.1, hq'.2.trans hs.1.2⟩
      by_cases hqt : q ≤ turningPoint k
      · have hb := (strictMonoOn_beta_left k hk) ⟨hu.1.le, hu.2.le⟩
          ⟨(hu.1.trans hq'.1).le, hqt⟩ hq'.1
        have hh := mul_lt_mul_of_pos_left hb hcoeff
        simpa only [hueq] using hh
      · have hb := (strictAntiOn_beta_right k hk)
          ⟨(lt_of_not_ge hqt).le, (hq'.2.trans hs.1.2).le⟩
          ⟨hs.1.1.le, hs.1.2.le⟩ hq'.2
        have hh := mul_lt_mul_of_pos_left hb hcoeff
        simpa only [hseq] using hh
  · apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
    · exact (continuousOn_f k hk lam).mono (fun q hq => hq.2)
    · intro q hq
      have hq' : Scalar.qS k lam < q ∧ q < 1 := by
        simpa only [interior_Ico, mem_Ioo] using hq
      have hb := (strictAntiOn_beta_right k hk) ⟨hs.1.1.le, hs.1.2.le⟩
        ⟨(hs.1.1.trans hq'.1).le, hq'.2.le⟩ hq'.1
      apply hneg q ⟨ht.1.trans (hs.1.1.trans hq'.1), hq'.2⟩
      have hh := mul_lt_mul_of_pos_left hb hcoeff
      simpa only [hseq] using hh

/-- Above the statistical threshold the stable root is the unique strict
maximum of the actual scalar potential on the entire half-open domain. -/
theorem supercritical_qS_strict_max (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) :
    0 < Scalar.f k lam (Scalar.qS k lam) ∧
      ∀ r ∈ Ico (0 : ℝ) 1, r ≠ Scalar.qS k lam →
        Scalar.f k lam r < Scalar.f k lam (Scalar.qS k lam) := by
  have hlamS := (lambdaS_lt_lambdaC k hk).trans hlam
  have hs := (qS_spec k hk hlamS).1
  have ht := turningPoint_mem_Ioo k hk
  obtain ⟨u, hu, hueq⟩ := exists_unstableStationaryPoint k hk hlamS
  obtain ⟨hleft, hmiddle, hright⟩ := f_stationary_monotonicity k hk hlamS hu hueq
  have hcrit := criticalOverlap_mem_Ioo k hk
  have hclt := criticalOverlap_lt_qS k hk hlam
  have hcp : 0 < Scalar.f k lam (Scalar.qS k lam) := by
    have h := hmiddle
      ⟨(hu.2.trans (criticalOverlap_gt_turningPoint k hk)).le, hclt.le⟩
      ⟨(hu.2.trans hs.1.1).le, le_rfl⟩ hclt
    exact (f_criticalOverlap_pos k hk hlam).trans h
  refine ⟨hcp, ?_⟩
  intro r hr hne
  by_cases hru : r ≤ u
  · have h := hleft.antitoneOn ⟨le_rfl, hu.1.le⟩ ⟨hr.1, hru⟩ hr.1
    have hz : Scalar.f k lam 0 = 0 := by
      simp [Scalar.f, show k ≠ 0 by omega]
    rw [hz] at h
    exact h.trans_lt hcp
  · have hur : u < r := lt_of_not_ge hru
    by_cases hrq : r ≤ Scalar.qS k lam
    · exact hmiddle ⟨hur.le, hrq⟩ ⟨(hu.2.trans hs.1.1).le, le_rfl⟩
        (lt_of_le_of_ne hrq hne)
    · exact hright ⟨le_rfl, hs.1.2⟩ ⟨(lt_of_not_ge hrq).le, hr.2⟩
        (lt_of_not_ge hrq)

theorem supercritical_qS_maximizer (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) :
    Scalar.IsScalarMaximizer k lam (Scalar.qS k lam) ∧
      ∀ q : ℝ, Scalar.IsScalarMaximizer k lam q → q = Scalar.qS k lam := by
  have hs := (qS_spec k hk ((lambdaS_lt_lambdaC k hk).trans hlam)).1
  have hqmem : Scalar.qS k lam ∈ Ico (0 : ℝ) 1 :=
    ⟨((turningPoint_mem_Ioo k hk).1.trans hs.1.1).le, hs.1.2⟩
  have hmax := (supercritical_qS_strict_max k hk hlam).2
  refine ⟨⟨hqmem, ?_⟩, ?_⟩
  · intro r hr
    by_cases heq : r = Scalar.qS k lam
    · exact le_of_eq (congrArg (Scalar.f k lam) heq)
    · exact (hmax r hr heq).le
  · intro q hq
    by_contra hne
    exact not_lt_of_ge (hq.2 _ hqmem) (hmax q hq.1 hne)

theorem qStar_eq_qS (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) : Scalar.qStar k lam = Scalar.qS k lam := by
  have hmax := supercritical_qS_maximizer k hk hlam
  have hset : {q : ℝ | Scalar.IsScalarMaximizer k lam q} = {Scalar.qS k lam} := by
    ext q
    constructor
    · intro hq
      exact mem_singleton_iff.mpr (hmax.2 q hq)
    · intro hq
      have heq : q = Scalar.qS k lam := mem_singleton_iff.mp hq
      change Scalar.IsScalarMaximizer k lam q
      simpa only [heq] using hmax.1
  unfold Scalar.qStar
  rw [ite_eq_right (not_le_of_gt hlam), hset]
  simp

/-- Complete checked selection laws, with no variational or probabilistic input. -/
theorem selectionLaws (k : ℕ) (hk : 3 ≤ k) : Scalar.SelectionLaws k := by
  refine ⟨lambdaS_pos k hk, lambdaS_lt_lambdaC k hk,
    nonpositiveStrengths_bddAbove k hk, ?_, ?_, zK_spec k hk, ?_⟩
  · intro lam hlam
    exact qS_spec k hk hlam
  · intro lam hlam
    have hmax := supercritical_qS_maximizer k hk hlam
    have hspec := (qS_spec k hk ((lambdaS_lt_lambdaC k hk).trans hlam)).1
    have hpos := (turningPoint_mem_Ioo k hk).1.trans hspec.1.1
    have heq := qStar_eq_qS k hk hlam
    rw [heq]
    exact ⟨hmax.1, hpos, rfl, hmax.2⟩
  · intro lam hlam
    by_cases hle : lam ≤ Scalar.lambdaC k
    · simp only [Scalar.qStar, ite_eq_left hle, mem_Ico]
      exact ⟨le_rfl, zero_lt_one⟩
    · have hgt : Scalar.lambdaC k < lam := lt_of_not_ge hle
      rw [qStar_eq_qS k hk hgt]
      have hs := (qS_spec k hk ((lambdaS_lt_lambdaC k hk).trans hgt)).1
      exact ⟨((turningPoint_mem_Ioo k hk).1.trans hs.1.1).le, hs.1.2⟩

end
end TensorPCA.ScalarSelectionProofs
