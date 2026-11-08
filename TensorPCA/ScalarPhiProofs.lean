-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarSelectionProofs

/-! Exact comparison of the two scalar potentials, including both endpoints. -/
@[expose] public section
namespace TensorPCA.ScalarPhiProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem hasDerivAt_phi (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (Scalar.phi k lam)
      (((k : ℝ)*((k : ℝ)-1)*lam^2*q^(k-2) /
        (1+lam^2*(k : ℝ)*q^(k-1))) *
        (q*(((k : ℝ)*lam^2)*beta k q-1))) q := by
  have hD : 1+lam^2*(k : ℝ)*q^(k-1) ≠ 0 := ne_of_gt (by positivity)
  have hlin := (hasDerivAt_const q (1 : ℝ)).add
    ((hasDerivAt_pow (k-1) q).const_mul (lam^2*(k : ℝ)))
  have hlog := hlin.log hD
  have hpow : q^(k-1) = q^(k-2)*q := by
    rw [← pow_succ]
    congr 1
    omega
  convert (((hasDerivAt_pow (k-1) q).const_mul (lam^2*(k : ℝ))).sub hlog).sub
    ((hasDerivAt_pow k q).const_mul (lam^2*((k : ℝ)-1))) using 1
  · funext x
    rfl
  · dsimp
    simp only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, Nat.sub_sub]
    unfold beta
    rw [hpow]
    field_simp [hD]
    ring

theorem continuousOn_phi (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    ContinuousOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) := by
  intro q hq
  exact (hasDerivAt_phi k hk lam hq.1).continuousAt.continuousWithinAt

theorem f_le_phi (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1) : Scalar.f k lam q ≤ Scalar.phi k lam q := by
  have hq0 := hq.1
  have hD : 0 < 1+lam^2*(k : ℝ)*q^(k-1) := by positivity
  have hp : 0 < (1-q)*(1+lam^2*(k : ℝ)*q^(k-1)) := mul_pos (sub_pos.mpr hq.2) hD
  have hlog := Real.log_le_sub_one_of_pos hp
  rw [Real.log_mul (sub_pos.mpr hq.2).ne' hD.ne'] at hlog
  have hpow : q^k = q^(k-1)*q := by rw [← pow_succ]; congr 1; omega
  unfold Scalar.f Scalar.phi
  rw [hpow]
  nlinarith

theorem phi_eq_f_of_stationary (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hs : ((k : ℝ)*lam^2)*beta k q = 1) :
    Scalar.phi k lam q = Scalar.f k lam q := by
  have hq0 := hq.1
  have hD : 0 < 1+lam^2*(k : ℝ)*q^(k-1) := by positivity
  have hpow : q^k = q^(k-1)*q := by rw [← pow_succ]; congr 1; omega
  have hp : q^(k-1) = q^(k-2)*q := by rw [← pow_succ]; congr 1; omega
  have hprod : (1-q)*(1+lam^2*(k : ℝ)*q^(k-1)) = 1 := by
    rw [hp]
    unfold beta at hs
    nlinarith [congrArg (fun x : ℝ => x*q) hs]
  have hlog : Real.log (1-q)+Real.log (1+lam^2*(k : ℝ)*q^(k-1)) = 0 := by
    rw [← Real.log_mul (sub_pos.mpr hq.2).ne' hD.ne', hprod, Real.log_one]
  unfold Scalar.phi Scalar.f
  rw [hpow, hp] at *
  unfold beta at hs
  nlinarith [congrArg (fun x : ℝ => x*q) hs]

theorem phi_one_not_max (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam) :
    ¬ IsMaxOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkm : 0 < (k : ℝ)-1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hd := hasDerivAt_phi k hk lam (q := 1) (by norm_num)
  have hc : (k : ℝ)*((k : ℝ)-1)*lam^2 /
      (1+lam^2*(k : ℝ)) > 0 := by positivity
  simp only [one_pow, beta, sub_self, mul_zero, mul_one, zero_sub, mul_neg_one] at hd
  intro hmax
  have htan : (-1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 1 := by
    have hseg : segment ℝ (1 : ℝ) 0 ⊆ Icc (0 : ℝ) 1 :=
      (convex_Icc _ _).segment_subset ⟨by norm_num, le_rfl⟩ ⟨le_rfl, by norm_num⟩
    simpa only [zero_sub] using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hh := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt htan
  have hbad : (k : ℝ)*((k : ℝ)-1)*lam^2 / (1+lam^2*(k : ℝ)) ≤ 0 := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, neg_mul, mul_neg_one,
      neg_neg, one_mul] using hh
  exact (not_le_of_gt hc) hbad

theorem phi_maximizer_eq_f (k : ℕ) (hk : 3 ≤ k) {lam q : ℝ}
    (hlam : 0 < lam) (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) q) :
    q ∈ Ico (0 : ℝ) 1 ∧ Scalar.phi k lam q = Scalar.f k lam q := by
  have hq1 : q < 1 := by
    apply lt_of_le_of_ne hq.2
    intro heq
    subst q
    exact phi_one_not_max k hk hlam hmax
  refine ⟨⟨hq.1, hq1⟩, ?_⟩
  by_cases hq0 : q = 0
  · subst q
    simp [Scalar.phi, Scalar.f, show k ≠ 0 by omega, show k-1 ≠ 0 by omega]
  · have hpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
    have hlocal := hmax.isLocalMax (Icc_mem_nhds hpos hq1)
    have hz := hlocal.hasDerivAt_eq_zero (hasDerivAt_phi k hk lam hq.1)
    have hfac : 0 < ((k : ℝ)*((k : ℝ)-1)*lam^2*q^(k-2) /
        (1+lam^2*(k : ℝ)*q^(k-1))) := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkm : 0 < (k : ℝ)-1 := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      positivity
    have hstat : ((k : ℝ)*lam^2)*beta k q = 1 := by
      have hh := (mul_eq_zero.mp hz).resolve_left hfac.ne'
      have hhh := (mul_eq_zero.mp hh).resolve_left hpos.ne'
      linarith
    exact phi_eq_f_of_stationary k hk lam ⟨hpos, hq1⟩ hstat

theorem qStar_isScalarMaximizer (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : 0 ≤ lam) : Scalar.IsScalarMaximizer k lam (Scalar.qStar k lam) := by
  by_cases hle : lam ≤ Scalar.lambdaC k
  · have hnonpos := (f_nonpos_iff_le_critical k hk hlam).mpr
      (by simpa only [← lambdaC_eq_sqrt_criticalSquared k hk] using hle)
    have hq : Scalar.qStar k lam = 0 := by simp [Scalar.qStar, hle]
    rw [hq]
    refine ⟨⟨le_rfl, zero_lt_one⟩, ?_⟩
    intro r hr
    have hz : Scalar.f k lam 0 = 0 := by simp [Scalar.f, show k ≠ 0 by omega]
    rw [hz]
    exact hnonpos r hr
  · have hgt := lt_of_not_ge hle
    rw [qStar_eq_qS k hk hgt]
    exact (supercritical_qS_maximizer k hk hgt).1

theorem phi_le_qStar_f (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Scalar.phi k lam q ≤ Scalar.f k lam (Scalar.qStar k lam) := by
  obtain ⟨p, hp, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) (continuousOn_phi k hk lam)
  have heq := phi_maximizer_eq_f k hk hlam hp hmax
  calc
    _ ≤ Scalar.phi k lam p := hmax hq
    _ = Scalar.f k lam p := heq.2
    _ ≤ _ := (qStar_isScalarMaximizer k hk hlam.le).2 p heq.1

theorem phi_qStar_eq_f (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam) :
    Scalar.phi k lam (Scalar.qStar k lam) = Scalar.f k lam (Scalar.qStar k lam) := by
  have hq := (qStar_isScalarMaximizer k hk hlam.le).1
  exact le_antisymm (phi_le_qStar_f k hk hlam ⟨hq.1, hq.2.le⟩) (f_le_phi k hk lam hq)

/-- The half-open f domain and closed phi domain have exactly the same global
maximizers. In particular q=1 is excluded by a checked endpoint derivative. -/
theorem common_maximizers (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam) (q : ℝ) :
    Scalar.IsScalarMaximizer k lam q ↔
      q ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) q := by
  constructor
  · intro hq
    have hselected := qStar_isScalarMaximizer k hk hlam.le
    have heq : Scalar.phi k lam q = Scalar.f k lam q := by
      exact le_antisymm ((phi_le_qStar_f k hk hlam ⟨hq.1.1, hq.1.2.le⟩).trans
        (hq.2 _ hselected.1)) (f_le_phi k hk lam hq.1)
    refine ⟨⟨hq.1.1, hq.1.2.le⟩, ?_⟩
    intro r hr
    rw [heq]
    exact (phi_le_qStar_f k hk hlam hr).trans (hq.2 _ hselected.1)
  · rintro ⟨hq, hmax⟩
    have heq := phi_maximizer_eq_f k hk hlam hq hmax
    refine ⟨heq.1, ?_⟩
    intro r hr
    calc
      _ ≤ Scalar.phi k lam r := f_le_phi k hk lam hr
      _ ≤ Scalar.phi k lam q := hmax ⟨hr.1, hr.2.le⟩
      _ = _ := heq.2

theorem common_maximum_values (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 < lam) :
    sSup (Scalar.f k lam '' Ico (0 : ℝ) 1) =
      sSup (Scalar.phi k lam '' Icc (0 : ℝ) 1) := by
  have hselected := qStar_isScalarMaximizer k hk hlam.le
  have hf : IsGreatest (Scalar.f k lam '' Ico (0 : ℝ) 1)
      (Scalar.f k lam (Scalar.qStar k lam)) := by
    refine ⟨⟨_, hselected.1, rfl⟩, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hselected.2 r hr
  have hp : IsGreatest (Scalar.phi k lam '' Icc (0 : ℝ) 1)
      (Scalar.f k lam (Scalar.qStar k lam)) := by
    refine ⟨⟨_, ⟨hselected.1.1, hselected.1.2.le⟩, phi_qStar_eq_f k hk hlam⟩, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact phi_le_qStar_f k hk hlam hr
  exact (hf.isLUB.csSup_eq ⟨_, hf.1⟩).trans (hp.isLUB.csSup_eq ⟨_, hp.1⟩).symm

theorem phi_neg_of_subcritical (k : ℕ) (hk : 3 ≤ k) {lam q : ℝ}
    (hlam : 0 < lam) (hsub : lam < Scalar.lambdaC k) (hq : q ∈ Ioc (0 : ℝ) 1) :
    Scalar.phi k lam q < 0 := by
  have hqs : Scalar.qStar k lam = 0 := by simp [Scalar.qStar, hsub.le]
  have hfzero : Scalar.f k lam 0 = 0 := by simp [Scalar.f, show k ≠ 0 by omega]
  have hbound (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : Scalar.phi k lam r ≤ 0 := by
    have hh := phi_le_qStar_f k hk hlam hr
    simpa only [hqs, hfzero] using hh
  by_contra hn
  have heq : Scalar.phi k lam q = 0 := le_antisymm (hbound q ⟨hq.1.le, hq.2⟩) (le_of_not_gt hn)
  have hmax : IsMaxOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) q := by
    intro r hr
    rw [heq]
    exact hbound r hr
  have hshared := phi_maximizer_eq_f k hk hlam ⟨hq.1.le, hq.2⟩ hmax
  have hneg := f_neg_of_subcritical k hk hlam.le hsub ⟨hq.1, hshared.1.2⟩
  rw [← hshared.2, heq] at hneg
  exact lt_irrefl _ hneg

theorem critical_phi_maximizers (k : ℕ) (hk : 3 ≤ k) (q : ℝ) :
    (q ∈ Icc (0 : ℝ) 1 ∧
      IsMaxOn (Scalar.phi k (Scalar.lambdaC k)) (Icc (0 : ℝ) 1) q) ↔
      q = 0 ∨ q = Scalar.qS k (Scalar.lambdaC k) := by
  rw [← common_maximizers k hk (lambdaC_pos k hk), critical_scalarMaximizers k hk,
    qS_at_critical k hk]

theorem supercritical_phi_maximizers (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaC k < lam) (q : ℝ) :
    (q ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (Scalar.phi k lam) (Icc (0 : ℝ) 1) q) ↔
      q = Scalar.qS k lam := by
  rw [← common_maximizers k hk ((lambdaC_pos k hk).trans hlam)]
  constructor
  · exact (supercritical_qS_maximizer k hk hlam).2 q
  · intro heq
    rw [heq]
    exact (supercritical_qS_maximizer k hk hlam).1

end
end TensorPCA.ScalarPhiProofs
