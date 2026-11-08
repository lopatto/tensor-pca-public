-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarShapeProofs
public import TensorPCA.ScalarValueProofs
public import TensorPCA.RSVariationalProof
public import TensorPCA.VariationalProofs
public import TensorPCA.CheckedReduction

/-! Local secondary-branch calculus for the variational energy. -/
@[expose] public section
namespace TensorPCA.EnergyBranchProofs
open Set Filter ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs ScalarBranchProofs ScalarValueProofs ScalarShapeProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def rsBoundary (k : ℕ) : ℝ := Real.sqrt (turningPoint k)

theorem rsBoundary_eq (k : ℕ) (hk : 3 ≤ k) :
    rsBoundary k = Real.sqrt (1-1/((k : ℝ)-1)) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold rsBoundary turningPoint
  congr 1
  field_simp [show (k : ℝ)-1 ≠ 0 by linarith]
  ring

theorem energy_eq_rsEnergy (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {m : ℝ}
    (hm : m ∈ Ioo (rsBoundary k) 1) : Scalar.energy k lam m = Scalar.rsEnergy k lam m := by
  have hm0 : 0 < m := (Real.sqrt_nonneg _).trans_lt hm.1
  have hmem : m ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hm.2.le⟩
  have hb : Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m| := by
    rw [← rsBoundary_eq k hk, abs_of_pos hm0]
    exact hm.1.le
  have hrs := GroundState.rsSlice_of_general RSVariationalProof.generalRSVariationalLaw
    VariationalProofs.slicePolynomialFacts k hk m hmem hb
  unfold Scalar.energy Scalar.rsEnergy
  rw [hrs]

theorem hasDerivAt_rsEnergy (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {m : ℝ}
    (hm : m ∈ Ioo (rsBoundary k) 1) :
    HasDerivAt (Scalar.rsEnergy k lam)
      (((k : ℝ)*m/Real.sqrt ((k : ℝ)*(1-m^2)))*
        (lam*m^(k-2)*Real.sqrt ((k : ℝ)*(1-m^2))-1)) m := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : 0 < m := (Real.sqrt_nonneg _).trans_lt hm.1
  have hsq : m^2 < 1 := by nlinarith [hm.2]
  have hR0 := mul_pos hk0 (sub_pos.mpr hsq)
  have hs := ((((hasDerivAt_const m (1 : ℝ)).sub ((hasDerivAt_id m).pow 2)).const_mul
    (k : ℝ)).sqrt hR0.ne')
  have hp : m^(k-1) = m^(k-2)*m := by rw [← pow_succ]; congr 1; omega
  convert (((hasDerivAt_pow k m).const_mul lam).add hs) using 1
  · funext x
    rfl
  · dsimp
    simp only [pow_one, mul_one, zero_sub]
    rw [hp]
    field_simp [(Real.sqrt_pos.mpr hR0).ne']
    ring

theorem hasDerivAt_energy (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {m : ℝ}
    (hm : m ∈ Ioo (rsBoundary k) 1) :
    HasDerivAt (Scalar.energy k lam)
      (((k : ℝ)*m/Real.sqrt ((k : ℝ)*(1-m^2)))*
        (lam*m^(k-2)*Real.sqrt ((k : ℝ)*(1-m^2))-1)) m := by
  apply (hasDerivAt_rsEnergy k hk lam hm).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x hx
  exact energy_eq_rsEnergy k hk lam hx

theorem energy_deriv_sign (k : ℕ) (hk : 3 ≤ k) {lam m : ℝ}
    (hlam : 0 < lam) (hm : m ∈ Ioo (rsBoundary k) 1) :
    (1 < ((k : ℝ)*lam^2)*beta k (m^2) → 0 < deriv (Scalar.energy k lam) m) ∧
      (((k : ℝ)*lam^2)*beta k (m^2) < 1 → deriv (Scalar.energy k lam) m < 0) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : 0 < m := (Real.sqrt_nonneg _).trans_lt hm.1
  have hsq : m^2 < 1 := by nlinarith [hm.2]
  have hR0 := mul_pos hk0 (sub_pos.mpr hsq)
  have hTpos : 0 < lam*m^(k-2)*Real.sqrt ((k : ℝ)*(1-m^2)) := by positivity
  have hp : (m^(k-2))^2 = (m^2)^(k-2) := by
    rw [← pow_mul, Nat.mul_comm (k-2) 2, pow_mul]
  have hT : (lam*m^(k-2)*Real.sqrt ((k : ℝ)*(1-m^2)))^2 =
      ((k : ℝ)*lam^2)*beta k (m^2) := by
    rw [mul_pow, mul_pow, hp, Real.sq_sqrt hR0.le]
    unfold beta
    ring
  have hfac : 0 < (k : ℝ)*m/Real.sqrt ((k : ℝ)*(1-m^2)) := by positivity
  rw [(hasDerivAt_energy k hk lam hm).deriv]
  constructor
  · intro hb
    exact mul_pos hfac (by nlinarith [hT])
  · intro hb
    exact mul_neg_of_pos_of_neg hfac (by nlinarith [hT])

/-- Unconditional local derivative signs at the secondary overlap, obtained
from the proved variational RS evaluation and the actual stable root. -/
theorem localEnergySigns (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) : CheckedReduction.LocalEnergySigns k lam := by
  have hlam0 := (lambdaS_pos k hk).trans hlam
  have ht := turningPoint_mem_Ioo k hk
  have hs := (qS_spec k hk hlam).1
  have hq0 := ht.1.trans hs.1.1
  have hm0 : 0 < Real.sqrt (Scalar.qS k lam) := Real.sqrt_pos.mpr hq0
  have hboundary : rsBoundary k < Real.sqrt (Scalar.qS k lam) := by
    exact Real.sqrt_lt_sqrt ht.1.le hs.1.1
  have hm1 : Real.sqrt (Scalar.qS k lam) < 1 := by
    have hh := Real.sq_sqrt hq0.le
    nlinarith [hs.1.2]
  have hcoeff : 0 < (k : ℝ)*lam^2 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hseq : ((k : ℝ)*lam^2)*beta k (Scalar.qS k lam) = 1 := by
    simpa only [beta, mul_assoc] using hs.2
  let eps : ℝ := min ((Real.sqrt (Scalar.qS k lam)-rsBoundary k)/2)
    ((1-Real.sqrt (Scalar.qS k lam))/2)
  have heps : 0 < eps := lt_min (half_pos (sub_pos.mpr hboundary)) (half_pos (sub_pos.mpr hm1))
  have hepsL : eps ≤ (Real.sqrt (Scalar.qS k lam)-rsBoundary k)/2 := min_le_left _ _
  have hepsR : eps ≤ (1-Real.sqrt (Scalar.qS k lam))/2 := min_le_right _ _
  have hdomain (x : ℝ)
      (hx : x ∈ Icc (Real.sqrt (Scalar.qS k lam)-eps) (Real.sqrt (Scalar.qS k lam)+eps)) :
      x ∈ Ioo (rsBoundary k) 1 := by constructor <;> linarith [hx.1, hx.2]
  refine ⟨⟨by linarith, hm1.le⟩, eps, heps, ?_, ?_, ?_⟩
  · intro x hx
    exact (hasDerivAt_energy k hk lam (hdomain x hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hd := hdomain x ⟨hx.1.le, by linarith [hx.2]⟩
    have hx0 : 0 < x := (Real.sqrt_nonneg _).trans_lt hd.1
    have hbx : turningPoint k < x^2 := by
      have hh := Real.sq_sqrt ht.1.le
      have hb0 : 0 ≤ rsBoundary k := Real.sqrt_nonneg _
      dsimp [rsBoundary] at hd hb0
      nlinarith [hd.1]
    have hxq : x^2 < Scalar.qS k lam := by nlinarith [Real.sq_sqrt hq0.le, hx.2]
    have hb := (strictAntiOn_beta_right k hk) ⟨hbx.le, (hxq.trans hs.1.2).le⟩
      ⟨hs.1.1.le, hs.1.2.le⟩ hxq
    apply (energy_deriv_sign k hk hlam0 hd).1
    have hh := mul_lt_mul_of_pos_left hb hcoeff
    simpa only [hseq] using hh
  · intro x hx
    have hd := hdomain x ⟨by linarith [hx.1], hx.2.le⟩
    have hxq : Scalar.qS k lam < x^2 := by nlinarith [Real.sq_sqrt hq0.le, hx.1]
    have hx1 : x^2 < 1 := by
      have hx0 : 0 < x := hm0.trans hx.1
      nlinarith [hd.2]
    have hb := (strictAntiOn_beta_right k hk) ⟨hs.1.1.le, hs.1.2.le⟩
      ⟨(hs.1.1.trans hxq).le, hx1.le⟩ hxq
    apply (energy_deriv_sign k hk hlam0 hd).2
    have hh := mul_lt_mul_of_pos_left hb hcoeff
    simpa only [hseq] using hh

theorem sqrt_qS_mem_rsDomain (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) : Real.sqrt (Scalar.qS k lam) ∈ Ioo (rsBoundary k) 1 := by
  have ht := turningPoint_mem_Ioo k hk
  have hs := (qS_spec k hk hlam).1
  have hq0 := ht.1.trans hs.1.1
  constructor
  · exact Real.sqrt_lt_sqrt ht.1.le hs.1.1
  · nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg (Scalar.qS k lam), hs.1.2]

theorem energy_at_qS_eq_branchEnergy (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) = branchEnergy k lam := by
  rw [energy_eq_rsEnergy k hk lam (sqrt_qS_mem_rsDomain k hk hlam)]
  unfold Scalar.rsEnergy branchEnergy
  rw [Real.sq_sqrt ((turningPoint_mem_Ioo k hk).1.trans (qS_spec k hk hlam).1.1.1).le]

/-- Exact displayed secondary-branch value, valid throughout lambda>lambdaS. -/
theorem secondaryBranch_explicit (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) =
      Real.sqrt (k : ℝ)/Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1))*
        (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1)/(k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hq0 := (turningPoint_mem_Ioo k hk).1.trans (qS_spec k hk hlam).1.1.1
  have hD : Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1)) ≠ 0 := by positivity
  rw [energy_at_qS_eq_branchEnergy k hk hlam, branchEnergy_eq_explicit k hk hlam]
  field_simp [hk0.ne', hD]

theorem strictMonoOn_branchEnergy (k : ℕ) (hk : 3 ≤ k) :
    StrictMonoOn (branchEnergy k) (Ioi (Scalar.lambdaS k)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro lam hlam
    exact (hasDerivAt_branchEnergy k hk hlam).continuousAt.continuousWithinAt
  · intro lam hlam
    have hlt : Scalar.lambdaS k < lam := by simpa only [interior_Ioi, mem_Ioi] using hlam
    have hpos := (turningPoint_mem_Ioo k hk).1.trans (qS_spec k hk hlt).1.1.1
    rw [(hasDerivAt_branchEnergy k hk hlt).deriv]
    exact pow_pos (Real.sqrt_pos.mpr hpos) _

theorem secondaryBranch_below_gs (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) (hbelow : lam < Scalar.lambdaC k) :
    Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) < Scalar.gs k := by
  rw [energy_at_qS_eq_branchEnergy k hk hlam, ← branchEnergy_critical k hk]
  exact strictMonoOn_branchEnergy k hk hlam (lambdaS_lt_lambdaC k hk) hbelow

theorem secondaryBranch_matches_mleValue (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) (habove : Scalar.lambdaC k ≤ lam) :
    Scalar.mleValue k lam = Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) := by
  rw [energy_at_qS_eq_branchEnergy k hk hlam]
  obtain heq | hgt := habove.eq_or_lt
  · rw [← heq, branchEnergy_critical k hk]
    simp [Scalar.mleValue]
  · rw [Scalar.mleValue, ite_eq_right (not_le_of_gt hgt)]
    exact supercriticalValue_eq_branchEnergy k hk hgt

theorem secondaryBranch_strict_local_max (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    Statements.StrictLocalMaximumOn (Scalar.energy k lam) (Real.sqrt (Scalar.qS k lam)) := by
  have hs := localEnergySigns k hk hlam
  exact Reduction.landscape_local_at hs.1 hs.2

/-- Strict increase of the actual secondary variational energy, rather than
only an auxiliary expression in the scalar root. -/
theorem strictMonoOn_secondaryEnergy (k : ℕ) (hk : 3 ≤ k) :
    StrictMonoOn (fun lam : ℝ => Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)))
      (Ioi (Scalar.lambdaS k)) := by
  intro lam hlam mu hmu hlt
  change Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) < Scalar.energy k mu (Real.sqrt (Scalar.qS k mu))
  rw [energy_at_qS_eq_branchEnergy k hk hlam, energy_at_qS_eq_branchEnergy k hk hmu]
  exact strictMonoOn_branchEnergy k hk hlam hmu hlt

/-- The critical secondary variational energy is exactly the pure ground value. -/
theorem secondaryEnergy_critical (k : ℕ) (hk : 3 ≤ k) :
    Scalar.energy k (Scalar.lambdaC k) (Real.sqrt (Scalar.qS k (Scalar.lambdaC k))) = Scalar.gs k := by
  rw [energy_at_qS_eq_branchEnergy k hk (lambdaS_lt_lambdaC k hk), branchEnergy_critical k hk]

end
end TensorPCA.EnergyBranchProofs
