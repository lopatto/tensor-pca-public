-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.ScalarBranchProofs
public import TensorPCA.Statistical
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Scalar continuity and posterior validation-envelope limits. -/
@[expose] public section
namespace TensorPCA.ValidationControlProofs
open Set Filter MeasureTheory ScalarThresholdProofs ScalarStaticRatioProofs ScalarStationaryProofs ScalarSelectionProofs ScalarBranchProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem continuousAt_qStar (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hne : lam ≠ Scalar.lambdaC k) : ContinuousAt (Scalar.qStar k) lam := by
  by_cases hle : lam ≤ Scalar.lambdaC k
  · have hlt : lam < Scalar.lambdaC k := lt_of_le_of_ne hle hne
    apply (continuousAt_const : ContinuousAt (fun _t : ℝ => (0 : ℝ)) lam).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with t ht
    simp only [Scalar.qStar, ite_eq_left ht.le]
  · have hgt := lt_of_not_ge hle
    apply (continuousAt_qS k hk ((lambdaS_lt_lambdaC k hk).trans hgt)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with t ht
    exact qStar_eq_qS k hk ht

theorem sqrt_pow_eq (q : ℝ) (hq : 0 ≤ q) (k : ℕ) :
    Real.sqrt (q^k) = (Real.sqrt q)^k := by
  apply (Real.sqrt_eq_iff_eq_sq (pow_nonneg hq _) (pow_nonneg (Real.sqrt_nonneg _) _)).mpr
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hq]

theorem validationEnvelope_tendsto (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hmmse : Tendsto (fun n : ℕ => Model.tensorMMSE (n+1) k (Real.sqrt (lam^2+delta^2)))
      atTop (𝓝 (1-(Scalar.qStar k (Real.sqrt (lam^2+delta^2)))^k))) :
    Tendsto (fun n : ℕ => Statistical.validationEnvelope (n+1) k lam delta) atTop
      (𝓝 ((Real.sqrt (Scalar.qStar k (Real.sqrt (lam^2+delta^2))))^k)) := by
  have hstrength : 0 ≤ Real.sqrt (lam^2+delta^2) := Real.sqrt_nonneg _
  have hq : 0 ≤ Scalar.qStar k (Real.sqrt (lam^2+delta^2)) :=
    ((selectionLaws k hk).2.2.2.2.2.2 _ hstrength).1
  have hroot : Tendsto
      (fun n : ℕ => Real.sqrt (1-Model.tensorMMSE (n+1) k (Real.sqrt (lam^2+delta^2))))
      atTop (𝓝 ((Real.sqrt (Scalar.qStar k (Real.sqrt (lam^2+delta^2))))^k)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hmmse).sqrt
    simpa only [sub_sub_cancel, sqrt_pow_eq _ hq k] using h
  have hnat : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_mono (fun n : ℕ => (by linarith : (n : ℝ) ≤ (n : ℝ)+1))
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hden : Tendsto (fun n : ℕ => delta*Real.sqrt (n+1 : ℕ)) atTop atTop :=
    Tendsto.const_mul_atTop hdelta (Real.tendsto_sqrt_atTop.comp hnat)
  have htail := hden.const_div_atTop (2 : ℝ)
  simpa only [Statistical.validationEnvelope, add_zero] using hroot.add htail

theorem validationRootEnvelope_tendsto (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hmmse : Tendsto (fun n : ℕ => Model.tensorMMSE (n+1) k (Real.sqrt (lam^2+delta^2)))
      atTop (𝓝 (1-(Scalar.qStar k (Real.sqrt (lam^2+delta^2)))^k))) :
    Tendsto (fun n : ℕ => Statistical.validationRootEnvelope (n+1) k lam delta) atTop
      (𝓝 (Real.sqrt (Scalar.qStar k (Real.sqrt (lam^2+delta^2))))) := by
  have he := validationEnvelope_tendsto k hk lam hdelta hmmse
  have h := he.rpow_const (Or.inr (by positivity : 0 ≤ (k : ℝ)⁻¹))
  simpa only [Statistical.validationRootEnvelope,
    Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) (by omega : k ≠ 0)] using h

/-- MMSE at perturbed strengths controls the explicit validation envelopes;
no estimator bound or estimator-dependent limit is assumed. -/
theorem validationEnvelopeControl (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : 0 ≤ lam) (hne : lam ≠ Scalar.lambdaC k)
    (hmmse : ∀ mu : ℝ, 0 < mu → mu ≠ Scalar.lambdaC k →
      Tendsto (fun n : ℕ => Model.tensorMMSE (n+1) k mu)
        atTop (𝓝 (1-(Scalar.qStar k mu)^k))) : Statistical.ValidationEnvelopeControl k lam := by
  let strength : ℝ → ℝ := fun delta => Real.sqrt (lam^2+delta^2)
  have hs0 : strength 0 = lam := by dsimp [strength]; simp only [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hlam]
  have hs : ContinuousAt strength 0 := by dsimp [strength]; fun_prop
  have hroot : ContinuousAt (fun delta : ℝ => Real.sqrt (Scalar.qStar k (strength delta))) 0 := by
    have hq : ContinuousAt (Scalar.qStar k) (strength 0) := by
      rw [hs0]
      exact continuousAt_qStar k hk hne
    simpa only [Function.comp_def] using Real.continuous_sqrt.continuousAt.comp (hq.comp hs)
  intro eps heps
  have ha : ∀ᶠ delta in 𝓝 (0 : ℝ),
      (Real.sqrt (Scalar.qStar k (strength delta)))^k < (Real.sqrt (Scalar.qStar k lam))^k+eps := by
    have hnh : Iio ((Real.sqrt (Scalar.qStar k lam))^k+eps) ∈
        𝓝 ((Real.sqrt (Scalar.qStar k (strength 0)))^k) := by
      rw [hs0]
      exact Iio_mem_nhds (lt_add_of_pos_right _ heps)
    exact (hroot.pow k).eventually hnh
  have hb : ∀ᶠ delta in 𝓝 (0 : ℝ),
      Real.sqrt (Scalar.qStar k (strength delta)) < Real.sqrt (Scalar.qStar k lam)+eps := by
    have hnh : Iio (Real.sqrt (Scalar.qStar k lam)+eps) ∈
        𝓝 (Real.sqrt (Scalar.qStar k (strength 0))) := by
      rw [hs0]
      exact Iio_mem_nhds (lt_add_of_pos_right _ heps)
    exact hroot.eventually hnh
  have hn : ∀ᶠ delta in 𝓝 (0 : ℝ), strength delta ≠ Scalar.lambdaC k := by
    have hnh : {mu : ℝ | mu ≠ Scalar.lambdaC k} ∈ 𝓝 (strength 0) :=
      isOpen_compl_singleton.mem_nhds (by simpa only [hs0, mem_compl_iff, mem_singleton_iff] using hne)
    exact hs.eventually hnh
  have hpositive : ∀ᶠ delta in 𝓝[>] (0 : ℝ), 0 < delta := self_mem_nhdsWithin
  have hall : ∀ᶠ delta in 𝓝[>] (0 : ℝ), 0 < delta ∧
      (Real.sqrt (Scalar.qStar k (strength delta)))^k < (Real.sqrt (Scalar.qStar k lam))^k+eps ∧
      Real.sqrt (Scalar.qStar k (strength delta)) < Real.sqrt (Scalar.qStar k lam)+eps ∧
      strength delta ≠ Scalar.lambdaC k :=
    hpositive.and ((ha.and (hb.and hn)).filter_mono nhdsWithin_le_nhds)
  obtain ⟨delta, hdelta, hda, hdb, hdne⟩ := hall.exists
  have hdpos : 0 < strength delta := Real.sqrt_pos.mpr (by positivity)
  have hm := hmmse (strength delta) hdpos hdne
  refine ⟨delta, (Real.sqrt (Scalar.qStar k (strength delta)))^k,
    Real.sqrt (Scalar.qStar k (strength delta)), hdelta, hdne, ?_, hda.le, ?_, hdb.le⟩
  · exact validationEnvelope_tendsto k hk lam hdelta hm
  · exact validationRootEnvelope_tendsto k hk lam hdelta hm

end
end TensorPCA.ValidationControlProofs
