-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityScalarizationProofs
public import TensorPCA.FinitePriorCavityRemainderProofs

/-! Uniform conditional RS upper bound for the fresh and correction channels. The only random error is the base-posterior replica variance. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityScalarErrorProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open FinitePriorCavityNormalizationProofs FinitePriorCavityScalarizationProofs
open FinitePriorCavityRemainderProofs GaussianPriorTransferProofs PosteriorPairProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem sqrt_remainder_le {I A L V n : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hn : 0 < n) (hI : I ≤ 2*(A/n)^2+2*L^2*V) :
    Real.sqrt I ≤ 2*(A/n+L*Real.sqrt V) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs : (L*Real.sqrt V)^2 = L^2*V := by rw [mul_pow,Real.sq_sqrt hV]
  have hp := mul_nonneg (div_nonneg hA hn.le) (mul_nonneg hL (Real.sqrt_nonneg V))
  nlinarith [sq_nonneg (A/n),sq_nonneg (L*Real.sqrt V)]

/-- The finite physical cavity contribution is bounded by the actual scalar
RS potential, with one constant uniform in dimension, background posterior,
and last-spin prior. No overlap-concentration premise is used. -/
theorem exists_conditional_scalar_error_constant (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k)
    {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
      (p : Measure S) [IsProbabilityMeasure p],
      mixtureFreeEnergy (q.prod p) (fun z ↦ a z.2 • cavitySignal a N k gamma z.1)-
        mixtureFreeEnergy q (correctionSignal a N k gamma) ≤
      scalarPotential p a k gamma (meanOverlap q a)+C*(1/(N : ℝ)+Real.sqrt (replicaVariance q a)) := by
  let A := gamma*(k : ℝ)*(((k-1 : ℕ) : ℝ)^2+((k-1 : ℕ) : ℝ))*K^(2*(k-1))
  let L := (k : ℝ)*gamma*((k-1 : ℕ) : ℝ)*(K^2)^(k-2)
  let B := gamma*(((k-1 : ℕ) : ℝ)*(k : ℝ)^2+((k-1 : ℕ) : ℝ)^2)*K^(2*k)
  let M := ((k-1 : ℕ) : ℝ)*gamma*(k : ℝ)*(K^2)^(k-1)
  let Ef := (1/2 : ℝ)*Real.exp (22*(2*(K*Real.sqrt ((Nat.factorial k : ℝ)*gamma*K^(2*(k-1)))))^2)
  let Ec := (1/2 : ℝ)*Real.exp (22*(2*Real.sqrt ((Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)*K^(2*k)))^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hEf : 0 ≤ Ef := by dsimp [Ef]; positivity
  have hEc : 0 ≤ Ec := by dsimp [Ec]; positivity
  refine ⟨Ef*K^2*2*(A+L)+Ec*2*(B+M), by positivity, ?_⟩
  intro N hN q _ p _
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hV : 0 ≤ replicaVariance q a := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hf := fresh_freeEnergy_scalar_error_le (k := k) q p a hN (by omega) hgamma hK hb
  have hc := correction_freeEnergy_scalar_error_le q a hN hk hgamma hK hb
  have hIf := cavitySignal_centered_sq_integral_le q a hN hk hgamma hK hb
  have hIc := correctionSignal_centered_sq_integral_le q a hN hk hgamma hK hb
  have hsf := sqrt_remainder_le hA hL hV hn hIf
  have hsc := sqrt_remainder_le hB hM hV hn hIc
  have hK4 : Real.sqrt (K^4) = K^2 := by
    rw [show K^4 = (K^2)^2 by ring,Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg K)]
  rw [Real.sqrt_mul (by positivity : 0 ≤ K^4),hK4] at hf
  have hf' := hf.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsf (sq_nonneg K)) hEf)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hsc hEc)
  have hAf : A/(N : ℝ)+L*Real.sqrt (replicaVariance q a) ≤
      (A+L)*(1/(N : ℝ)+Real.sqrt (replicaVariance q a)) := by
    calc
      _ = A*(1/(N : ℝ))+L*Real.sqrt (replicaVariance q a) := by ring
      _ ≤ A*(1/(N : ℝ)+Real.sqrt (replicaVariance q a))+
          L*(1/(N : ℝ)+Real.sqrt (replicaVariance q a)) := add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hA)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (one_div_nonneg.mpr hn.le)) hL)
      _ = _ := by ring
  have hAc : B/(N : ℝ)+M*Real.sqrt (replicaVariance q a) ≤
      (B+M)*(1/(N : ℝ)+Real.sqrt (replicaVariance q a)) := by
    calc
      _ = B*(1/(N : ℝ))+M*Real.sqrt (replicaVariance q a) := by ring
      _ ≤ B*(1/(N : ℝ)+Real.sqrt (replicaVariance q a))+
          M*(1/(N : ℝ)+Real.sqrt (replicaVariance q a)) := add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hB)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (one_div_nonneg.mpr hn.le)) hM)
      _ = _ := by ring
  have hf'' := hf'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAf
      (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg K)) hEf)
  have hc'' := hc'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hAc (by norm_num : (0 : ℝ) ≤ 2)) hEc)
  have Hf := (le_abs_self _).trans hf''
  have Hc := (neg_le_abs _).trans hc''
  change _ ≤ Ef*(K^2*(2*((A+L)*(1/(N : ℝ)+Real.sqrt (replicaVariance q a))))) at Hf
  change _ ≤ Ec*(2*((B+M)*(1/(N : ℝ)+Real.sqrt (replicaVariance q a)))) at Hc
  dsimp only [scalarPotential]
  nlinarith only [Hf,Hc]

end
end TensorPCA.FinitePriorCavityScalarErrorProofs
