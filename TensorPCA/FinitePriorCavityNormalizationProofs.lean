-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityFieldProofs

/-! Exact cavity correction variance and independent Gaussian mixing.
The correction is defined by the exact coefficient difference rather than an
asymptotic Taylor remainder. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityNormalizationProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open TensorOrbitAggregationProofs TensorOrbitCountProofs GaussianPriorTransferProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem aggregateCoefficient_sq {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    (aggregateCoefficient N k gamma)^2 = (Nat.factorial k : ℝ)*gamma/(N : ℝ)^(k-1) := by
  rw [aggregateCoefficient_eq_sqrt hN hk hgamma,Real.sq_sqrt (by positivity)]

theorem aggregateCoefficient_succ_sq_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    (aggregateCoefficient (N+1) k gamma)^2 ≤ (aggregateCoefficient N k gamma)^2 := by
  rw [aggregateCoefficient_sq (Nat.succ_pos N) hk hgamma,aggregateCoefficient_sq hN hk hgamma]
  apply div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hgamma) (by positivity)
  exact pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast Nat.le_succ N) (k-1)

def correctionCoefficient (N k : ℕ) (gamma : ℝ) : ℝ :=
  Real.sqrt ((aggregateCoefficient N k gamma)^2-(aggregateCoefficient (N+1) k gamma)^2)

theorem correctionCoefficient_sq {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    (correctionCoefficient N k gamma)^2 =
      (aggregateCoefficient N k gamma)^2-(aggregateCoefficient (N+1) k gamma)^2 := by
  exact Real.sq_sqrt (sub_nonneg.mpr (aggregateCoefficient_succ_sq_le hN hk hgamma))

theorem coefficient_variance_split {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    (aggregateCoefficient (N+1) k gamma)^2+(correctionCoefficient N k gamma)^2 =
      (aggregateCoefficient N k gamma)^2 := by
  rw [correctionCoefficient_sq hN hk hgamma]
  ring

theorem correctionCoefficient_variance {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    (correctionCoefficient N k gamma)^2 = (Nat.factorial k : ℝ)*gamma*
      ((N : ℝ)^(k-1))⁻¹-(Nat.factorial k : ℝ)*gamma*(((N+1 : ℕ) : ℝ)^(k-1))⁻¹ := by
  rw [correctionCoefficient_sq hN hk hgamma,aggregateCoefficient_sq hN hk hgamma,
    aggregateCoefficient_sq (Nat.succ_pos N) hk hgamma]
  simp only [div_eq_mul_inv]

section GaussianMix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

def gaussianMix (a b : ℝ) : (E × E) →L[ℝ] E :=
  a • ContinuousLinearMap.fst ℝ E E+b • ContinuousLinearMap.snd ℝ E E

/-- The exact independent Gaussian mixture used to recombine background and
correction noises, for every finite-dimensional real Hilbert coefficient space. -/
theorem gaussianMix_stdGaussian_map (a b : ℝ) (hab : a^2+b^2 = 1) :
    ((stdGaussian E).prod (stdGaussian E)).map (gaussianMix (E := E) a b) = stdGaussian E := by
  apply Measure.ext_of_charFunDual
  funext L
  have hleft : (L.comp (gaussianMix a b)).comp (ContinuousLinearMap.inl ℝ E E) = a • L := by
    ext x
    simp [gaussianMix]
  have hright : (L.comp (gaussianMix a b)).comp (ContinuousLinearMap.inr ℝ E E) = b • L := by
    ext x
    simp [gaussianMix]
  rw [charFunDual_map,charFunDual_prod,hleft,hright,charFunDual_stdGaussian,charFunDual_stdGaussian,
    charFunDual_stdGaussian,← Complex.exp_add]
  congr 1
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  norm_cast
  simp only [mul_pow,sq_abs]
  have H := congrArg (fun r : ℝ ↦ r*‖L‖^2) hab
  nlinarith only [H]
end GaussianMix

variable {S : Type*} [MeasurableSpace S]

def monomialSignal (a : S → ℝ) (N k : ℕ) (x : Fin N → S) : EuclideanSpace ℝ (KSubset N k) :=
  WithLp.toLp 2 (fun T ↦ ∏ i ∈ T.1, a (x i))

def correctionSignal (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) : EuclideanSpace ℝ (KSubset N k) :=
  correctionCoefficient N k gamma • monomialSignal a N k x

def correctionHamiltonian (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X x : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : ℝ :=
  inner ℝ (correctionSignal a N k gamma x) (correctionSignal a N k gamma X+w)-‖correctionSignal a N k gamma x‖^2/2

theorem tensorSignal_eq_monomial (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) :
    tensorSignal a N k gamma x = aggregateCoefficient N k gamma • monomialSignal a N k x := by
  ext T
  rfl

theorem backgroundSignal_eq_monomial (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) :
    backgroundSignal a N k gamma x = aggregateCoefficient (N+1) k gamma • monomialSignal a N k x := by
  ext T
  rfl

theorem aggregateCoefficient_pos {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < aggregateCoefficient N k gamma := by
  rw [aggregateCoefficient_eq_sqrt hN hk hgamma.le]
  apply Real.sqrt_pos.mpr
  positivity

theorem normalized_correction_weights {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma) :
    (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)^2+
      (correctionCoefficient N k gamma/aggregateCoefficient N k gamma)^2 = 1 := by
  rw [div_pow,div_pow,← add_div,coefficient_variance_split hN hk hgamma.le]
  exact div_self (pow_ne_zero 2 (aggregateCoefficient_pos hN hk hgamma).ne')

theorem correction_noise_gaussian_map {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ((stdGaussian (EuclideanSpace ℝ (KSubset N k))).prod (stdGaussian (EuclideanSpace ℝ (KSubset N k)))).map
      (gaussianMix (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
        (correctionCoefficient N k gamma/aggregateCoefficient N k gamma)) =
      stdGaussian (EuclideanSpace ℝ (KSubset N k)) :=
  gaussianMix_stdGaussian_map _ _ (normalized_correction_weights hN hk hgamma)

omit [MeasurableSpace S] in
theorem exponent_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (v X w : E) : inner ℝ (c • v) (c • X+w)-‖c • v‖^2/2 =
      c*inner ℝ v w+c^2*(inner ℝ v X-‖v‖^2/2) := by
  simp only [real_inner_smul_left,inner_add_right,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs]
  ring

/-- Exact y-channel decomposition of the N-variable Hamiltonian. Under the
independent Gaussian product law the recombined noise is canonical by the
preceding theorem, so this is the source's equality in law without Taylor error. -/
theorem plantedHamiltonian_background_correction {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) (X x : Fin N → S)
    (w0 w1 : EuclideanSpace ℝ (KSubset N k)) :
    backgroundHamiltonian a N k gamma X x w0+correctionHamiltonian a N k gamma X x w1 =
      plantedHamiltonian a N k gamma X x
        (gaussianMix (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
          (correctionCoefficient N k gamma/aggregateCoefficient N k gamma) (w0,w1)) := by
  have hc := (aggregateCoefficient_pos hN hk hgamma).ne'
  rw [backgroundHamiltonian,correctionHamiltonian,plantedHamiltonian]
  simp_rw [backgroundSignal_eq_monomial,tensorSignal_eq_monomial,correctionSignal,exponent_smul]
  simp only [gaussianMix,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul,inner_add_right,real_inner_smul_right]
  let D := inner ℝ (monomialSignal a N k x) (monomialSignal a N k X)-‖monomialSignal a N k x‖^2/2
  have hcd : aggregateCoefficient N k gamma*(aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma) =
      aggregateCoefficient (N+1) k gamma := by field_simp
  have hce : aggregateCoefficient N k gamma*(correctionCoefficient N k gamma/aggregateCoefficient N k gamma) =
      correctionCoefficient N k gamma := by field_simp
  rw [mul_add,← mul_assoc,hcd,← mul_assoc,hce]
  have H := congrArg (fun r : ℝ ↦ r*D) (coefficient_variance_split hN hk hgamma.le)
  dsimp only [D] at H
  nlinarith only [H]

end
end TensorPCA.FinitePriorCavityNormalizationProofs
