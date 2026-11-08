-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteEmpiricalNormalizer

/-! Dimension-free iid empirical mean bounds for genuinely square-integrable
marks. No pointwise supremum or Gaussian norm expectation enters the bound. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityEmpiricalMoments
open MeasureTheory ProbabilityTheory Filter
open GGFiniteEmpiricalNormalizer
open scoped BigOperators
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem empiricalMean_memLp (K : ℕ) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    MemLp (empiricalMean K Y) 2 (Measure.pi (fun _ : Fin K ↦ nu)) := by
  have hi (i : Fin K) : MemLp (fun s : Fin K → V ↦ Y (s i)) 2 (Measure.pi (fun _ : Fin K ↦ nu)) :=
    hY.comp_measurePreserving (measurePreserving_eval (fun _ : Fin K ↦ nu) i)
  have hSum := memLp_finsetSum Finset.univ (fun i _ ↦ hi i)
  change MemLp (fun s : Fin K → V ↦ ∑ i : Fin K,Y (s i)) 2 (Measure.pi (fun _ : Fin K ↦ nu)) at hSum
  have he : empiricalMean K Y=(fun s : Fin K → V ↦ (∑ i : Fin K,Y (s i))*(K : ℝ)⁻¹) := by
    funext s
    unfold empiricalMean
    ring
  rw [he]
  exact MemLp.mul_const hSum ((K : ℝ)⁻¹)

theorem empiricalMean_integral_memLp {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    (∫ s : Fin K → V,empiricalMean K Y s ∂Measure.pi (fun _ : Fin K ↦ nu))=∫ z,Y z ∂nu := by
  have hKR : (K : ℝ)≠0 := by exact_mod_cast hK.ne'
  have hI : Integrable Y nu := hY.integrable (by norm_num)
  have hi (i : Fin K) : Integrable (fun s : Fin K → V ↦ Y (s i)) (Measure.pi (fun _ : Fin K ↦ nu)) :=
    (measurePreserving_eval (fun _ : Fin K ↦ nu) i).hasLaw.integrable_comp hI
  have he (i : Fin K) : (∫ s : Fin K → V,Y (s i) ∂Measure.pi (fun _ : Fin K ↦ nu))=∫ z,Y z ∂nu :=
    (measurePreserving_eval (fun _ : Fin K ↦ nu) i).hasLaw.integral_comp hY.aestronglyMeasurable
  unfold empiricalMean
  rw [integral_div,integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem empiricalMean_variance_memLp {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    variance (empiricalMean K Y) (Measure.pi (fun _ : Fin K ↦ nu))=variance Y nu/(K : ℝ) := by
  have hKR : (K : ℝ)≠0 := by exact_mod_cast hK.ne'
  have H := variance_sum_pi (ι := Fin K) (μ := fun _ : Fin K ↦ nu) (X := fun _ : Fin K ↦ Y) (fun _ ↦ hY)
  have heval : (∑ i : Fin K,fun s : Fin K → V ↦ Y (s i))=(fun s : Fin K → V ↦ ∑ i : Fin K,Y (s i)) := by
    funext s
    simp only [Finset.sum_apply]
  rw [heval] at H
  have hs : variance (fun s : Fin K → V ↦ ∑ i : Fin K,Y (s i)) (Measure.pi (fun _ : Fin K ↦ nu))=
      (K : ℝ)*variance Y nu := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
  have he : empiricalMean K Y=(fun s : Fin K → V ↦ (1/(K : ℝ))*(∑ i : Fin K,Y (s i))) := by
    funext s
    unfold empiricalMean
    ring
  rw [he,variance_const_mul,hs]
  field_simp

theorem empiricalMean_centered_sq {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    (∫ s : Fin K → V,(empiricalMean K Y s-(∫ z,Y z ∂nu))^2 ∂Measure.pi (fun _ : Fin K ↦ nu))=
      variance Y nu/(K : ℝ) := by
  have H := empiricalMean_variance_memLp hK nu hY
  rw [variance_eq_integral (empiricalMean_memLp K nu hY).aestronglyMeasurable.aemeasurable,
    empiricalMean_integral_memLp hK nu hY] at H
  exact H

theorem empiricalMean_centered_sq_le {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    (∫ s : Fin K → V,(empiricalMean K Y s-(∫ z,Y z ∂nu))^2 ∂Measure.pi (fun _ : Fin K ↦ nu))≤
      (∫ z,(Y z)^2 ∂nu)/(K : ℝ) := by
  rw [empiricalMean_centered_sq hK nu hY]
  exact div_le_div_of_nonneg_right (variance_le_expectation_sq hY.aestronglyMeasurable) (Nat.cast_nonneg K)

theorem empiricalMean_L1_error_sq_le {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    (∫ s : Fin K → V,|empiricalMean K Y s-(∫ z,Y z ∂nu)| ∂Measure.pi (fun _ : Fin K ↦ nu))^2≤
      (∫ z,(Y z)^2 ∂nu)/(K : ℝ) := by
  let P := Measure.pi (fun _ : Fin K ↦ nu)
  let X := fun s : Fin K → V ↦ empiricalMean K Y s-(∫ z,Y z ∂nu)
  have hLpX : MemLp X 2 P := (empiricalMean_memLp K nu hY).sub (memLp_const _)
  have hAbs : MemLp (fun s ↦ |X s|) 2 P := by simpa only [Real.norm_eq_abs] using hLpX.norm
  have hCS : (∫ s,|X s| ∂P)^2≤∫ s,(X s)^2 ∂P := by
    have H := variance_nonneg (fun s ↦ |X s|) P
    rw [variance_eq_sub hAbs] at H
    change 0≤(∫ s,|X s|^2 ∂P)-(∫ s,|X s| ∂P)^2 at H
    simp only [sq_abs] at H
    linarith
  exact hCS.trans (empiricalMean_centered_sq_le hK nu hY)

theorem empiricalMean_L1_error_le {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : MemLp Y 2 nu) :
    (∫ s : Fin K → V,|empiricalMean K Y s-(∫ z,Y z ∂nu)| ∂Measure.pi (fun _ : Fin K ↦ nu))≤
      Real.sqrt (∫ z,(Y z)^2 ∂nu)/Real.sqrt (K : ℝ) := by
  have hKR : 0<(K : ℝ) := by exact_mod_cast hK
  have hSq : (Real.sqrt (∫ z,(Y z)^2 ∂nu)/Real.sqrt (K : ℝ))^2=(∫ z,(Y z)^2 ∂nu)/(K : ℝ) := by
    rw [div_pow,Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),Real.sq_sqrt hKR.le]
  apply (sq_le_sq₀ (integral_nonneg (fun _ ↦ abs_nonneg _)) (by positivity)).mp
  exact (empiricalMean_L1_error_sq_le hK nu hY).trans_eq hSq.symm

end
end TensorPCA.NonRSLowerProofs.FiniteCavityEmpiricalMoments
