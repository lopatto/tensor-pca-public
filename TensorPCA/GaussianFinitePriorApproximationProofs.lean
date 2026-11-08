-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianMomentProofs

/-! Explicit finite-valued Gaussian quantizers. Clipping and rounding toward
zero preserve every absolute moment; the mesh will decrease faster than every
fixed power of the clipping radius. These are finite prior laws, not
free-energy convergence hypotheses. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
noncomputable section

/-- The nonnegative clipped grid magnitude; D is the mesh denominator. -/
def clipMagnitude (B D : ℕ) (x : ℝ) : ℝ :=
  ((min (B*D) ⌊(D : ℝ)*|x|⌋₊ : ℕ) : ℝ)/(D : ℝ)

/-- Clip at B and round toward zero on the exact mesh 1/D. -/
def clipRound (B D : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then -clipMagnitude B D x else clipMagnitude B D x

theorem clipMagnitude_nonneg (B D : ℕ) (x : ℝ) : 0 ≤ clipMagnitude B D x := by
  unfold clipMagnitude
  positivity

theorem clipMagnitude_le_abs (B : ℕ) {D : ℕ} (hD : 0 < D) (x : ℝ) :
    clipMagnitude B D x ≤ |x| := by
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  apply (div_le_iff₀ hd).mpr
  have hm : ((min (B*D) ⌊(D : ℝ)*|x|⌋₊ : ℕ) : ℝ) ≤ (⌊(D : ℝ)*|x|⌋₊ : ℝ) := by
    exact_mod_cast Nat.min_le_right (B*D) ⌊(D : ℝ)*|x|⌋₊
  exact hm.trans ((Nat.floor_le (mul_nonneg hd.le (abs_nonneg x))).trans_eq (mul_comm _ _))

theorem clipMagnitude_le_bound (B : ℕ) {D : ℕ} (hD : 0 < D) (x : ℝ) :
    clipMagnitude B D x ≤ B := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hD)).mpr
  exact_mod_cast Nat.min_le_left (B*D) ⌊(D : ℝ)*|x|⌋₊

theorem abs_clipRound (B D : ℕ) (x : ℝ) : |clipRound B D x| = clipMagnitude B D x := by
  unfold clipRound
  split_ifs <;> simp only [abs_neg,abs_of_nonneg (clipMagnitude_nonneg B D x)]

theorem clipRound_abs_le (B : ℕ) {D : ℕ} (hD : 0 < D) (x : ℝ) : |clipRound B D x| ≤ |x| := by
  rw [abs_clipRound]
  exact clipMagnitude_le_abs B hD x

theorem clipRound_abs_le_bound (B : ℕ) {D : ℕ} (hD : 0 < D) (x : ℝ) : |clipRound B D x| ≤ B := by
  rw [abs_clipRound]
  exact clipMagnitude_le_bound B hD x

theorem clipMagnitude_measurable (B D : ℕ) : Measurable (clipMagnitude B D) := by
  have hf : Measurable (fun x : ℝ ↦ ⌊(D : ℝ)*|x|⌋₊) :=
    (Nat.floor_mono : Monotone (Nat.floor : ℝ → ℕ)).measurable.comp (measurable_const.mul continuous_abs.measurable)
  have hm : Measurable (fun x : ℝ ↦ min (B*D) ⌊(D : ℝ)*|x|⌋₊) := measurable_const.min hf
  exact ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp hm).div_const D

theorem clipRound_measurable (B D : ℕ) : Measurable (clipRound B D) := by
  exact (clipMagnitude_measurable B D).neg.piecewise measurableSet_Iio (clipMagnitude_measurable B D)

theorem clipRound_finite_range (B D : ℕ) : (Set.range (clipRound B D)).Finite := by
  let I := {n : ℕ | n ≤ B*D}
  have hI : I.Finite := finite_Iic _
  let A := (fun n : ℕ ↦ (n : ℝ)/(D : ℝ)) '' I
  have hA : A.Finite := hI.image _
  have hUnion := (hA.image (fun r : ℝ ↦ -r)).union hA
  apply hUnion.subset
  rintro z ⟨x,rfl⟩
  have hr : clipMagnitude B D x ∈ A :=
    ⟨min (B*D) ⌊(D : ℝ)*|x|⌋₊,Nat.min_le_left _ _,rfl⟩
  unfold clipRound
  split_ifs
  · exact Or.inl ⟨_,hr,rfl⟩
  · exact Or.inr hr

theorem clipRound_error_eq (B : ℕ) {D : ℕ} (hD : 0 < D) (x : ℝ) :
    |clipRound B D x-x| = |x|-clipMagnitude B D x := by
  have hmag := clipMagnitude_le_abs B hD x
  by_cases hx : x < 0
  · rw [abs_of_neg hx] at hmag
    rw [clipRound,ite_eq_left hx,abs_of_neg hx,abs_of_nonneg (by linarith : 0 ≤ -clipMagnitude B D x-x)]
    ring
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    rw [abs_of_nonneg hx0] at hmag
    rw [clipRound,ite_eq_right hx,abs_of_nonneg hx0,abs_of_nonpos (by linarith : clipMagnitude B D x-x ≤ 0)]
    ring

theorem clipRound_error_le_abs (B : ℕ) {D : ℕ} (hD : 0 < D) (x : ℝ) :
    |clipRound B D x-x| ≤ |x| := by
  rw [clipRound_error_eq B hD]
  exact sub_le_self _ (clipMagnitude_nonneg B D x)

/-- Within the clipping radius, only the exact one-grid-step error remains. -/
theorem clipRound_error_le_mesh (B : ℕ) {D : ℕ} (hD : 0 < D) {x : ℝ} (hx : |x| ≤ B) :
    |clipRound B D x-x| ≤ 1/(D : ℝ) := by
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hfloor : ⌊(D : ℝ)*|x|⌋₊ ≤ B*D := Nat.floor_le_of_le (by
    rw [Nat.cast_mul]
    nlinarith)
  rw [clipRound_error_eq B hD,clipMagnitude,min_eq_right hfloor]
  have h := (Nat.lt_floor_add_one (|x| *(D : ℝ))).le
  apply (le_div_iff₀ hd).mpr
  field_simp
  nlinarith

/-- One explicit sequence, independent of the tensor order. Its mesh is
B^(-B) at clipping radius B=j+1. -/
def gaussianQuantizer (j : ℕ) : ℝ → ℝ := clipRound (j+1) ((j+1)^(j+1))

def finiteGaussianPrior (j : ℕ) : Measure ℝ := (stdGaussian ℝ).map (gaussianQuantizer j)

theorem gaussianQuantizer_measurable (j : ℕ) : Measurable (gaussianQuantizer j) := clipRound_measurable _ _

theorem gaussianQuantizer_finite_range (j : ℕ) : (Set.range (gaussianQuantizer j)).Finite := clipRound_finite_range _ _

theorem gaussianQuantizer_abs_le (j : ℕ) (x : ℝ) : |gaussianQuantizer j x| ≤ |x| :=
  clipRound_abs_le _ (pow_pos (Nat.succ_pos j) _) x

theorem gaussianQuantizer_abs_le_bound (j : ℕ) (x : ℝ) : |gaussianQuantizer j x| ≤ (j : ℝ)+1 := by
  simpa only [gaussianQuantizer,Nat.cast_add,Nat.cast_one] using clipRound_abs_le_bound (j+1) (pow_pos (Nat.succ_pos j) _) x

instance finiteGaussianPrior_probability (j : ℕ) : IsProbabilityMeasure (finiteGaussianPrior j) := by
  unfold finiteGaussianPrior
  exact (Measure.isProbabilityMeasure_map_iff (gaussianQuantizer_measurable j).aemeasurable).mpr inferInstance

/-- The actual pushed-forward Gaussian is supported on a proved finite set. -/
theorem finiteGaussianPrior_finite_support (j : ℕ) :
    ∃ S : Set ℝ, S.Finite ∧ finiteGaussianPrior j Sᶜ = 0 := by
  refine ⟨Set.range (gaussianQuantizer j),gaussianQuantizer_finite_range j,?_⟩
  rw [finiteGaussianPrior,Measure.map_apply (gaussianQuantizer_measurable j)
    (gaussianQuantizer_finite_range j).measurableSet.compl]
  have hpre : (gaussianQuantizer j) ⁻¹' (Set.range (gaussianQuantizer j))ᶜ = ∅ := by
    ext x
    simp only [mem_preimage,mem_compl_iff,mem_range,not_exists,mem_empty_iff_false]
    exact ⟨fun h ↦ h x rfl,fun h ↦ h.elim⟩
  rw [hpre,measure_empty]

theorem gaussianQuantizer_tendsto (x : ℝ) : Tendsto (fun j ↦ gaussianQuantizer j x) atTop (𝓝 x) := by
  have hnear : ∀ᶠ j : ℕ in atTop, |gaussianQuantizer j x-x| ≤ (1 : ℝ)/((j : ℝ)+1) := by
    obtain ⟨J,hJ⟩ := exists_nat_gt |x|
    filter_upwards [eventually_ge_atTop J] with j hj
    have hx : |x| ≤ ((j+1 : ℕ) : ℝ) := by
      have hcast : (J : ℝ) ≤ j := Nat.cast_le.mpr hj
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
    have hD : 0 < (j+1)^(j+1) := pow_pos (Nat.succ_pos j) _
    have hBD : j+1 ≤ (j+1)^(j+1) := le_self_pow₀ (by omega) (by omega)
    apply (clipRound_error_le_mesh (j+1) hD hx).trans
    have hc : ((j+1 : ℕ) : ℝ) ≤ ((j+1)^(j+1) : ℕ) := Nat.cast_le.mpr hBD
    have H : (1 : ℝ)/(((j+1)^(j+1) : ℕ) : ℝ) ≤ 1/((j+1 : ℕ) : ℝ) :=
      (div_le_div_iff₀ (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr (Nat.succ_pos j))).mpr
        (by simpa only [one_mul] using hc)
    simpa only [one_mul,mul_one,Nat.cast_add,Nat.cast_one] using H
  have hz : Tendsto (fun j ↦ |gaussianQuantizer j x-x|) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall (fun j ↦ abs_nonneg _)) hnear tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using hz

theorem gaussianQuantizer_memLp_two (j : ℕ) : MemLp (gaussianQuantizer j) 2 (stdGaussian ℝ) := by
  apply ((IsGaussian.memLp_two_id : MemLp (id : ℝ → ℝ) 2 (stdGaussian ℝ)).norm).mono'
    (gaussianQuantizer_measurable j).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by simpa only [id_eq,Real.norm_eq_abs] using gaussianQuantizer_abs_le j x)

/-- Rounding toward zero preserves the variance-normalization upper bound. -/
theorem finiteGaussianPrior_second_moment_le_one (j : ℕ) :
    (∫ x : ℝ,x^2 ∂finiteGaussianPrior j) ≤ 1 := by
  rw [finiteGaussianPrior,integral_map (gaussianQuantizer_measurable j).aemeasurable (by fun_prop)]
  have hi : Integrable (fun x : ℝ ↦ x^2) (stdGaussian ℝ) := IsGaussian.memLp_two_id.integrable_sq
  have H := integral_mono (gaussianQuantizer_memLp_two j).integrable_sq hi (fun x ↦ by
    have hh := (sq_le_sq₀ (abs_nonneg (gaussianQuantizer j x)) (abs_nonneg x)).mpr (gaussianQuantizer_abs_le j x)
    simpa only [sq_abs] using hh)
  have he : (∫ x : ℝ,x^2 ∂stdGaussian ℝ) = 1 := by
    simpa [Real.norm_eq_abs,GaussianMomentProofs.radialMomentProduct] using
      (GaussianMomentProofs.gaussian_radius_even_moment (E := ℝ) 1)
  exact H.trans_eq he

end
end TensorPCA.GaussianFinitePriorApproximationProofs
