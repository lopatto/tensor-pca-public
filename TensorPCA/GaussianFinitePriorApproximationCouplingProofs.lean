-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationTensorProofs
public import TensorPCA.GaussianTensorMomentProofs

/-! Coordinatewise Gaussian quantization with dimension-normalized moment
control. Coordinate marginal laws suffice for the fourth error estimate;
no independence is assumed between the Gaussian norm and its clipping error. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationCouplingProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianFinitePriorApproximationProofs
open GaussianFinitePriorApproximationMomentProofs GaussianFinitePriorApproximationTensorProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

def quantizeVector (N j : ℕ) (g : Model.Vector N) : Model.Vector N :=
  WithLp.toLp 2 (fun i ↦ gaussianQuantizer j (g i))

theorem quantizeVector_measurable (N j : ℕ) : Measurable (quantizeVector N j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N ↦ ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  exact (gaussianQuantizer_measurable j).comp (PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).measurable

theorem quantizeVector_norm_le (N j : ℕ) (g : Model.Vector N) : ‖quantizeVector N j g‖ ≤ ‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _hi
  change (gaussianQuantizer j (g i))^2 ≤ (g i)^2
  have H := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (gaussianQuantizer_abs_le j (g i))
  simpa only [sq_abs] using H

theorem quantizeVector_error_norm_le (N j : ℕ) (g : Model.Vector N) : ‖quantizeVector N j g-g‖ ≤ ‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _hi
  change (gaussianQuantizer j (g i)-g i)^2 ≤ (g i)^2
  have H := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
    (clipRound_error_le_abs (j+1) (D := (j+1)^(j+1)) (pow_pos (Nat.succ_pos j) (j+1)) (g i))
  simpa only [sq_abs,gaussianQuantizer] using H

theorem quantizeVector_memLp (N j : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (quantizeVector N j) p (stdGaussian (Model.Vector N)) := by
  apply ((IsGaussian.memLp_id (stdGaussian (Model.Vector N)) p hp).norm).mono'
    (quantizeVector_measurable N j).aestronglyMeasurable
  exact Eventually.of_forall (fun g ↦ quantizeVector_norm_le N j g)

theorem quantizeVector_error_memLp (N j : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun g ↦ quantizeVector N j g-g) p (stdGaussian (Model.Vector N)) := by
  apply ((IsGaussian.memLp_id (stdGaussian (Model.Vector N)) p hp).norm).mono'
    ((quantizeVector_measurable N j).sub measurable_id).aestronglyMeasurable
  exact Eventually.of_forall (fun g ↦ quantizeVector_error_norm_le N j g)

theorem quantizeVector_clip_norm_le (N j : ℕ) (g : Model.Vector N) :
    ‖quantizeVector N j g‖ ≤ Real.sqrt N*((j : ℝ)+1) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  have H : (∑ i : Fin N,(quantizeVector N j g i)^2) ≤ ∑ _i : Fin N,((j : ℝ)+1)^2 := by
    apply Finset.sum_le_sum
    intro i _hi
    have HH := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (gaussianQuantizer_abs_le_bound j (g i))
    simpa only [sq_abs,quantizeVector] using HH
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

theorem vector_error_fourth_le_sum (N j : ℕ) (g : Model.Vector N) :
    ‖quantizeVector N j g-g‖^4 ≤ (N : ℝ)*∑ i : Fin N,|gaussianQuantizer j (g i)-g i|^4 := by
  have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _i : Fin N ↦ (1 : ℝ))
    (fun i : Fin N ↦ (gaussianQuantizer j (g i)-g i)^2)
  have he : ‖quantizeVector N j g-g‖^2 = ∑ i : Fin N,(gaussianQuantizer j (g i)-g i)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,he]
  simpa only [one_mul,mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← pow_mul,Nat.reduceMul,show ∀ z : ℝ,|z|^4 = z^4 from fun z ↦ by rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,pow_mul,sq_abs]] using H

/-- A fixed normalized Gaussian radius moment has a uniform dimension bound. -/
theorem normalized_radius_even_moment_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (∫ g : Model.Vector N,(‖g‖/Real.sqrt N)^(2*r) ∂stdGaussian (Model.Vector N)) ≤
      ∏ i ∈ Finset.range r,(1+2*(i : ℝ)) := by
  rw [GaussianMomentProofs.normalized_radius_even_moment hN r]
  apply Finset.prod_le_prod₀ (fun _i _hi ↦ by positivity)
  intro i _hi
  apply add_le_add (le_refl (1 : ℝ))
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ i from Nat.cast_nonneg i) (sub_nonneg.mpr hn)]

theorem scalar_error_fourth_integrable (j : ℕ) :
    Integrable (fun x : ℝ ↦ |gaussianQuantizer j x-x|^4) (stdGaussian ℝ) := by
  apply (gaussian_abs_pow_integrable 4).mono'
    ((continuous_abs.measurable.comp ((gaussianQuantizer_measurable j).sub measurable_id)).pow_const 4).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (clipRound_error_le_abs (j+1) (D := (j+1)^(j+1)) (pow_pos (Nat.succ_pos j) _) x) 4)

theorem coordinate_error_fourth_integrable {N : ℕ} (j : ℕ) (i : Fin N) :
    Integrable (fun g : Model.Vector N ↦ |gaussianQuantizer j (g i)-g i|^4)
      (stdGaussian (Model.Vector N)) := by
  have hmp : MeasurePreserving (fun g : Model.Vector N ↦ g i) (stdGaussian (Model.Vector N)) (stdGaussian ℝ) :=
    ⟨(PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).measurable,GaussianTensorMomentProofs.gaussian_coordinate_law i⟩
  exact hmp.integrable_comp_of_integrable (scalar_error_fourth_integrable j)

theorem coordinate_error_fourth_integral {N : ℕ} (j : ℕ) (i : Fin N) :
    (∫ g : Model.Vector N,|gaussianQuantizer j (g i)-g i|^4 ∂stdGaussian (Model.Vector N)) =
      ∫ x : ℝ,|gaussianQuantizer j x-x|^4 ∂stdGaussian ℝ := by
  have hm : AEStronglyMeasurable (fun x : ℝ ↦ |gaussianQuantizer j x-x|^4)
      ((stdGaussian (Model.Vector N)).map (fun g ↦ g i)) := by
    rw [GaussianTensorMomentProofs.gaussian_coordinate_law i]
    exact (scalar_error_fourth_integrable j).aestronglyMeasurable
  have H := integral_map (PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).measurable.aemeasurable hm
  rw [GaussianTensorMomentProofs.gaussian_coordinate_law i] at H
  exact H.symm

theorem vector_error_fourth_integral_le (N j : ℕ) :
    (∫ g : Model.Vector N,‖quantizeVector N j g-g‖^4 ∂stdGaussian (Model.Vector N)) ≤
      (N : ℝ)^2*(∫ x : ℝ,|gaussianQuantizer j x-x|^4 ∂stdGaussian ℝ) := by
  have hi := (quantizeVector_error_memLp N j 4 (by norm_num)).integrable_norm_pow'
  have hSum := integrable_finsetSum (Finset.univ : Finset (Fin N)) (fun i _hi ↦ coordinate_error_fourth_integrable (N := N) j i)
  have H := integral_mono hi (hSum.const_mul (N : ℝ)) (vector_error_fourth_le_sum N j)
  rw [integral_const_mul,integral_finsetSum (Finset.univ : Finset (Fin N)) (fun i _hi ↦ coordinate_error_fourth_integrable (N := N) j i)] at H
  simp_rw [coordinate_error_fourth_integral] at H
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
  nlinarith only [H]

theorem gaussianFourthRootError_pow_four (j : ℕ) :
    (gaussianFourthRootError j)^4 = ∫ x : ℝ,|gaussianQuantizer j x-x|^4 ∂stdGaussian ℝ := by
  have hp : 0 ≤ ∫ x : ℝ,|gaussianQuantizer j x-x|^4 ∂stdGaussian ℝ :=
    integral_nonneg (fun x ↦ by change 0 ≤ |gaussianQuantizer j x-x|^4; positivity)
  rw [gaussianFourthRootError,show (4 : ℕ) = 2*2 from rfl,pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt hp]

/-- The normalized vector's true fourth error is uniformly bounded by its
one-coordinate scalar fourth error, with no independence between the errors. -/
theorem normalized_vector_error_fourth_le {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (∫ g : Model.Vector N,(‖quantizeVector N j g-g‖/Real.sqrt N)^4 ∂stdGaussian (Model.Vector N)) ≤
      (gaussianFourthRootError j)^4 := by
  simp_rw [div_pow]
  rw [integral_div,show (Real.sqrt (N : ℝ))^4 = (N : ℝ)^2 from by
    rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sq_sqrt (Nat.cast_nonneg N)],gaussianFourthRootError_pow_four]
  exact (div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hN))).mpr
    ((vector_error_fourth_integral_le N j).trans_eq (mul_comm _ _))

end
end TensorPCA.GaussianFinitePriorApproximationCouplingProofs
