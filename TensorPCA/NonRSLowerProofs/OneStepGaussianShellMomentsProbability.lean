-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianShellMoments

/-! Finite Gaussian shell and field-cutoff probability estimates.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianShellMoments
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem shifted_norm_sq_centered_tail (u : Model.Vector N) (s : ℝ) {t : ℝ}
    (ht : 0 < t) :
    (stdGaussian (Model.Vector N)).real
      {g | t ≤ |‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ))|} ≤
      (8*s^2*‖u‖^2+4*s^4*(N : ℝ))/t^2 := by
  let F : Model.Vector N → ℝ := fun g => ‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ))
  have hi : Integrable (fun g => (F g)^2) (stdGaussian (Model.Vector N)) :=
    ((norm_shift_sq_memLp_two u s).sub (memLp_const _)).integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun g => sq_nonneg (F g))) hi (t^2)
  have hsub : {g : Model.Vector N | t ≤ |F g|} ⊆ {g | t^2 ≤ (F g)^2} := by
    intro g hg
    change t^2 ≤ (F g)^2
    simpa only [sq_abs] using (sq_le_sq₀ ht.le (abs_nonneg (F g))).mpr hg
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = t^2*(stdGaussian (Model.Vector N)).real {g | t ≤ |F g|} := by dsimp [F]; ring
    _ ≤ t^2*(stdGaussian (Model.Vector N)).real {g | t^2 ≤ (F g)^2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg t)
    _ ≤ ∫ g, (F g)^2 ∂stdGaussian (Model.Vector N) := hm
    _ ≤ _ := integral_centered_norm_shift_sq_le u s

theorem shifted_norm_tail (u : Model.Vector N) (s : ℝ) {R : ℝ} (hR : 0 < R) :
    (stdGaussian (Model.Vector N)).real {g | R < ‖u+s • g‖} ≤
      (‖u‖^2+s^2*(N : ℝ))/R^2 := by
  have hi : Integrable (fun g : Model.Vector N => ‖u+s • g‖^2)
      (stdGaussian (Model.Vector N)) := (norm_shift_sq_memLp_two u s).integrable one_le_two
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun g : Model.Vector N => sq_nonneg ‖u+s • g‖)) hi (R^2)
  have hsub : {g : Model.Vector N | R < ‖u+s • g‖} ⊆ {g | R^2 ≤ ‖u+s • g‖^2} := by
    intro g hg
    exact ((sq_lt_sq₀ hR.le (norm_nonneg _)).mpr hg).le
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  calc
    _ = R^2*(stdGaussian (Model.Vector N)).real {g | R < ‖u+s • g‖} := by ring
    _ ≤ R^2*(stdGaussian (Model.Vector N)).real {g | R^2 ≤ ‖u+s • g‖^2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg R)
    _ ≤ ∫ g, ‖u+s • g‖^2 ∂stdGaussian (Model.Vector N) := hm
    _ = _ := integral_norm_shift_sq u s

theorem shifted_shell_bad_mass_le (u : Model.Vector N) (s : ℝ)
    (hN : 0 < N) {eps : ℝ} (heps : 0 < eps)
    (hbias : |‖u‖^2+s^2*(N : ℝ)-(N : ℝ)| ≤ eps*(N : ℝ)/2) :
    (stdGaussian (Model.Vector N)).real
      {g | eps*(N : ℝ) < |‖u+s • g‖^2-(N : ℝ)|} ≤
      (8*s^2*‖u‖^2+4*s^4*(N : ℝ))/(eps*(N : ℝ)/2)^2 := by
  have ht : 0 < eps*(N : ℝ)/2 := by positivity
  have hsub : {g : Model.Vector N | eps*(N : ℝ) < |‖u+s • g‖^2-(N : ℝ)|} ⊆
      {g | eps*(N : ℝ)/2 ≤ |‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ))|} := by
    intro g hg
    have htri := abs_sub_le (‖u+s • g‖^2) (‖u‖^2+s^2*(N : ℝ)) (N : ℝ)
    change eps*(N : ℝ) < |‖u+s • g‖^2-(N : ℝ)| at hg
    change eps*(N : ℝ)/2 ≤ |‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ))|
    linarith
  exact (measureReal_mono hsub).trans (shifted_norm_sq_centered_tail u s ht)


end
end TensorPCA.NonRSLowerProofs.OneStepGaussianShellMoments
