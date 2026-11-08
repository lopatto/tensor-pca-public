-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Exact scaling API follows the immutable source GOEScaling.lean,
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e.
   The law proof here uses the literal independent upper Gaussian entries,
   avoiding the source's unrelated spectral import. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GOERawMoments
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEScaling
open MeasureTheory ProbabilityTheory SphericalGaussianJet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def scaleFactor (n N : ℕ) (b : ℝ) : ℝ := Real.sqrt (b*(n+1 : ℝ)/N)

lemma scaleFactor_pos (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 < b) :
    0 < scaleFactor n N b := by unfold scaleFactor; positivity

lemma scaleFactor_square (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    scaleFactor n N b^2 = b*(n+1 : ℝ)/N := by
  apply Real.sq_sqrt
  positivity

lemma scaleFactor_le_sqrt {n N : ℕ} (hN : 0 < N) (hmN : n+1 ≤ N) {b : ℝ} (hb : 0 ≤ b) :
    scaleFactor n N b ≤ Real.sqrt b := by
  apply Real.sqrt_le_sqrt
  apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hb

theorem goeLaw_map_scalar (m N : ℕ) {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    (goeLaw m N v).map (fun W => t • W) = goeLaw m N (t^2*v) := by
  classical
  let T : (UpperIndex m → ℝ) → UpperIndex m → ℝ := fun z ij => t*z ij
  have hT : Measurable T := measurable_pi_iff.mpr (fun ij => measurable_const.mul (measurable_pi_apply ij))
  have hC : Measurable (fun W : Matrix (Fin m) (Fin m) ℝ => t • W) := by fun_prop
  have heq : (fun W : Matrix (Fin m) (Fin m) ℝ => t • W) ∘ symmetricMatrix = symmetricMatrix ∘ T := by
    funext z
    ext i j
    simp only [Function.comp_def, Matrix.smul_apply, smul_eq_mul, symmetricMatrix, T]
    split_ifs <;> rfl
  unfold goeLaw
  rw [Measure.map_map hC (symmetricMatrix_measurable m), heq,
    ← Measure.map_map (symmetricMatrix_measurable m) hT,
    Measure.pi_map_pi (f := fun _ (z : ℝ) => t*z) (fun _ => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  congr 1
  funext ij
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.coe_injective
  have hv0 : 0 ≤ (v/(N : ℝ))*(if ij.val.1=ij.val.2 then 2 else 1) := by split_ifs <;> positivity
  have hv1 : 0 ≤ ((t^2*v)/(N : ℝ))*(if ij.val.1=ij.val.2 then 2 else 1) := by split_ifs <;> positivity
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv0, Real.coe_toNNReal _ hv1]
  ring

theorem goeLaw_eq_of_div_eq (m N M : ℕ) {v b : ℝ} (h : v/(N : ℝ)=b/(M : ℝ)) :
    goeLaw m N v = goeLaw m M b := by
  unfold goeLaw
  rw [h]

/-- Exact actual law scaling from standard matrix variance1/(n+1) to b/N. -/
theorem goeLaw_scale (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    (goeLaw (n+1) (n+1) 1).map (fun W => scaleFactor n N b • W) = goeLaw (n+1) N b := by
  rw [goeLaw_map_scalar (n+1) (n+1) (by norm_num) (scaleFactor n N b)]
  apply goeLaw_eq_of_div_eq
  rw [scaleFactor_square n hN hb, mul_one]
  have hm : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  simp only [Nat.cast_add, Nat.cast_one]

end
end TensorPCA.RetainedCountProofs.GOEScaling
