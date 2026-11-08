-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed Apache-2.0 source port:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/NegativeDefiniteOperators.lean
Retained static negativity/Borel/coordinate bodies are unchanged apart from
namespace/import prefixes. Unused spectral criteria are omitted, and no
spectral asymptotic premise is substituted. See repository LICENSE. -/
module

public import TensorPCA.RetainedCountProofs.SphereHessian
public import TensorPCA.RetainedCountProofs.GaussianMatrixOperators

/-! Strict quadratic negativity of operators: Borel measurability,
coordinate invariance, and the spectral criterion. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
open Set MeasureTheory
open TensorPCA.RetainedCountProofs.OAI.CriticalSK GOEAsymptotics
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def NegativeDefinite (T : E →L[ℝ] E) : Prop := ∀ v : E, v ≠ 0 → inner ℝ v (T v) < 0

omit [FiniteDimensional ℝ E] in
lemma negativeDefinite_iff_sphere (T : E →L[ℝ] E) :
    NegativeDefinite T ↔ ∀ u : ↥(Metric.sphere (0:E) 1), inner ℝ (u:E) (T u) < 0 := by
  constructor
  · intro h u
    apply h
    have hu : ‖(u:E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  · intro h v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hh := h ⟨‖v‖⁻¹ • v, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩
    change inner ℝ (‖v‖⁻¹ • v) (T (‖v‖⁻¹ • v)) < 0 at hh
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc] at hh
    have hp := mul_pos (inv_pos.mpr hn) (inv_pos.mpr hn)
    nlinarith

lemma isOpen_negativeDefinite : IsOpen {T : E →L[ℝ] E | NegativeDefinite T} := by
  let S := ↥(Metric.sphere (0:E) 1)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0:E) 1)
  have hc : Continuous (fun p : (E →L[ℝ] E) × S => inner ℝ (p.2:E) (p.1 p.2)) :=
    (continuous_subtype_val.comp continuous_snd).inner
      (continuous_fst.clm_apply (continuous_subtype_val.comp continuous_snd))
  have hclosed := isClosedMap_fst_of_compactSpace (X := E →L[ℝ] E) (Y := S)
    {p : (E →L[ℝ] E) × S | 0 ≤ inner ℝ (p.2:E) (p.1 p.2)}
    (isClosed_le (continuous_const (y := (0:ℝ))) hc)
  have he : {T : E →L[ℝ] E | NegativeDefinite T}ᶜ =
      Prod.fst '' {p : (E →L[ℝ] E) × S | 0 ≤ inner ℝ (p.2:E) (p.1 p.2)} := by
    ext T
    simp only [mem_compl_iff, mem_ofPred_eq, negativeDefinite_iff_sphere, not_forall,
      not_lt, mem_image, Prod.exists]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨T,u,hu,rfl⟩
    · rintro ⟨T',u,hu,rfl⟩
      exact ⟨u,hu⟩
  apply isClosed_compl_iff.mp
  rw [he]
  exact hclosed

lemma negativeDefinite_pullback_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F) (T : F →L[ℝ] F) :
    NegativeDefinite (SphereHessian.pullback e T) ↔ NegativeDefinite T := by
  have he (v : E) : inner ℝ v (SphereHessian.pullback e T v) = inner ℝ (e v) (T (e v)) := by
    exact (e : E →L[ℝ] F).adjoint_inner_right v (T (e v))
  constructor
  · intro h v hv
    have hh := h (e.symm v) (by intro h0; apply hv; simpa using congrArg e h0)
    rw [he, e.apply_symm_apply] at hh
    exact hh
  · intro h v hv
    rw [he]
    exact h (e v) (by intro h0; apply hv; exact e.injective (h0.trans (map_zero e).symm))


end
end TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
