-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceLaw
public import TensorPCA.GroundUpperProofs

/-! Geometric identities for the frozen literal cavityReferenceMap. No new
reference map, normalized prior, or Gaussian-process assumption is introduced. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGeometry
open Set FiniteCavityReferenceLaw
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem append_inner {N M : ℕ} (x y : Model.Vector N) (eta eta' : Model.Vector M) :
    inner ℝ (WithLp.toLp 2 (Fin.addCases x eta) : Model.Vector (N+M))
      (WithLp.toLp 2 (Fin.addCases y eta'))=inner ℝ x y+inner ℝ eta eta' := by
  rw [PiLp.inner_apply,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,PiLp.inner_apply]

theorem scaled_append_inner {N M : ℕ} (x y : Model.Vector N) (eta eta' : Model.Vector M) (r r' : ℝ) :
    inner ℝ (WithLp.toLp 2 (Fin.addCases (r • x) eta) : Model.Vector (N+M))
      (WithLp.toLp 2 (Fin.addCases (r' • y) eta'))=r*r'*inner ℝ x y+inner ℝ eta eta' := by
  rw [append_inner]
  simp only [WithLp.toLp_smul,WithLp.toLp_ofLp]
  rw [real_inner_smul_left,real_inner_smul_right]
  ring

theorem scaled_append_norm_sq {N M : ℕ} (x : Model.Vector N) (eta : Model.Vector M) (r : ℝ) :
    ‖(WithLp.toLp 2 (Fin.addCases (r • x) eta) : Model.Vector (N+M))‖^2=
      r^2*‖x‖^2+‖eta‖^2 := by
  rw [← real_inner_self_eq_norm_sq,scaled_append_inner,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  ring

theorem scaled_append_norm_on_unit {N M : ℕ} {x : Model.Vector N}
    (hx : x∈Model.unitSphere N) (r : ℝ) (eta : Model.Vector M) :
    ‖(WithLp.toLp 2 (Fin.addCases (r • x) eta) : Model.Vector (N+M))‖=
      Real.sqrt (r^2+‖eta‖^2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
  rw [scaled_append_norm_sq,show ‖x‖=1 from hx,one_pow,mul_one,
    Real.sq_sqrt (by positivity : 0≤r^2+‖eta‖^2)]

/-- The identity includes the total zero-origin convention of Model.normalize;
positive retained radii are therefore a valid specialization. -/
theorem reference_inner {N M : ℕ} {x y : Model.Vector N}
    (hx : x∈Model.unitSphere N) (hy : y∈Model.unitSphere N)
    (r r' : ℝ) (eta eta' : Model.Vector M) :
    inner ℝ (cavityReferenceMap N M (x,(r,eta))) (cavityReferenceMap N M (y,(r',eta')))=
      (r*r'*inner ℝ x y+inner ℝ eta eta')/Real.sqrt ((r^2+‖eta‖^2)*(r'^2+‖eta'‖^2)) := by
  rw [cavityReferenceMap_eq,cavityReferenceMap_eq]
  unfold Model.normalize
  dsimp only
  simp only [WithLp.ofLp_smul]
  rw [real_inner_smul_left,real_inner_smul_right,
    scaled_append_norm_on_unit hx r eta,scaled_append_norm_on_unit hy r' eta',scaled_append_inner]
  rw [Real.sqrt_mul (by positivity : 0≤r^2+‖eta‖^2)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem reference_unit {N M : ℕ} {x : Model.Vector N} (hx : x∈Model.unitSphere N)
    {r : ℝ} (hr : 0<r) (eta : Model.Vector M) :
    cavityReferenceMap N M (x,(r,eta))∈Model.unitSphere (N+M) := by
  have hne : (WithLp.toLp 2 (Fin.addCases (r • x) eta) : Model.Vector (N+M))≠0 := by
    intro hz
    have hh := scaled_append_norm_sq x eta r
    rw [hz,norm_zero,zero_pow two_ne_zero,show ‖x‖=1 from hx,one_pow,mul_one] at hh
    nlinarith only [hh,sq_pos_of_pos hr,sq_nonneg ‖eta‖]
  exact Model.norm_normalize _ hne

theorem reference_sliceFeature_inner {N M : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) {x y : Model.Vector N}
    (hx : x∈Model.unitSphere N) (hy : y∈Model.unitSphere N)
    (r r' : ℝ) (eta eta' : Model.Vector M) :
    inner ℝ (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (x,(r,eta))))
      (beta • GroundState.sliceFeature k mu (cavityReferenceMap N M (y,(r',eta'))))=
      ((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu
        ((r*r'*inner ℝ x y+inner ℝ eta eta')/Real.sqrt ((r^2+‖eta‖^2)*(r'^2+‖eta'‖^2))) := by
  rw [real_inner_smul_left,real_inner_smul_right,GroundUpperProofs.sliceFeature_inner hmu,
    reference_inner hx hy,Nat.cast_add]
  ring


end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGeometry
