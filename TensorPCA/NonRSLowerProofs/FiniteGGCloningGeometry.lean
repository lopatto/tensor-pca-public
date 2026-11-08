-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGBarycenterGeometry

/-! Deterministic margins for finite cloning windows. Centers are arbitrary real numbers
approximating unit-vector overlaps, so the window error is retained in the upper
margin for the largest center.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGCloningGeometry
open RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem window_center_upper_margin {eps g a b c : ℝ}
    (heps : 0≤eps) (hGap : 2*eps≤g) (hab : g≤b-a)
    (x y z : E) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1)
    (hxy : |inner ℝ x y-a|≤eps) (hxz : |inner ℝ x z-b|≤eps)
    (hyz : |inner ℝ y z-c|≤eps) :
    c≤1+eps-(g-2*eps)^2/2 := by
  have hDiff : g-2*eps≤ inner ℝ x z-inner ℝ x y := by
    linarith only [(abs_le.mp hxy).2,(abs_le.mp hxz).1,hab]
  have hNon : 0≤g-2*eps := by linarith only [hGap]
  have hCauchy : |inner ℝ x z-inner ℝ x y|≤‖z-y‖ := by
    rw [← inner_sub_right]
    simpa only [hx,one_mul] using abs_real_inner_le_norm x (z-y)
  have hBound : g-2*eps≤‖z-y‖ := hDiff.trans ((le_abs_self _).trans hCauchy)
  have hSquare : (g-2*eps)^2≤‖z-y‖^2 := by
    exact (sq_le_sq₀ hNon (norm_nonneg _)).mpr hBound
  have hNorm : ‖z-y‖^2=2-2*inner ℝ y z := by
    rw [norm_sub_sq_real,hz,hy]
    rw [real_inner_comm z y]
    ring
  rw [hNorm] at hSquare
  linarith only [hSquare,(abs_le.mp hyz).1]

theorem window_center_uniform_margin {eps g a b c : ℝ}
    (heps : 0≤eps) (hg : 0<g) (hepsG : eps≤g/16) (hepsSq : eps≤g^2/128) (hab : g≤b-a)
    (x y z : E) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1)
    (hxy : |inner ℝ x y-a|≤eps) (hxz : |inner ℝ x z-b|≤eps)
    (hyz : |inner ℝ y z-c|≤eps) : c≤1-3*g^2/8 := by
  have hGap : 2*eps≤g := by linarith only [hepsG,hg]
  have hLower : 7*g/8≤g-2*eps := by linarith only [hepsG]
  have hNon : 0≤g-2*eps := by linarith only [hGap]
  have hSquare : (7*g/8)^2≤(g-2*eps)^2 :=
    (sq_le_sq₀ (by positivity : 0≤7*g/8) hNon).mpr hLower
  have H := window_center_upper_margin heps hGap hab x y z hx hy hz hxy hxz hyz
  nlinarith only [H,hSquare,hepsSq]

theorem exists_barycenter_contradiction_budget {g : ℝ} (hg : 0<g) :
    ∃ eps : ℝ,0<eps ∧ eps≤g/16 ∧ eps≤g^2/128 ∧
      ∃ m : ℕ,0<m ∧ 2*eps+Real.sqrt (4/(m : ℝ)+4*eps)<g := by
  let eps := min (g/16) (g^2/128)
  have heps : 0<eps := lt_min (by positivity) (by positivity)
  have hepsG : eps≤g/16 := min_le_left _ _
  have hepsSq : eps≤g^2/128 := min_le_right _ _
  obtain ⟨m,hm⟩ := exists_nat_gt (128/g^2)
  have hmR : (0 : ℝ)<m := (div_pos (by norm_num) (sq_pos_of_pos hg)).trans hm
  have hmN : 0<m := Nat.cast_pos.mp hmR
  have hmProd : (128 : ℝ)<(m : ℝ)*g^2 := (div_lt_iff₀ (sq_pos_of_pos hg)).mp hm
  have hInv : 4/(m : ℝ)<g^2/32 := by
    apply (div_lt_iff₀ hmR).mpr
    nlinarith only [hmProd]
  have hRoot : Real.sqrt (4/(m : ℝ)+4*eps)<g/4 := by
    apply (Real.sqrt_lt' (by positivity : 0<g/4)).mpr
    nlinarith only [hInv,hepsSq]
  refine ⟨eps,heps,hepsG,hepsSq,m,hmN,?_⟩
  linarith only [hRoot,hepsG,hg]

end
end TensorPCA.NonRSLowerProofs.FiniteGGCloningGeometry
