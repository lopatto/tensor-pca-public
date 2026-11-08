-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorTowerClipping
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSphericalStages

/-! The finite-dimensional sphericalStage numerator admits one upper cutoff, chosen
uniformly over depth, masses and variance allocation. This is the numerator clipping
estimate; hierarchy-moment identification is treated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClippingUniform
open MeasureTheory ProbabilityTheory
open FiniteGaussianSphericalNumeratorTowerClipping
open FiniteGaussianQuadraticSphericalStages FiniteGaussianQuadraticLogSteps FiniteGaussianQuadraticStep
open FiniteGaussianLogStepsCompression OneStepGaussianTiltEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M : ℕ}

theorem sphericalStage_clipping_bound (hM : 0<M) {d : ℕ} (x Delta : Fin d→ℝ)
    (hx : ∀j,0<x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hDelta : ∀j,0≤Delta j)
    {v0 L : ℝ} (hv0 : 0≤v0) (hL : 1≤L) :
    let raw := fun g : Model.Vector M => sphericalStage M x Delta 0 (Real.sqrt v0 •g)
    let clipped := fun g : Model.Vector M => gaussianLogSteps (quadraticSteps M x Delta)
      (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)) (Real.sqrt v0 •g)
    Integrable raw (stdGaussian (Model.Vector M)) ∧
    Integrable clipped (stdGaussian (Model.Vector M)) ∧
    0≤(∫g,raw g ∂stdGaussian (Model.Vector M))-(∫g,clipped g ∂stdGaussian (Model.Vector M)) ∧
    (∫g,raw g ∂stdGaussian (Model.Vector M))-(∫g,clipped g ∂stdGaussian (Model.Vector M))≤
      Real.exp (2*(M : ℝ)*(v0+∑j,Delta j))/L := by
  let layers := List.ofFn (fun j : Fin d => (x j,Delta j))
  have hm : ∀s∈layers,0<s.1 ∧ s.1≤1 := by
    intro s hs
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
    exact ⟨hx j,hx1 j⟩
  have hv : ∀s∈layers,0≤s.2 := by
    intro s hs
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
    exact hDelta j
  have ho : layers.Pairwise (fun s t => s.1≤t.1) :=
    List.pairwise_ofFn.mpr (fun _ _ hij => hxm hij.le)
  have H := averaged_spherical_root_clipping_bound hM layers hm hv ho hv0 hL
  simpa only [layers,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    sphericalStage,List.drop_zero,quadraticSteps,shift] using H

theorem exists_uniform_sphericalStage_cutoff (hM : 0<M) (Y : ℝ) {eta : ℝ} (heta : 0<eta) :
    ∃L : ℝ,1≤L ∧ ∀(d : ℕ) (x Delta : Fin d→ℝ) (v0 : ℝ),
      (∀j,0<x j) → (∀j,x j≤1) → Monotone x → (∀j,0≤Delta j) → 0≤v0 →
      v0+∑j,Delta j≤Y →
      let raw := fun g : Model.Vector M => sphericalStage M x Delta 0 (Real.sqrt v0 •g)
      let clipped := fun g : Model.Vector M => gaussianLogSteps (quadraticSteps M x Delta)
        (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)) (Real.sqrt v0 •g)
      Integrable raw (stdGaussian (Model.Vector M)) ∧
      Integrable clipped (stdGaussian (Model.Vector M)) ∧
      0≤(∫g,raw g ∂stdGaussian (Model.Vector M))-(∫g,clipped g ∂stdGaussian (Model.Vector M)) ∧
      (∫g,raw g ∂stdGaussian (Model.Vector M))-(∫g,clipped g ∂stdGaussian (Model.Vector M))≤eta := by
  let C := Real.exp (2*(M : ℝ)*Y)
  let L := 1+C/eta
  have hC : 0<C := Real.exp_pos _
  have hL : 1≤L := le_add_of_nonneg_right (div_nonneg hC.le heta.le)
  refine ⟨L,hL,?_⟩
  intro d x Delta v0 hx hx1 hxm hDelta hv0 hTotal
  have H := sphericalStage_clipping_bound hM x Delta hx hx1 hxm hDelta hv0 hL
  have hExp : Real.exp (2*(M : ℝ)*(v0+∑j,Delta j))≤C :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hTotal (mul_nonneg (by norm_num) (Nat.cast_nonneg M)))
  have hSmall : C/L≤eta := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hL)).mpr
    dsimp [L]
    field_simp
    nlinarith
  exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.trans ((div_le_div_of_nonneg_right hExp (zero_lt_one.trans_le hL).le).trans hSmall)⟩

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClippingUniform
