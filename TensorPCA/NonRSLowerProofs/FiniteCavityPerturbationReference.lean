-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationCovariance
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGeometry
public import TensorPCA.NonRSLowerProofs.FiniteCavityNormalizedGramBounds
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedPrior

/-! The enlarged perturbation field compared with the unchanged bulk-N perturbation at
the same cutoff and amplitude cube.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationReference
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteCavityPerturbationCovariance FiniteCavityReferenceGeometry FiniteCavityReferenceLaw
open FiniteCavityNormalizedGramBounds FiniteCavityRetainedPrior
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem perturbationFeature_unit_norm_le {N K : ℕ} (v : ℝ) (a : Fin K→ℝ)
    (ha : ∀p,|a p|≤2) {x : Model.Vector N} (hx : ‖x‖=1) :
    ‖feature (coefficients v a) x‖≤2*|v| := by
  apply feature_norm_le _ (by positivity) _ x hx
  have H := coefficients_budget v a ha
  simpa only [mul_pow,sq_abs] using H

theorem reference_perturbation_gram_error {N M K : ℕ} (hN : 0<N)
    (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) (v w : ℝ) {L e r r' : ℝ}
    (hL : 0≤L) (he0 : 0≤e) (he1 : e≤1/2)
    {x y : Model.Vector N} (hx : ‖x‖=1) (hy : ‖y‖=1) (hr : 0≤r) (hr' : 0≤r')
    (eta eta' : Model.Vector M) (heta : ‖eta‖^2≤L) (heta' : ‖eta'‖^2≤L)
    (hbox : r^2/(N : ℝ)∈Icc (1-e) (1+e)) (hbox' : r'^2/(N : ℝ)∈Icc (1-e) (1+e)) :
    |inner ℝ (feature (coefficients v a) (cavityReferenceMap N M (x,(r,eta))))
        (feature (coefficients v a) (cavityReferenceMap N M (y,(r',eta'))))-
      inner ℝ (feature (coefficients w a) x) (feature (coefficients w a) y)|≤
      4*|v^2-w^2|+16*(K : ℝ)*L*v^2/(N : ℝ) := by
  have hR : |inner ℝ x y|≤1 := (abs_real_inner_le_norm x y).trans_eq (by rw [hx,hy,mul_one])
  have hc : (inner ℝ eta eta')^2≤‖eta‖^2*‖eta'‖^2 := by
    simpa only [sq_abs,mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm eta eta') 2
  have H := normalizedGram_shell_bounds (Nat.cast_pos.mpr hN) hL he0 he1 hr hr'
    ⟨sq_nonneg _,heta⟩ ⟨sq_nonneg _,heta'⟩ hbox hbox' hR hc
  rw [feature_inner_eq_amplitudeKernel,feature_inner_eq_amplitudeKernel,reference_inner hx hy]
  have HC := amplitude_covariance_error a ha v w H.2.1 hR
  calc
    _ ≤ 4*|v^2-w^2|+4*(K : ℝ)*v^2*
        |(r*r'*inner ℝ x y+inner ℝ eta eta')/Real.sqrt ((r^2+‖eta‖^2)*(r'^2+‖eta'‖^2))-inner ℝ x y| := HC
    _ ≤ 4*|v^2-w^2|+4*(K : ℝ)*v^2*(4*L/(N : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left H.2.2.1 (by positivity : 0≤4*(K : ℝ)*v^2))
    _ = _ := by ring

theorem retained_perturbation_covariance_bounds {N M K : ℕ} (hN : 0<N)
    (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) (v w : ℝ) {delta e : ℝ}
    (hdelta : 0≤delta) (he0 : 0≤e) (he1 : e≤1/2) :
    let E := 4*|v^2-w^2|+16*(K : ℝ)*((M : ℝ)*(1+delta))*v^2/(N : ℝ)
    (∀ᵐ z∂retainedPrior N M e delta,
      |inner ℝ (feature (coefficients v a) (cavityReferenceMap N M z))
          (feature (coefficients v a) (cavityReferenceMap N M z))-
        inner ℝ (feature (coefficients w a) z.1) (feature (coefficients w a) z.1)|≤E) ∧
    (∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
      |inner ℝ (feature (coefficients v a) (cavityReferenceMap N M p.1))
          (feature (coefficients v a) (cavityReferenceMap N M p.2))-
        inner ℝ (feature (coefficients w a) p.1.1) (feature (coefficients w a) p.2.1)|≤E) := by
  dsimp only
  have hs := retainedPrior_support_ae (M := M) hN e delta
  have H (z z' : Model.Vector N×(ℝ×Model.Vector M))
      (hz : ‖z.1‖=1 ∧ 0<z.2.1 ∧ z.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
        z.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta)
      (hz' : ‖z'.1‖=1 ∧ 0<z'.2.1 ∧ z'.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
        z'.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta) :=
    reference_perturbation_gram_error hN a ha v w (by positivity) he0 he1 hz.1 hz'.1
      hz.2.1.le hz'.2.1.le z.2.2 z'.2.2 hz.2.2.2.2 hz'.2.2.2.2 hz.2.2.1 hz'.2.2.1
  refine ⟨hs.mono (fun z hz => H z z hz hz),?_⟩
  have hS1 : ∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
      ‖p.1.1‖=1 ∧ 0<p.1.2.1 ∧ p.1.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
        p.1.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta :=
    Measure.quasiMeasurePreserving_fst.ae hs
  have hS2 : ∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
      ‖p.2.1‖=1 ∧ 0<p.2.2.1 ∧ p.2.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
        p.2.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta :=
    Measure.quasiMeasurePreserving_snd.ae hs
  filter_upwards [hS1,hS2] with p hp hp'
  exact H p.1 p.2 hp hp'

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationReference
