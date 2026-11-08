-- SPDX-License-Identifier: Apache-2.0
/- Adapted finite edge comparison from immutable source
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
GaussianDominatedEdge.lean. The already checked canonical Gaussian comparison
and finite Rayleigh bridge replace unrelated GOE spectral imports. No
spectral/asymptotic conclusion is supplied as an assumption. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixSpectralTools
public import TensorPCA.GaussianMaximumComparisonProofs
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GaussianDominatedEdge
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianMatrixFeatures
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev UnitSphere (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
instance unitSphere_nonempty (n : ℕ) : Nonempty (UnitSphere n) := by
  refine ⟨⟨EuclideanSpace.basisFun (Fin (n+1)) ℝ 0,?_⟩⟩
  simpa only [Metric.mem_sphere,dist_zero_right] using (EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0
instance unitSphere_compact (n : ℕ) : CompactSpace (UnitSphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
lemma unitSphere_norm {n : ℕ} (u : UnitSphere n) : ‖(u : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using u.property

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
def upperEigenvalue (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (g : EuclideanSpace ℝ ι) : ℝ := matrixOrderedEigenvalues (W g) 0

lemma upperEigenvalue_lipschitz (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) :
    LipschitzWith ‖W‖₊ (upperEigenvalue W) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  change |matrixOrderedEigenvalues (W g) 0-matrixOrderedEigenvalues (W h) 0| ≤ ‖W‖*‖g-h‖
  have H := (matrixTopEigenvalue_lipschitz n).dist_le_mul (W g) (W h)
  change |matrixOrderedEigenvalues (W g) 0-matrixOrderedEigenvalues (W h) 0| ≤ (1 : ℝ)*‖W g-W h‖ at H
  calc
    _ ≤ ‖W g-W h‖ := by simpa only [one_mul] using H
    _ ≤ _ := by rw [← W.map_sub]; exact W.le_opNorm (g-h)

lemma sphereFeature_continuous (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) :
    Continuous (fun u : UnitSphere n ↦ quadraticFeature W u.val) :=
  W.adjoint.continuous.comp (rankOneMatrix_continuous.comp continuous_subtype_val)

lemma sphereFeature_bound (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) (u : UnitSphere n) :
    ‖innerSL ℝ (quadraticFeature W u.val)‖ ≤ ‖W‖ := by
  rw [innerSL_apply_norm]
  change ‖W.adjoint (rankOneMatrix u.val)‖ ≤ ‖W‖
  simpa only [rankOneMatrix_norm,unitSphere_norm,one_pow,mul_one,ContinuousLinearMap.adjoint.norm_map]
    using W.adjoint.le_opNorm (rankOneMatrix u.val)

/-- The actual top eigenvalue is the compact quadratic Gaussian field maximum.
The canonical symmetric-part convention also makes this true on all matrices. -/
lemma upperEigenvalue_eq_supremum (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (g : EuclideanSpace ℝ ι) :
    upperEigenvalue W g = ⨆ u : UnitSphere n, inner ℝ (quadraticFeature W u.val) g := by
  apply le_antisymm
  · obtain ⟨v,hv,hval⟩ := exists_unit_quadratic_eq_top (W g)
    let u : UnitSphere n := ⟨v,by simpa only [Metric.mem_sphere,dist_zero_right] using hv⟩
    have he : inner ℝ (quadraticFeature W u.val) g = upperEigenvalue W g := by
      rw [quadraticFeature_apply]
      exact hval
    rw [← he]
    exact GaussianCompactMaximum.le_field_supremum
      (fun u : UnitSphere n ↦ innerSL ℝ (quadraticFeature W u.val)) (sphereFeature_bound W) g u
  · apply ciSup_le
    intro u
    rw [quadraticFeature_apply]
    exact quadratic_le_topEigenvalue (W g) u.val (unitSphere_norm u)

lemma upperEigenvalue_integrable (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) :
    Integrable (upperEigenvalue W) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have he : upperEigenvalue W = fun g ↦ ⨆ u : UnitSphere n, inner ℝ (quadraticFeature W u.val) g :=
    funext (upperEigenvalue_eq_supremum W)
  rw [he]
  exact GaussianMaximumComparisonProofs.supremum_integrable _ (sphereFeature_continuous W)

/-- Actual finite-dimensional expected edge from compact Gaussian comparison.
The matrix covariance scale enters only through the proved linear-map norm. -/
theorem mean_upperEigenvalue_le (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hW : ‖W‖ ≤ sigma) :
    (∫ g, upperEigenvalue W g ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      (Real.sqrt 2*sigma)*Real.sqrt (n+1 : ℕ) := by
  have H := GaussianMaximumComparisonProofs.expected_supremum_le_linear_bound
    (fun u : UnitSphere n ↦ quadraticFeature W u.val)
    (fun u : UnitSphere n ↦ u.val) (sphereFeature_continuous W) continuous_subtype_val
    (mul_nonneg (Real.sqrt_nonneg 2) hsigma) unitSphere_norm
    (fun u v ↦ quadraticFeature_unit_increment W hsigma hW u.val v.val (unitSphere_norm u) (unitSphere_norm v))
  have he : upperEigenvalue W = fun g ↦ ⨆ u : UnitSphere n, inner ℝ (quadraticFeature W u.val) g :=
    funext (upperEigenvalue_eq_supremum W)
  rw [he]
  simpa only [Fintype.card_fin] using H

theorem upperEigenvalue_centered_subGaussian
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {sigma : ℝ} (hsigma : 0 < sigma) (hW : ‖W‖ ≤ sigma) :
    HasSubgaussianMGF (fun g ↦ upperEigenvalue W g-
      ∫ h, upperEigenvalue W h ∂stdGaussian (EuclideanSpace ℝ ι))
      (sigma^2).toNNReal (stdGaussian (EuclideanSpace ℝ ι)) := by
  have H := SYK.product_standardGaussian_hasSubgaussianMGF (upperEigenvalue W) sigma hsigma
    ((upperEigenvalue_lipschitz W).weaken (by
      change ‖W‖ ≤ (sigma.toNNReal : ℝ)
      rw [Real.coe_toNNReal _ hsigma.le]
      exact hW))
  simpa only [TensorPCA.GaussianConcentrationBridge.standardGaussianMeasure_bridge] using H

theorem upperEigenvalue_tail (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {sigma : ℝ} (hsigma : 0 < sigma) (hW : ‖W‖ ≤ sigma) {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      {g | (Real.sqrt 2*sigma)*Real.sqrt (n+1 : ℕ)+t ≤ upperEigenvalue W g} ≤
      Real.exp (-t^2/(2*sigma^2)) := by
  have hmean := mean_upperEigenvalue_le W hsigma.le hW
  have htail := (upperEigenvalue_centered_subGaussian W hsigma hW).measure_ge_le ht
  rw [Real.coe_toNNReal _ (sq_nonneg sigma)] at htail
  refine (measureReal_mono (fun g hg ↦ ?_)).trans htail
  change t ≤ upperEigenvalue W g-_
  change (Real.sqrt 2*sigma)*Real.sqrt (n+1 : ℕ)+t ≤ upperEigenvalue W g at hg
  linarith

lemma covariance_edge_scale_le {N : ℕ} (hN : n+1 ≤ N) {b : ℝ} (hb : 0 ≤ b) :
    (Real.sqrt 2*Real.sqrt (2*b/N))*Real.sqrt (n+1 : ℕ) ≤ 2*Real.sqrt b := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnN : ((n+1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have hbn : (0 : ℝ) ≤ 2*b/N := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt hbn,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n+1 : ℕ)),mul_pow,Real.sq_sqrt hb]
  have H := (div_le_iff₀ hNp).mpr
    (mul_le_mul_of_nonneg_left hnN (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb))
  convert H using 1 <;> ring

theorem mean_upperEigenvalue_le_covarianceScale
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {N : ℕ} (hN : n+1 ≤ N) {b : ℝ} (hb : 0 ≤ b) (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) :
    (∫ g, upperEigenvalue W g ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ 2*Real.sqrt b :=
  (mean_upperEigenvalue_le W (Real.sqrt_nonneg _) hW).trans (covariance_edge_scale_le hN hb)

theorem upperEigenvalue_tail_covarianceScale
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {N : ℕ} (hN : n+1 ≤ N) {b : ℝ} (hb : 0 < b)
    (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      {g | 2*Real.sqrt b+t ≤ upperEigenvalue W g} ≤ Real.exp (-(N : ℝ)*t^2/(4*b)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsigma : 0 < Real.sqrt (2*b/N) := Real.sqrt_pos.mpr (by positivity)
  have htail := upperEigenvalue_tail W hsigma hW ht
  have hscale := covariance_edge_scale_le hN hb.le
  have he : -t^2/(2*(Real.sqrt (2*b/N))^2) = -(N : ℝ)*t^2/(4*b) := by
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*b/N)]
    field_simp [ne_of_gt hb,ne_of_gt hNp] <;> ring
  rw [he] at htail
  refine (measureReal_mono (fun g hg ↦ ?_)).trans htail
  change (Real.sqrt 2*Real.sqrt (2*b/N))*Real.sqrt (n+1 : ℕ)+t ≤ upperEigenvalue W g
  change 2*Real.sqrt b+t ≤ upperEigenvalue W g at hg
  linarith

end
end TensorPCA.RetainedCountProofs.GaussianDominatedEdge
