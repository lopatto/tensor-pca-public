-- SPDX-License-Identifier: Apache-2.0
/- Attributed finite first-moment source port from
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalCountIntensity.lean
with the two finite prefactor lemmas from SphericalSignedWindowHelpers.lean
at the same immutable revision. Mathematical bodies are retained; narrow
already-proved finite imports replace unrelated signed-GOE asymptotics.
Apache-2.0; see LICENSE. -/
module

public import TensorPCA.RetainedCountProofs.SphericalSignedCounts
public import TensorPCA.RetainedCountProofs.UnrestrictedConditionedDeterminants
public import TensorPCA.RetainedCountProofs.ConditionedDeterminantMoments

/-! Exact physical intensities of the one-point critical counts. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalSequentialRegression GOEPhysicalPotential ConditionedDeterminantMoments
open UnrestrictedConditionedDeterminants SphericalIntrinsicKacRice WholeFieldRegression
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma sphereKRPrefactor_ne_zero (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    sphereKRPrefactor n μ Q ≠ 0 := by
  rw [sphereKRPrefactor_physical n μ hQ]
  apply mul_ne_zero (manuscriptRoundVolume_mass_ne_zero n)
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (mul_pos hQ (mixture_xi1_pos μ hQ))) _

lemma sphereKRPrefactor_ne_top (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    sphereKRPrefactor n μ Q ≠ ⊤ := by
  exact ENNReal.mul_ne_top (manuscriptRoundVolume_mass_ne_top n) ENNReal.ofReal_ne_top

lemma mixed_posterior_det_mean (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+2)) (hx : ‖x‖ ^ 2 = (n+2 : ℕ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det|
      ∂mixedConditionedLaw (n := n+1) c x hx b) =
      ENNReal.ofReal (physicalMean n (n+2) (Q^2 * μ.xi2 Q) (b 1)) := by
  have he := ofReal_integral_eq_lintegral_ofReal
    (mixed_intrinsicDet_integrable (n := n+1) μ hQ hnp x hx b)
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
  exact he.symm.trans (congrArg ENNReal.ofReal
    (determinant_mean_eq_of_law (mixed_intrinsicDet_hasLaw μ hQ hnp x hx b)))

lemma pure_posterior_det_mean (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+2)) (hx : ‖x‖ ^ 2 = (n+2 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det|
      ∂valueConditionedLaw (n := n+1) c x hx h) =
      ENNReal.ofReal (physicalMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h)) := by
  have he := ofReal_integral_eq_lintegral_ofReal
    (pure_intrinsicDet_integrable (n := n+1) p hp alpha halpha hQ x hx h)
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
  exact he.symm.trans (congrArg ENNReal.ofReal
    (determinant_mean_eq_of_law (pure_intrinsicDet_hasLaw p hp alpha halpha hQ x hx h)))

/-- The genuine mixed critical-point intensity in normalized score coordinates.
Here the sphere has ambient dimension `n+2`, and its Hessian dimension is `n+1`. -/
def mixedCriticalIntensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (b : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  sphereKRPrefactor (n+1) μ Q * physicalScorePdf (n+2) μ Q b *
    ENNReal.ofReal (physicalMean n (n+2) (Q^2 * μ.xi2 Q) (b 1))

/-- The proper pure critical-point intensity has a scalar value density. -/
def pureCriticalIntensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q h : ℝ) : ℝ≥0∞ :=
  let μ := FiniteMixture.pure p hp alpha halpha
  sphereKRPrefactor (n+1) μ Q * physicalValuePdf (n+2) μ Q h *
    ENNReal.ofReal (physicalMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h))

/-- Exact expected number of true mixed critical points in every Borel score
window, with the actual ordinary GOE determinant mean and no spatial dependence. -/
theorem actual_mixed_count_intensity (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) = ∫⁻ b in K, mixedCriticalIntensity n μ Q b := by
  dsimp only
  rw [(actual_mixed_score_window_kacRice (n+1) (by omega) μ hQ hnp K hK
    (fun _ _ => 1) measurable_const).2]
  have he : mixedWindowIntensity (n+1) μ Q K (fun _ _ => 1) =ᵐ[sphereLaw (n+2)]
      (fun _ => ∫⁻ b in K, physicalScorePdf (n+2) μ Q b *
        ENNReal.ofReal (physicalMean n (n+2) (Q^2 * μ.xi2 Q) (b 1))) := by
    filter_upwards [sphereLaw_support (show 1 ≤ n+2 by omega)] with x hx
    rw [mixedWindowIntensity, dite_eq_left hx]
    apply lintegral_congr
    intro b
    simp only [mul_one, mixed_posterior_det_mean n μ hQ hnp x hx b]
  rw [lintegral_congr_ae he, lintegral_const]
  simp only [measure_univ, mul_one]
  rw [← lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) μ Q)]
  apply lintegral_congr
  intro b
  exact (mul_assoc _ _ _).symm

theorem actual_mixed_count_intensity_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    (∫⁻ b in K, mixedCriticalIntensity n μ Q b) < ⊤ := by
  rw [← actual_mixed_count_intensity n μ hQ hnp K hK]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ K
    (fun _ _ => 1) 1 (by simp) (fun _ _ => le_rfl)

/-- Exact expected pure critical count, retaining the literal scalar window
`{h | (h,p*h)∈K}` and no redundant two-dimensional density. -/
theorem actual_pure_count_intensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ h in pureScoreWindow p K, pureCriticalIntensity n p hp alpha halpha Q h := by
  let μ := FiniteMixture.pure p hp alpha halpha
  dsimp only
  rw [(actual_pure_score_window_kacRice (n+1) (by omega) p hp alpha halpha hQ K hK
    (fun _ _ => 1) measurable_const).2]
  have he : valueWindowIntensity (n+1) μ Q (pureScoreWindow p K) (fun _ _ => 1)
      =ᵐ[sphereLaw (n+2)] (fun _ => ∫⁻ h in pureScoreWindow p K,
        physicalValuePdf (n+2) μ Q h *
        ENNReal.ofReal (physicalMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h))) := by
    filter_upwards [sphereLaw_support (show 1 ≤ n+2 by omega)] with x hx
    rw [valueWindowIntensity, dite_eq_left hx]
    apply lintegral_congr
    intro b
    simp only [mul_one]
    congr 1
    exact pure_posterior_det_mean n p hp alpha halpha hQ x hx b
  rw [lintegral_congr_ae he, lintegral_const]
  simp only [measure_univ, mul_one]
  rw [← lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) μ Q)]
  apply lintegral_congr
  intro b
  exact (mul_assoc _ _ _).symm

theorem actual_pure_count_intensity_finite (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    (∫⁻ h in pureScoreWindow p K, pureCriticalIntensity n p hp alpha halpha Q h) < ⊤ := by
  rw [← actual_pure_count_intensity n p hp alpha halpha hQ K hK]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega)
    (FiniteMixture.pure p hp alpha halpha) hQ K
    (fun _ _ => 1) 1 (by simp) (fun _ _ => le_rfl)

end
end TensorPCA.RetainedCountProofs.SphericalMarkedWindows

