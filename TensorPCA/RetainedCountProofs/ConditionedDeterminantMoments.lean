-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite actual-GOE source port from pmaronow/slowequilibration-palomar
   a28aaa336343c4caf43791ababd8ed0ee5c7b58e. Only the literal definitions and
   finite law/mean APIs named below are retained; no spectral/moment asymptotic
   bound is imported or assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GOEPhysicalPotential
public import TensorPCA.RetainedCountProofs.PureConditionedHessian
public import TensorPCA.RetainedCountProofs.SphericalSequentialRegression
@[expose] public section
namespace TensorPCA.RetainedCountProofs.ConditionedDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian WholeFieldRegression
open IntrinsicHessianLaw ConditionedIntrinsicHessian PureConditionedHessian
open SphericalSequentialRegression GOERawMoments GOEPhysicalPotential
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Literal absolute determinant of the actual intrinsic Hessian operator. -/
def intrinsicDet {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (x : Vector N)
    (J : Disorder N μ.maxDegree) : ℝ :=
  |(intrinsicHessian (field (centerCoefficients (mixtureCoefficients μ) Q) J) x).det|

/-- The actual canonical posterior at normalized nonpure value/radial marks. -/
def mixedLaw {n : ℕ} (μ : FiniteMixture) (Q : ℝ) (x : Vector (n + 2))
    (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    Measure (Disorder (n + 2) μ.maxDegree) :=
  coefficientKernel (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) x (tangentFrame x hx))
    (jointScoreTarget (n + 1) (((n + 2 : ℕ) : ℝ) • z))

/-- The actual proper pure posterior, with redundant radial score omitted. -/
def pureLaw {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (h : ℝ) :
    Measure (Disorder (n + 2) (FiniteMixture.pure p hp alpha halpha).maxDegree) :=
  coefficientKernel (ValueTangentConditioning.valueTangentCLM
    (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q)
      x (tangentFrame x hx)) (valueTarget (n + 1) h)

lemma intrinsicMatrix_abs_det {n : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (J : Disorder (n + 2) μ.maxDegree) :
    |(intrinsicMatrix (centerCoefficients (mixtureCoefficients μ) Q) x hx J).det| = intrinsicDet μ Q x J := by
  rw [intrinsicMatrix, LinearMap.det_toMatrix]
  rfl

lemma shifted_abs_det (n : ℕ) (k : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    |(W - k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).det| = matrixAbsoluteDet n k W := by
  have he : W - k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = -(k • 1 - W) := by abel
  rw [he, Matrix.det_neg, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  rfl

lemma shifted_absdet_law {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω} (n : ℕ)
    (H : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (D : Ω → ℝ)
    (b k : ℝ)
    (hH : HasLaw H ((goeLaw (n + 1) (n + 2) b).map
      (fun W => W - k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))) η)
    (hD : ∀ ω, |(H ω).det| = D ω) :
    HasLaw D ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) η := by
  have hf : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => |W.det|) :=
    continuous_id.matrix_det.abs.measurable
  have hs : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => W - k • 1) := by fun_prop
  have h := (hasLaw_map hf.aemeasurable).fun_comp hH
  rw [Measure.map_map hf hs] at h
  simpa only [Function.comp_def, shifted_abs_det, hD] using h

/-- The posterior determinant itself has the literal canonical ordinary GOE
absolute determinant law at every specified nonpure null mark. -/
theorem mixed_intrinsicDet_hasLaw {n : ℕ} (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    HasLaw (intrinsicDet μ Q x)
      ((goeLaw (n + 1) (n + 2) (Q ^ 2 * μ.xi2 Q)).map (matrixAbsoluteDet n (z 1)))
      (mixedLaw μ Q x hx z) := by
  have hk : jointScoreTarget (n + 1) (((n + 2 : ℕ) : ℝ) • z) (Sum.inl 1) / (n + 2 : ℕ) = z 1 := by
    change (((n + 2 : ℕ) : ℝ) * z 1) / (n + 2 : ℕ) = _
    field_simp
  have h := conditioned_intrinsicMatrix_hasLaw μ hQ hnp x hx
    (jointScoreTarget (n + 1) (((n + 2 : ℕ) : ℝ) • z))
  simp only [hk] at h
  exact shifted_absdet_law n _ _ _ _ h (intrinsicMatrix_abs_det μ Q x hx)

/-- Proper pure conditioning yields the literal determinant law at k=ph. -/
theorem pure_intrinsicDet_hasLaw {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    HasLaw (intrinsicDet μ Q x)
      ((goeLaw (n + 1) (n + 2) (Q ^ 2 * μ.xi2 Q)).map (matrixAbsoluteDet n ((p : ℝ) * h)))
      (pureLaw p hp alpha halpha Q x hx h) := by
  dsimp only
  have hH := pure_hessian_at_normalized_value p hp alpha halpha hQ x hx h
  exact shifted_absdet_law n _ _ _ _ hH
    (intrinsicMatrix_abs_det (FiniteMixture.pure p hp alpha halpha) Q x hx)

/-- Exact ordinary expectation equality follows from the actual law, without
an expected-log or conditional-version premise. -/
theorem determinant_mean_eq_of_law {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω}
    {n : ℕ} {b k : ℝ} {D : Ω → ℝ}
    (hD : HasLaw D ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) η) :
    (∫ ω, D ω ∂η) = physicalMean n (n + 2) b k := by
  rw [hD.integral_eq]
  simpa only [id_eq, physicalMean] using
    (integral_map (φ := matrixAbsoluteDet n k) (f := id)
      (matrixAbsoluteDet_measurable n k).aemeasurable (aestronglyMeasurable_id (μ := (goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k))))

end
end TensorPCA.RetainedCountProofs.ConditionedDeterminantMoments
