-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Expected spectral statistics under the sole actual GOE law. The proof
   couples its genuine Householder tridiagonalization to the literal Jacobi
   matrix and uses the proved deterministic semicircle limit. No empirical
   measure convergence or spectral-asymptotic premise is assumed. -/
module
public import TensorPCA.RetainedCountProofs.GaussianJacobiMeanCoupling
public import TensorPCA.RetainedCountProofs.JacobiSemicircle
public import TensorPCA.RetainedCountProofs.GOEClippedDeterminants
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology RealInnerProductSpace NNReal
namespace TensorPCA.RetainedCountProofs.GOEExpectedTraceProofs
open OAI.CriticalSK GOEAsymptotics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def testTrace (m : ℕ) (f : ℝ → ℝ) (A : GOEAsymptotics.GaussianMatrix m) : ℝ :=
  ∑ i : Fin m, f (matrixOrderedEigenvalues A i)

lemma testTrace_lipschitz (m : ℕ) (f : ℝ → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith ⟨Real.sqrt (m:ℝ)*(L:ℝ), by positivity⟩ (testTrace m f) :=
  GOEClippedDeterminants.spectralTrace_lipschitz m f hf

lemma testTrace_triReduce {m : ℕ} (f : ℝ → ℝ) (A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j, A i j = A j i) : testTrace m f (triReduce m A) = testTrace m f A := by
  unfold testTrace
  rw [matrixOrderedEigenvalues_triReduce A hA]

lemma testTrace_jacobi (n : ℕ) (f : ℝ → ℝ) :
    testTrace (n+1) f (jacobiGaussian (n+1:ℝ)⁻¹ (n+1)) =
      ∑ i : Fin (n+1), f ((JacobiMatrix.jacobi_hermitian (n+1:ℝ)⁻¹ (n+1)).eigenvalues i) := by
  let hA := JacobiMatrix.jacobi_hermitian (n+1:ℝ)⁻¹ (n+1)
  have hsym : ∀ i j, jacobiGaussian (n+1:ℝ)⁻¹ (n+1) i j =
      jacobiGaussian (n+1:ℝ)⁻¹ (n+1) j i := by
    intro i j
    exact congrFun (congrFun (JacobiMatrix.jacobi_symmetric (n+1:ℝ)⁻¹ (n+1)) j) i
  unfold testTrace
  rw [matrixOrderedEigenvalues_eq _ hsym]
  let hS := gaussianMatrixCLM_symmetric (jacobiGaussian (n+1:ℝ)⁻¹ (n+1)) hsym
  have hchar : (gaussianMatrixCLM (jacobiGaussian (n+1:ℝ)⁻¹ (n+1))).toLinearMap.charpoly =
      (JacobiMatrix.jacobi (n+1:ℝ)⁻¹ (n+1)).charpoly :=
    Matrix.charpoly_toLin (JacobiMatrix.jacobi (n+1:ℝ)⁻¹ (n+1))
      (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis
  have hsroots := hS.roots_charpoly_eq_eigenvalues
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1)
  rw [hchar] at hsroots
  have he := congrArg (fun M : Multiset ℝ => (M.map f).sum)
    (hsroots.symm.trans hA.roots_charpoly_eq_eigenvalues)
  simpa only [Multiset.map_map, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
    Finset.sum_eq_multiset_sum] using he

/-- Actual GOE and deterministic Jacobi spectral statistics differ in mean
by the proved Frobenius coupling, for every scalar Lipschitz test. -/
theorem expected_testTrace_difference (n : ℕ) (f : ℝ → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    Integrable (testTrace (n+1) f)
      ((stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n))) ∧
    |(∫ A, testTrace (n+1) f A
      ∂((stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n)))) -
      testTrace (n+1) f (jacobiGaussian (n+1:ℝ)⁻¹ (n+1))| ≤
        Real.sqrt (((n+1:ℕ):ℝ))*(L:ℝ)*Real.sqrt 6 := by
  let μ := (stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
    (symmetrizeGaussianMatrix (goeScale n))
  let J := jacobiGaussian (n+1:ℝ)⁻¹ (n+1)
  let C : ℝ := Real.sqrt (((n+1:ℕ):ℝ))*(L:ℝ)
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) L.coe_nonneg
  have hLip := testTrace_lipschitz (n+1) f hf
  have hpoint (A : GOEAsymptotics.GaussianMatrix (n+1)) :
      |testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J| ≤
        C*‖triReduce (n+1) A-J‖ := by
    have hh := hLip.dist_le_mul (triReduce (n+1) A) J
    change ‖testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J‖ ≤
      C*‖triReduce (n+1) A-J‖ at hh
    simpa only [Real.norm_eq_abs] using hh
  have hm : Measurable (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
      testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J) :=
    (hLip.continuous.measurable.comp (triReduce_measurable (n+1))).sub measurable_const
  have hBoundI : Integrable (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
      C*‖triReduce (n+1) A-J‖) μ :=
    (jacobiError_norm_integrable n).const_mul C
  have hErrI : Integrable (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
      testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J) μ :=
    hBoundI.mono' hm.aestronglyMeasurable (ae_of_all _ fun A => by
      simpa only [Real.norm_eq_abs] using hpoint A)
  have hTI : Integrable (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
      testTrace (n+1) f (triReduce (n+1) A)) μ := by
    apply (hErrI.add (integrable_const (testTrace (n+1) f J))).congr
    exact ae_of_all _ fun A => sub_add_cancel
      (testTrace (n+1) f (triReduce (n+1) A)) (testTrace (n+1) f J)
  have heq : (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
      testTrace (n+1) f (triReduce (n+1) A)) =ᵐ[μ] testTrace (n+1) f := by
    filter_upwards [symmetrized_symmetric_ae (m := n+1) (goeScale n)] with A hA
    exact testTrace_triReduce f A hA
  have hI : Integrable (testTrace (n+1) f) μ := hTI.congr heq
  have hDiff : (∫ A : GOEAsymptotics.GaussianMatrix (n+1),
      testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J ∂μ) =
        (∫ A, testTrace (n+1) f A ∂μ)-testTrace (n+1) f J := by
    calc
      _ = (∫ A, testTrace (n+1) f (triReduce (n+1) A) ∂μ) -
          (∫ _A : GOEAsymptotics.GaussianMatrix (n+1), testTrace (n+1) f J ∂μ) :=
        integral_sub hTI (integrable_const (testTrace (n+1) f J))
      _ = _ := by rw [integral_congr_ae heq, integral_const]; simp
  refine ⟨hI, ?_⟩
  calc
    _ = ‖∫ A : GOEAsymptotics.GaussianMatrix (n+1),
        testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J ∂μ‖ := by
      rw [hDiff, Real.norm_eq_abs]
    _ ≤ ∫ A : GOEAsymptotics.GaussianMatrix (n+1),
        ‖testTrace (n+1) f (triReduce (n+1) A)-testTrace (n+1) f J‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ A : GOEAsymptotics.GaussianMatrix (n+1), C*‖triReduce (n+1) A-J‖ ∂μ :=
      integral_mono hErrI.norm hBoundI (fun A => by
        simpa only [Real.norm_eq_abs] using hpoint A)
    _ = C*(∫ A : GOEAsymptotics.GaussianMatrix (n+1), ‖triReduce (n+1) A-J‖ ∂μ) :=
      integral_const_mul C _
    _ ≤ C*Real.sqrt 6 := mul_le_mul_of_nonneg_left
      (integral_jacobiError_norm_le_sqrt_six n) hC

lemma normalized_expected_testTrace_difference (n : ℕ) (f : ℝ → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    |(∫ A, testTrace (n+1) f A
      ∂((stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n))))/(n+1:ℝ) -
      testTrace (n+1) f (jacobiGaussian (n+1:ℝ)⁻¹ (n+1))/(n+1:ℝ)| ≤
        ((L:ℝ)*Real.sqrt 6)/Real.sqrt (n+1:ℝ) := by
  have hN : (0:ℝ) < n+1 := by positivity
  have hroot : Real.sqrt (n+1:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hb := (expected_testTrace_difference n f hf).2
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rw [← sub_div, abs_div, abs_of_pos hN]
  calc
    _ ≤ (Real.sqrt (n+1:ℝ)*(L:ℝ)*Real.sqrt 6)/(n+1:ℝ) :=
      div_le_div_of_nonneg_right hb hN.le
    _ = _ := by
      apply (div_eq_div_iff hN.ne' hroot).mpr
      calc
        Real.sqrt (n+1:ℝ)*(L:ℝ)*Real.sqrt 6*Real.sqrt (n+1:ℝ) =
            ((L:ℝ)*Real.sqrt 6)*(Real.sqrt (n+1:ℝ))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hN.le]

theorem normalized_symmetrized_testTrace_tendsto (f : ℝ → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    Tendsto (fun n => (∫ A, testTrace (n+1) f A
      ∂((stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n))))/(n+1:ℝ)) atTop
      (𝓝 (∫ t, f t ∂SemicirclePotential.law)) := by
  have hN : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hbound : Tendsto (fun n : ℕ => ((L:ℝ)*Real.sqrt 6)/Real.sqrt (n+1:ℝ))
      atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hN).const_div_atTop _
  have hd : Tendsto (fun n =>
      (∫ A, testTrace (n+1) f A
        ∂((stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
          (symmetrizeGaussianMatrix (goeScale n))))/(n+1:ℝ) -
        testTrace (n+1) f (jacobiGaussian (n+1:ℝ)⁻¹ (n+1))/(n+1:ℝ))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hbound.eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq, sub_zero]
    exact (normalized_expected_testTrace_difference n f hf).trans_lt hn
  have hj : Tendsto (fun n => testTrace (n+1) f (jacobiGaussian (n+1:ℝ)⁻¹ (n+1))/(n+1:ℝ))
      atTop (𝓝 (∫ t, f t ∂SemicirclePotential.law)) := by
    simpa only [testTrace_jacobi, Nat.cast_add, Nat.cast_one] using
      JacobiSemicircle.continuous_test_tendsto_real f hf.continuous
  have hh := hd.add hj
  simp only [zero_add] at hh
  exact hh.congr' (Eventually.of_forall fun n => sub_add_cancel _ _)

lemma normalized_goe_matrix_hasLaw (n : ℕ) :
    HasLaw (matrixToGaussian (k := n+1))
      ((stdGaussian (OAI.CriticalSK.GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n)))
      (SphericalGaussianJet.goeLaw (n+1) (n+1) 1) := by
  refine ⟨(matrixToGaussian_measurable (n+1)).aemeasurable, ?_⟩
  apply goeLaw_bridge
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using goeScale_square n

lemma raw_testTrace_integrable (n : ℕ) (f : ℝ → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    Integrable (fun W => testTrace (n+1) f (matrixToGaussian W))
      (SphericalGaussianJet.goeLaw (n+1) (n+1) 1) :=
  (normalized_goe_matrix_hasLaw n).integrable_fun_comp
    (expected_testTrace_difference n f hf).1

/-- The expected normalized statistic of the genuine independent-upper-entry
GOE converges to its actual semicircle-density integral. -/
theorem normalized_goe_testTrace_tendsto (f : ℝ → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    Tendsto (fun n => (∫ W, testTrace (n+1) f (matrixToGaussian W)
      ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)/(n+1:ℝ)) atTop
      (𝓝 (∫ t, f t ∂SemicirclePotential.law)) := by
  apply (normalized_symmetrized_testTrace_tendsto f hf).congr'
  apply Eventually.of_forall
  intro n
  apply congrArg (fun r : ℝ => r/(n+1:ℝ))
  exact ((normalized_goe_matrix_hasLaw n).integral_comp
    (testTrace_lipschitz (n+1) f hf).continuous.aestronglyMeasurable).symm

/-- Literal actual clipped-log trace convergence, with every real shift and
positive clipping radius; no empirical-law or mean-limit premise remains. -/
theorem normalized_expected_clippedTrace_tendsto (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (fun n => (∫ W,
      GOEClippedDeterminants.matrixClippedTrace (n+1) k rho W
      ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)/(n+1:ℝ)) atTop
      (𝓝 (∫ t, SpectralTraceLipschitz.clippedLog k rho t ∂SemicirclePotential.law)) := by
  simpa only [testTrace, GOEClippedDeterminants.matrixClippedTrace] using
    normalized_goe_testTrace_tendsto (SpectralTraceLipschitz.clippedLog k rho)
      (SpectralTraceLipschitz.clippedLog_lipschitz k hrho)

end TensorPCA.RetainedCountProofs.GOEExpectedTraceProofs
