-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Actual Gaussian Householder-to-Jacobi mean coupling. The denominator of
   the Gaussian scale remains fixed throughout the dimension recursion.
   The diagonal, column and reduced-tail laws are derived from the proved
   actual Gaussian block law; no empirical-limit assumption is supplied. -/
module
public import TensorPCA.RetainedCountProofs.GaussianJacobiCoupling
public import TensorPCA.RetainedCountProofs.GaussianColumnNormLaw
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma symmetrized_diagonal_preserving (m : ℕ) (s : ℝ) :
    MeasurePreserving (fun A : GaussianMatrix (Fin (m+1)) => A 0 0)
      ((stdGaussian (GaussianMatrix (Fin (m+1)))).map (symmetrizeGaussianMatrix s))
      (gaussianReal 0 (4*s^2).toNNReal) := by
  refine ⟨by fun_prop, ?_⟩
  simpa only [ite_true] using symmetrized_entry_law s (0 : Fin (m+1)) 0

lemma symmetrized_reducedTail_preserving (m : ℕ) (s : ℝ) :
    MeasurePreserving (reducedTail (n := m))
      ((stdGaussian (GaussianMatrix (Fin (m+1)))).map (symmetrizeGaussianMatrix s))
      ((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s)) := by
  have h := exposed_column_tail_law m s (firstAxis m)
  exact measurePreserving_snd.comp (measurePreserving_snd.comp h)

lemma symmetrized_columnNorm_preserving (m : ℕ) (s : ℝ) :
    MeasurePreserving (fun A : GaussianMatrix (Fin (m+1)) => ‖firstColumn A‖)
      ((stdGaussian (GaussianMatrix (Fin (m+1)))).map (symmetrizeGaussianMatrix s))
      (columnNormLaw m s) := by
  have h := exposed_column_tail_law m s (firstAxis m)
  have hc : MeasurePreserving (fun A : GaussianMatrix (Fin (m+1)) => fun i : Fin m => A 0 i.succ)
      ((stdGaussian (GaussianMatrix (Fin (m+1)))).map (symmetrizeGaussianMatrix s))
      (Measure.pi fun _ : Fin m => gaussianReal 0 (2*s^2).toNNReal) :=
    measurePreserving_fst.comp (measurePreserving_snd.comp h)
  exact (columnNorm_preserving m s).comp hc

lemma jacobiSquaredError_zero (a : ℝ) (A : GaussianMatrix (Fin 0)) :
    jacobiSquaredError a 0 A = 0 := by
  unfold jacobiSquaredError
  rw [show triReduce 0 A = jacobiGaussian a 0 from Subsingleton.elim _ _,
    sub_self, norm_zero, zero_pow two_ne_zero]

/-- The physical denominator n+1 is fixed while the tail dimension m varies. -/
theorem jacobiSquaredError_integrable_and_integral_le (n m : ℕ) :
    Integrable (jacobiSquaredError (n+1 : ℝ)⁻¹ m)
      ((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix (goeScale n))) ∧
    (∫ A, jacobiSquaredError (n+1 : ℝ)⁻¹ m A
      ∂((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix (goeScale n)))) ≤
      6*(m:ℝ)/(n+1 : ℝ) := by
  induction m with
  | zero =>
    have hz : jacobiSquaredError (n+1:ℝ)⁻¹ 0 =
        (fun _ : GaussianMatrix (Fin 0) => (0:ℝ)) :=
      funext (jacobiSquaredError_zero (n+1:ℝ)⁻¹)
    constructor
    · rw [hz]
      exact integrable_const (0:ℝ)
    · rw [hz]
      simp
  | succ m ih =>
    let μ := (stdGaussian (GaussianMatrix (Fin (m+1)))).map
      (symmetrizeGaussianMatrix (goeScale n))
    have hd := (symmetrized_diagonal_preserving m (goeScale n)).hasLaw
    have hc := (symmetrized_columnNorm_preserving m (goeScale n)).hasLaw
    have ht := (symmetrized_reducedTail_preserving m (goeScale n)).hasLaw
    have hdI : Integrable (fun A : GaussianMatrix (Fin (m+1)) => (A 0 0)^2) μ :=
      hd.integrable_fun_comp (diagonal_sq_integrable n)
    have hcI : Integrable (fun A : GaussianMatrix (Fin (m+1)) =>
        (‖firstColumn A‖-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2) μ :=
      hc.integrable_fun_comp (columnNorm_error_integrable n m)
    have htI : Integrable (fun A : GaussianMatrix (Fin (m+1)) =>
        jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A)) μ :=
      ht.integrable_fun_comp ih.1
    let g : GaussianMatrix (Fin (m+1)) → ℝ := fun A =>
      (A 0 0)^2 + 2*(‖firstColumn A‖-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2 +
        jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A)
    have hgI : Integrable g μ := (hdI.add (hcI.const_mul 2)).add htI
    have hcenter : Real.sqrt ((n+1:ℝ)⁻¹*(m:ℝ)) =
        Real.sqrt ((m:ℝ)/(n+1:ℝ)) := by
      congr 1
      ring
    have hpoint (A : GaussianMatrix (Fin (m+1))) :
        jacobiSquaredError (n+1:ℝ)⁻¹ (m+1) A ≤ g A := by
      simpa only [hcenter] using jacobiSquaredError_succ_le (n+1:ℝ)⁻¹ m A
    have hI : Integrable (jacobiSquaredError (n+1:ℝ)⁻¹ (m+1)) μ :=
      hgI.mono' (jacobiSquaredError_measurable _ _).aestronglyMeasurable
        (ae_of_all _ fun A => by
          have hz : 0 ≤ jacobiSquaredError (n+1:ℝ)⁻¹ (m+1) A := sq_nonneg _
          simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hpoint A)
    have hdE : (∫ A : GaussianMatrix (Fin (m+1)), (A 0 0)^2 ∂μ) = 2/(n+1:ℝ) := by
      exact (hd.integral_comp (diagonal_sq_integrable n).aestronglyMeasurable).trans
        (diagonal_integral_sq n)
    have hcE : (∫ A : GaussianMatrix (Fin (m+1)),
        (‖firstColumn A‖-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2 ∂μ) ≤ 2/(n+1:ℝ) := by
      calc
        _ = ∫ r : ℝ, (r-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2
            ∂columnNormLaw m (goeScale n) :=
          hc.integral_comp (columnNorm_error_integrable n m).aestronglyMeasurable
        _ ≤ _ := columnNorm_mean_square_error n m
    have htE : (∫ A : GaussianMatrix (Fin (m+1)),
        jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A) ∂μ) ≤ 6*(m:ℝ)/(n+1:ℝ) := by
      calc
        _ = ∫ B, jacobiSquaredError (n+1:ℝ)⁻¹ m B
            ∂((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix (goeScale n))) :=
          ht.integral_comp ih.1.aestronglyMeasurable
        _ ≤ _ := ih.2
    refine ⟨hI, ?_⟩
    calc
      _ ≤ ∫ A, g A ∂μ := integral_mono hI hgI hpoint
      _ = (∫ A : GaussianMatrix (Fin (m+1)), (A 0 0)^2 ∂μ) +
          2*(∫ A : GaussianMatrix (Fin (m+1)),
            (‖firstColumn A‖-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2 ∂μ) +
          (∫ A : GaussianMatrix (Fin (m+1)),
            jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A) ∂μ) := by
        calc
          _ = (∫ A : GaussianMatrix (Fin (m+1)), (A 0 0)^2 +
                2*(‖firstColumn A‖-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2 ∂μ) +
              (∫ A : GaussianMatrix (Fin (m+1)),
                jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A) ∂μ) :=
            integral_add (hdI.add (hcI.const_mul 2)) htI
          _ = ((∫ A : GaussianMatrix (Fin (m+1)), (A 0 0)^2 ∂μ) +
                (∫ A : GaussianMatrix (Fin (m+1)),
                  2*(‖firstColumn A‖-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2 ∂μ)) +
              (∫ A : GaussianMatrix (Fin (m+1)),
                jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A) ∂μ) :=
            congrArg (fun r : ℝ => r + ∫ A : GaussianMatrix (Fin (m+1)),
              jacobiSquaredError (n+1:ℝ)⁻¹ m (reducedTail A) ∂μ)
              (integral_add hdI (hcI.const_mul 2))
          _ = _ := by rw [integral_const_mul]
      _ ≤ 2/(n+1:ℝ) + 2*(2/(n+1:ℝ)) + 6*(m:ℝ)/(n+1:ℝ) := by
        rw [hdE]
        linarith
      _ = 6*((m+1:ℕ):ℝ)/(n+1:ℝ) := by push_cast; ring

theorem jacobiSquaredError_integral_le_six (n : ℕ) :
    (∫ A, jacobiSquaredError (n+1:ℝ)⁻¹ (n+1) A
      ∂((stdGaussian (GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n)))) ≤ 6 := by
  calc
    _ ≤ 6*((n+1:ℕ):ℝ)/(n+1:ℝ) :=
      (jacobiSquaredError_integrable_and_integral_le n (n+1)).2
    _ = 6 := by push_cast; field_simp

theorem jacobiError_memLp_two (n : ℕ) :
    MemLp (fun A : GaussianMatrix (Fin (n+1)) =>
      triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)) 2
      ((stdGaussian (GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n))) := by
  have hm : Measurable (fun A : GaussianMatrix (Fin (n+1)) =>
      triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)) :=
    (triReduce_measurable (n+1)).sub measurable_const
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    (jacobiSquaredError_integrable_and_integral_le n (n+1)).1

theorem jacobiError_norm_integrable (n : ℕ) :
    Integrable (fun A : GaussianMatrix (Fin (n+1)) =>
      ‖triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)‖)
      ((stdGaussian (GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n))) :=
  (jacobiError_memLp_two n).norm.integrable (by norm_num)

/-- The exact actual Gaussian Householder error has bounded mean Frobenius
norm, uniformly in the physical dimension. -/
theorem integral_jacobiError_norm_le_sqrt_six (n : ℕ) :
    (∫ A : GaussianMatrix (Fin (n+1)),
      ‖triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)‖
      ∂((stdGaussian (GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n)))) ≤ Real.sqrt 6 := by
  have hv := variance_nonneg (fun A : GaussianMatrix (Fin (n+1)) =>
      ‖triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)‖)
    ((stdGaussian (GaussianMatrix (Fin (n+1)))).map
      (symmetrizeGaussianMatrix (goeScale n)))
  rw [variance_eq_sub (jacobiError_memLp_two n).norm] at hv
  have he := jacobiSquaredError_integral_le_six n
  have hnonneg : 0 ≤ ∫ A : GaussianMatrix (Fin (n+1)),
      ‖triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)‖
      ∂((stdGaussian (GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n))) := integral_nonneg fun _ => norm_nonneg _
  apply (Real.le_sqrt hnonneg (by norm_num : (0:ℝ) ≤ 6)).mpr
  change (∫ A : GaussianMatrix (Fin (n+1)),
      ‖triReduce (n+1) A - jacobiGaussian (n+1:ℝ)⁻¹ (n+1)‖
      ∂((stdGaussian (GaussianMatrix (Fin (n+1)))).map
        (symmetrizeGaussianMatrix (goeScale n)))) ^ 2 ≤ 6
  change 0 ≤ (∫ A, jacobiSquaredError (n+1:ℝ)⁻¹ (n+1) A
    ∂((stdGaussian (GaussianMatrix (Fin (n+1)))).map
      (symmetrizeGaussianMatrix (goeScale n)))) - _ at hv
  linarith

end TensorPCA.RetainedCountProofs.OAI.CriticalSK
