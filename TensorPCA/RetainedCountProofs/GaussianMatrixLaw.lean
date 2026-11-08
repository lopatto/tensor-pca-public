-- SPDX-License-Identifier: Apache-2.0
/- Narrow exact Gaussian law port from immutable pmaronow/slowequilibration-palomar
 a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
 Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean (credited
 openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb) and GOEAsymptotics.lean.
 Only finite Gaussian entry independence and the literal upper-product bridge
 are retained. The sole GOE definition is SphericalGaussianJet.goeLaw;
 symmetrized standard Gaussian maps are written explicitly, not redefined.
 See the repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixSymmetry
public import TensorPCA.RetainedCountProofs.SphericalGaussianJet
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
@[expose] public section
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma covariance_inner_stdGaussian (v w : E) :
    cov[fun x => inner ℝ v x, fun x => inner ℝ w x; stdGaussian E] = inner ℝ v w := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  rfl

lemma inner_stdGaussian_law (v : E) :
    (stdGaussian E).map (fun x => inner ℝ v x) =
      gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  have hG : HasGaussianLaw (fun x : E => inner ℝ v x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ v)
  rw [hG.map_eq_gaussianReal]
  congr 1
  · exact integral_strongDual_stdGaussian (innerSL ℝ v)
  · rw [← covariance_self (by fun_prop), covariance_inner_stdGaussian, real_inner_self_eq_norm_sq]

lemma gaussian_orthogonal_independent {κ : Type*} [Fintype κ] (v : κ → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) = 0)) :
    iIndepFun (fun i x => inner ℝ (v i) x) (stdGaussian E) := by
  have hG : HasGaussianLaw (fun x : E => fun i => inner ℝ (v i) x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi (fun i => innerSL ℝ (v i)))
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [covariance_inner_stdGaussian]
  exact hv hij


end Gaussian
section Entries
variable {ι : Type*} [Fintype ι]
noncomputable def matrixUnit (i j : ι) : GaussianMatrix ι := by
  classical
  exact PiLp.single 2 i (EuclideanSpace.single j 1)

@[simp] lemma matrixUnit_inner (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (matrixUnit i j) A = A i j := by
  classical
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp [matrixUnit, EuclideanSpace.inner_single_left]
  · intro k _ hki
    simp [matrixUnit, hki]
  · simp

@[simp] lemma matrixUnit_apply [DecidableEq ι] (i j k l : ι) :
    matrixUnit i j k l = if k = i ∧ l = j then 1 else 0 := by
  classical
  simp [matrixUnit]
  split_ifs <;> simp_all

def goeEntryVector (s : ℝ) (i j : ι) : GaussianMatrix ι :=
  s • (matrixUnit i j + matrixUnit j i)

lemma goeEntryVector_inner (s : ℝ) (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (goeEntryVector s i j) A = symmetrizeGaussianMatrix s A i j := by
  simp [goeEntryVector, symmetrizeGaussianMatrix, inner_smul_left, inner_add_left]

lemma goe_entry_variance [DecidableEq ι] (s : ℝ) (i j : ι) :
    ‖goeEntryVector s i j‖ ^ 2 = if i = j then 4 * s ^ 2 else 2 * s ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  by_cases hij : i = j
  · subst j
    simp only [and_self, ite_true]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, and_self, ite_true, ite_false]
    ring

lemma symmetrized_entry_law [DecidableEq ι] (s : ℝ) (i j : ι) :
    ((stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)).map (fun A => A i j) =
      gaussianReal 0 (if i = j then (4 * s ^ 2).toNNReal else (2 * s ^ 2).toNNReal) := by
  classical
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, ← goeEntryVector_inner]
  rw [inner_stdGaussian_law, goe_entry_variance]
  split_ifs <;> rfl


end Entries
section Upper
variable {m : ℕ}
lemma goeEntryVector_orthogonal (s : ℝ) :
    Pairwise (fun p q : SphericalGaussianJet.UpperIndex m =>
      inner ℝ (goeEntryVector s p.1.1 p.1.2) (goeEntryVector s q.1.1 q.1.2) = 0) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ hpq
  have h1 : ¬(i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    exact hpq rfl
  have h2 : ¬(i = l ∧ j = k) := by
    intro hs
    have he : i = j := le_antisymm hij (by simpa only [hs.1, hs.2] using hkl)
    apply hpq
    apply Subtype.ext
    exact Prod.ext (he.trans hs.2) (he.symm.trans hs.1)
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  simp only [h1, h2, ite_false, add_zero, mul_zero,
    show ¬(j = k ∧ i = l) from fun h => h2 ⟨h.2, h.1⟩,
    show ¬(j = l ∧ i = k) from fun h => h1 ⟨h.2, h.1⟩]

lemma symmetrized_entries_independent (s : ℝ) :
    iIndepFun (fun p : SphericalGaussianJet.UpperIndex m => fun A : GaussianMatrix (Fin m) => A p.1.1 p.1.2)
      ((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s)) := by
  have h := gaussian_orthogonal_independent
    (fun p : SphericalGaussianJet.UpperIndex m => goeEntryVector s p.1.1 p.1.2) (goeEntryVector_orthogonal s)
  simp only [goeEntryVector_inner] at h
  let : IsProbabilityMeasure ((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s)) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => by fun_prop)).2
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  have hh := h.map_fun_eq_pi_map (fun _ => by fun_prop)
  simp only [Function.comp_def] at *
  rw [hh]
  congr 1
  ext p : 1
  exact (Measure.map_map (g := fun A : GaussianMatrix (Fin m) => A p.1.1 p.1.2) (by fun_prop)
    (symmetrizeGaussianMatrix_continuous s).measurable).symm
def upperRead (A : GaussianMatrix (Fin m)) : SphericalGaussianJet.UpperIndex m → ℝ := fun p => A p.1.1 p.1.2

def upperWrite (a : SphericalGaussianJet.UpperIndex m → ℝ) : GaussianMatrix (Fin m) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j =>
    if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), (le_of_not_ge h)⟩))

lemma upperRead_measurable : Measurable (upperRead (m := m)) := by
  apply Measurable.of_eval
  intro p
  fun_prop [upperRead]

lemma upperWrite_measurable : Measurable (upperWrite (m := m)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  dsimp [upperWrite]
  split_ifs <;> fun_prop

lemma upperWrite_upperRead (A : GaussianMatrix (Fin m)) (hA : ∀ i j, A i j = A j i) :
    upperWrite (upperRead A) = A := by
  ext i j
  dsimp [upperWrite, upperRead]
  split_ifs
  · rfl
  · exact hA j i

@[simp] lemma upperRead_upperWrite (a : SphericalGaussianJet.UpperIndex m → ℝ) :
    upperRead (upperWrite a) = a := by
  funext p
  exact dite_eq_left p.2

lemma symmetrized_symmetric_ae (s : ℝ) : ∀ᵐ A ∂((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s)), ∀ i j, A i j = A j i := by
  apply (ae_map_iff (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable (by measurability)).2
  filter_upwards [] with A i j
  simp only [symmetrizeGaussianMatrix, PiLp.smul_apply, PiLp.add_apply,
    transposeGaussianMatrix_apply, smul_eq_mul]
  ring

lemma symmetrized_upper_law (s : ℝ) :
    (((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s))).map upperRead = Measure.pi (fun p : SphericalGaussianJet.UpperIndex m =>
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)) := by
  unfold upperRead
  rw [(symmetrized_entries_independent (m := m) s).map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext p
  exact symmetrized_entry_law s p.1.1 p.1.2

lemma symmetrized_eq_upper_product (s : ℝ) :
    ((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s)) = (Measure.pi (fun p : SphericalGaussianJet.UpperIndex m =>
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal))).map
        upperWrite := by
  rw [← symmetrized_upper_law, Measure.map_map upperWrite_measurable upperRead_measurable]
  have heq : (upperWrite ∘ upperRead : GaussianMatrix (Fin m) → GaussianMatrix (Fin m)) =ᵐ[((stdGaussian (GaussianMatrix (Fin m))).map (symmetrizeGaussianMatrix s))] id := by
    filter_upwards [symmetrized_symmetric_ae (m := m) s] with A hA
    exact upperWrite_upperRead A hA
  rw [Measure.map_congr heq, Measure.map_id]

end Upper
end
end TensorPCA.RetainedCountProofs.OAI.CriticalSK
namespace TensorPCA.RetainedCountProofs.GOEAsymptotics
noncomputable section
open MeasureTheory ProbabilityTheory OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact literal agreement with the existing independent-upper-entry GOE.
The map on the right is the actual symmetric standard Gaussian realization. -/
theorem goeLaw_bridge (m N : ℕ) (b sigma : ℝ) (hscale : 2*sigma^2 = b/(N : ℝ)) :
    (SphericalGaussianJet.goeLaw m N b).map matrixToGaussian =
      (stdGaussian (GaussianMatrix m)).map (symmetrizeGaussianMatrix sigma) := by
  rw [symmetrized_eq_upper_product (m := m) sigma]
  unfold SphericalGaussianJet.goeLaw
  rw [Measure.map_map (matrixToGaussian_measurable m) (SphericalGaussianJet.symmetricMatrix_measurable m)]
  have hmarg : (fun ij : SphericalGaussianJet.UpperIndex m ↦ gaussianReal 0
      (((b/(N : ℝ))*(if ij.val.1=ij.val.2 then 2 else 1)).toNNReal)) =
      (fun ij : SphericalGaussianJet.UpperIndex m ↦ gaussianReal 0
        (if ij.val.1=ij.val.2 then (4*sigma^2).toNNReal else (2*sigma^2).toNNReal)) := by
    funext ij
    split_ifs
    · congr 1
      apply congrArg Real.toNNReal
      rw [← hscale]
      ring
    · simp [hscale]
  rw [hmarg]
  rfl

end
end TensorPCA.RetainedCountProofs.GOEAsymptotics
