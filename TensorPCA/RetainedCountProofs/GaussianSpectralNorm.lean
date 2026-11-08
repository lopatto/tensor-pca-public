-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite spectral-norm source port from immutable
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
GaussianSpectralNorm.lean. The checked local Rayleigh/comparison APIs replace
unrelated spectral-asymptotic imports. Only exact finite eigenbasis arguments
and Gaussian tails are used. See the repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianDominatedEdge
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GaussianSpectralNorm
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma eigenvalue_le_upper {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    matrixOrderedEigenvalues A i ≤ matrixOrderedEigenvalues A 0 := by
  rw [matrixOrderedEigenvalues_eq A hA]
  exact (gaussianMatrixCLM_symmetric A hA).eigenvalues_antitone _ (Fin.zero_le i)

lemma symmetric_norm_le_of_eigenvalues {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) {m : ℕ}
    (hm : Module.finrank ℝ E = m) {r : ℝ} (hr : 0 ≤ r)
    (he : ∀ i : Fin m, |hT.eigenvalues hm i| ≤ r) : ‖T‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg x))).mp
  let B := hT.eigenvectorBasis hm
  have hdiag (i : Fin m) : B.repr (T x) i = hT.eigenvalues hm i * B.repr x i :=
    hT.eigenvectorBasis_apply_self_apply hm x i
  rw [mul_pow, ← B.repr.norm_map (T x), ← B.repr.norm_map x]
  simp only [PiLp.norm_sq_eq_of_L2, hdiag, Real.norm_eq_abs, sq_abs, mul_pow,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr (he i)

lemma neg_eigenvalue_le_upper {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    -matrixOrderedEigenvalues A i ≤ matrixOrderedEigenvalues (-A) 0 := by
  have hnA : ∀ i j, (-A) i j = (-A) j i := by intro i j; change -A i j = -A j i; rw [hA]
  let h := gaussianMatrixCLM_symmetric A hA
  let hn := gaussianMatrixCLM_symmetric (-A) hnA
  let hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := h.eigenvectorBasis hd i
  have hv : v ≠ 0 := (h.eigenvectorBasis hd).orthonormal.ne_zero i
  have he : gaussianMatrixCLM A v = h.eigenvalues hd i • v := h.apply_eigenvectorBasis hd i
  have hneg : gaussianMatrixCLM (-A) = -(gaussianMatrixCLM A) :=
    (gaussianMatrixToCLM (n+1)).map_neg A
  have hen : gaussianMatrixCLM (-A) v = (-h.eigenvalues hd i) • v := by
    rw [hneg, ContinuousLinearMap.neg_apply, he, neg_smul]
  have hHas : Module.End.HasEigenvalue (gaussianMatrixCLM (-A)).toLinearMap
      (-h.eigenvalues hd i) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hen, hv⟩
  obtain ⟨j, hj⟩ := hn.exists_eigenvalues_eq hd hHas
  rw [matrixOrderedEigenvalues_eq A hA, matrixOrderedEigenvalues_eq (-A) hnA]
  exact hj ▸ hn.eigenvalues_antitone hd (Fin.zero_le j)

lemma operator_norm_le_edges {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) {r : ℝ} (hr : 0 ≤ r)
    (hp : matrixOrderedEigenvalues A 0 ≤ r)
    (hn : matrixOrderedEigenvalues (-A) 0 ≤ r) : ‖gaussianMatrixCLM A‖ ≤ r := by
  apply symmetric_norm_le_of_eigenvalues (gaussianMatrixCLM A)
    (gaussianMatrixCLM_symmetric A hA) (m := n+1) (by simp) hr
  intro i
  have hupper := (eigenvalue_le_upper A hA i).trans hp
  have hlower := (neg_eigenvalue_le_upper A hA i).trans hn
  rw [matrixOrderedEigenvalues_eq A hA] at hupper hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem operator_norm_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {n N : ℕ}
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j, W z i j = W z j i) (hN : n+1 ≤ N)
    {b : ℝ} (hb : 0 < b) (hW : ‖W‖ ≤ Real.sqrt (2*b/N))
    {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      {z | 2*Real.sqrt b+t < ‖gaussianMatrixCLM (W z)‖} ≤
        2*Real.exp (-(N : ℝ)*t^2/(4*b)) := by
  have hWn : ‖-W‖ ≤ Real.sqrt (2*b/N) := by simpa only [norm_neg] using hW
  have hp := upperEigenvalue_tail_covarianceScale W hN hb hW ht
  have hn := upperEigenvalue_tail_covarianceScale (-W) hN hb hWn ht
  have hsub : {z | 2*Real.sqrt b+t < ‖gaussianMatrixCLM (W z)‖} ⊆
      {z | 2*Real.sqrt b+t ≤ upperEigenvalue W z} ∪
      {z | 2*Real.sqrt b+t ≤ upperEigenvalue (-W) z} := by
    intro z hz
    by_cases hpz : 2*Real.sqrt b+t ≤ upperEigenvalue W z
    · exact Or.inl hpz
    right
    by_contra hnz
    have he := operator_norm_le_edges (W z) (hSym z) (by positivity : 0 ≤ 2*Real.sqrt b+t)
      (not_le.mp hpz).le (not_le.mp hnz).le
    exact (not_le.mpr hz) he
  calc
    _ ≤ (stdGaussian (EuclideanSpace ℝ ι)).real
        ({z | 2*Real.sqrt b+t ≤ upperEigenvalue W z} ∪
         {z | 2*Real.sqrt b+t ≤ upperEigenvalue (-W) z}) := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

/-- Genuine operator-norm integrability, needed when the tail estimate is
used inside actual GOE determinant expectations. -/
theorem operatorNorm_integrable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j, W z i j = W z j i) :
    Integrable (fun z ↦ ‖gaussianMatrixCLM (W z)‖) (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hI : Integrable (fun z ↦ |upperEigenvalue W z|+|upperEigenvalue (-W) z|)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (upperEigenvalue_integrable W).abs.add (upperEigenvalue_integrable (-W)).abs
  apply hI.mono' (((gaussianMatrixCLM_continuous (n+1)).comp W.continuous).norm.aestronglyMeasurable)
  exact .of_forall fun z ↦ by
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    have hp := (le_abs_self (upperEigenvalue W z)).trans
      (le_add_of_nonneg_right (abs_nonneg (upperEigenvalue (-W) z)))
    have hn := (le_abs_self (upperEigenvalue (-W) z)).trans
      (le_add_of_nonneg_left (abs_nonneg (upperEigenvalue W z)))
    exact operator_norm_le_edges (W z) (hSym z) (add_nonneg (abs_nonneg _) (abs_nonneg _)) hp hn

end
end TensorPCA.RetainedCountProofs.GaussianSpectralNorm
