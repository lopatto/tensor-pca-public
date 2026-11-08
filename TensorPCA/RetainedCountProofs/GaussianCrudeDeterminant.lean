-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Narrow attributed source port from immutable pmaronow/slowequilibration-palomar
 a28aaa336343c4caf43791ababd8ed0ee5c7b58e, GaussianCrudeDeterminant.lean.
Only the genuine linear-realization endpoint is retained. Shared checked local
edge APIs and the literal ordinary determinant replace the source's broad
matrix-moment/affine-determinant scaffolding. The unused generic covariance
realization endpoint is not imported. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianSpectralNorm
public import TensorPCA.RetainedCountProofs.GOEClippedDeterminants
public import TensorPCA.RetainedCountProofs.GOERawMoments
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GaussianCrudeDeterminant
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators RealInnerProductSpace
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge GaussianSpectralNorm GOERawMoments
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma upper_edge_exp_integrable
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {σ : ℝ} (hσ : 0 < σ) (hW : ‖W‖ ≤ σ) (r : ℝ) :
    Integrable (fun z => Real.exp (r*upperEigenvalue W z))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hG := upperEigenvalue_centered_subGaussian W hσ hW
  let a := ∫ z,upperEigenvalue W z ∂stdGaussian (EuclideanSpace ℝ ι)
  apply ((hG.integrable_exp_mul r).mul_const (Real.exp (r*a))).congr
  exact ae_of_all _ fun z => by
    change Real.exp (r*(upperEigenvalue W z-a))*Real.exp (r*a)=Real.exp (r*upperEigenvalue W z)
    rw [← Real.exp_add]
    congr 1
    dsimp only [a]
    ring

lemma upper_edge_exp_mean
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    {σ : ℝ} (hσ : 0 < σ) (hW : ‖W‖ ≤ σ)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ z,Real.exp (r*upperEigenvalue W z) ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ 
      Real.exp (r*((Real.sqrt 2*σ)*Real.sqrt (n+1 : ℝ))+σ^2*r^2/2) := by
  have hG := upperEigenvalue_centered_subGaussian W hσ hW
  let a := ∫ z,upperEigenvalue W z ∂stdGaussian (EuclideanSpace ℝ ι)
  have hm := mean_upperEigenvalue_le W hσ.le hW
  simp only [Nat.cast_add,Nat.cast_one] at hm
  have hmgf := hG.mgf_le r
  simp only [mgf,Real.coe_toNNReal _ (sq_nonneg σ)] at hmgf
  have hf : (fun z => Real.exp (r*upperEigenvalue W z))=
      fun z => Real.exp (r*a)*Real.exp (r*(upperEigenvalue W z-a)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf,integral_const_mul]
  calc
    _ ≤ Real.exp (r*a)*Real.exp (σ^2*r^2/2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _=Real.exp (r*a+σ^2*r^2/2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left hm hr
      dsimp only [a]
      linarith)

lemma norm_exp_le_edges (A : GOEAsymptotics.GaussianMatrix (n+1)) (hA : ∀ i j,A i j=A j i)
    {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (r*‖gaussianMatrixCLM A‖) ≤ 
      Real.exp (r*matrixOrderedEigenvalues A 0)+Real.exp (r*matrixOrderedEigenvalues (-A) 0) := by
  let u := matrixOrderedEigenvalues A 0
  let v := matrixOrderedEigenvalues (-A) 0
  have huv : 0 ≤ max u v := by
    have h := neg_eigenvalue_le_upper A hA 0
    have hu : u ≤ max u v := le_max_left _ _
    have hv : v ≤ max u v := le_max_right _ _
    dsimp only [u,v] at hu hv ⊢
    linarith
  have hn := operator_norm_le_edges A hA huv (le_max_left _ _) (le_max_right _ _)
  calc
    _ ≤ Real.exp (r*max u v) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hr)
    _ ≤ _ := by
      rcases le_total u v with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (Real.exp_pos _).le

lemma eigenvalue_abs_le_operator_norm (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j,A i j=A j i) (i : Fin (n+1)) :
    |matrixOrderedEigenvalues A i| ≤ ‖gaussianMatrixCLM A‖ := by
  let hS := gaussianMatrixCLM_symmetric A hA
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := hS.eigenvectorBasis hn i
  have hv : ‖v‖=1 := (hS.eigenvectorBasis hn).norm_eq_one i
  have he : gaussianMatrixCLM A v = hS.eigenvalues hn i • v := hS.apply_eigenvectorBasis hn i
  rw [matrixOrderedEigenvalues_eq A hA]
  calc
    _ = ‖hS.eigenvalues hn i • v‖ := by rw [norm_smul,Real.norm_eq_abs,hv,mul_one]
    _ = ‖gaussianMatrixCLM A v‖ := congrArg norm he.symm
    _ ≤ ‖gaussianMatrixCLM A‖*‖v‖ := (gaussianMatrixCLM A).le_opNorm v
    _ = _ := by rw [hv,mul_one]

lemma rawDet_le_norm_exp (A : GOEAsymptotics.GaussianMatrix (n+1)) (hA : ∀ i j,A i j=A j i) (k : ℝ) :
    matrixAbsoluteDet n k (gaussianToMatrix A) ≤ Real.exp ((n+1 : ℝ)*(|k|+‖gaussianMatrixCLM A‖)) := by
  unfold matrixAbsoluteDet
  rw [GOEClippedDeterminants.shifted_det_eq_prod k A hA,Finset.abs_prod]
  have hi (i : Fin (n+1)) : |k-matrixOrderedEigenvalues A i| ≤ 
      Real.exp (|k|+‖gaussianMatrixCLM A‖) := by
    calc
      _ ≤ |k|+|matrixOrderedEigenvalues A i| := abs_sub _ _
      _ ≤ |k|+‖gaussianMatrixCLM A‖ := by linarith [eigenvalue_abs_le_operator_norm A hA i]
      _ ≤ _ := by linarith [Real.add_one_le_exp (|k|+‖gaussianMatrixCLM A‖)]
  have hp : (∏ i : Fin (n+1),|k-matrixOrderedEigenvalues A i|) ≤ 
      ∏ _i : Fin (n+1),Real.exp (|k|+‖gaussianMatrixCLM A‖) :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hi i)
  apply hp.trans_eq
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul,
    Nat.cast_add,Nat.cast_one]

/-- Crude constant uniform in all source dimensions and all real shifts. -/
def crudeConstant (b : ℝ) : ℝ := Real.log 2+2*Real.sqrt b+b

/-- Actual linear Gaussian matrix, all m=n+1 ≤ N and all real k. -/
theorem realization_crude_mean {N : ℕ}
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j,W z i j=W z j i) (hN : n+1 ≤ N)
    {b : ℝ} (hb : 0 < b) (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) (k : ℝ) :
    Integrable (fun z => matrixAbsoluteDet n k (gaussianToMatrix (W z)))
      (stdGaussian (EuclideanSpace ℝ ι)) ∧
    (∫ z,matrixAbsoluteDet n k (gaussianToMatrix (W z)) ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ 
      Real.exp ((N:ℝ)*(crudeConstant b+|k|)) := by
  have hNp : 0 < N := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hNp
  let σ := Real.sqrt (2*b/N)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hWneg : ‖-W‖ ≤ σ := by simpa only [norm_neg] using hW
  let r : ℝ := n+1
  have hr : 0 ≤ r := by positivity
  let F := fun z => Real.exp (r*upperEigenvalue W z)
  let G := fun z => Real.exp (r*upperEigenvalue (-W) z)
  have hF := upper_edge_exp_integrable W hσ hW r
  have hG := upper_edge_exp_integrable (-W) hσ hWneg r
  have hdom (z) : matrixAbsoluteDet n k (gaussianToMatrix (W z)) ≤ Real.exp (r*|k|)*(F z+G z) := by
    apply (rawDet_le_norm_exp (W z) (hSym z) k).trans
    rw [mul_add,Real.exp_add]
    exact mul_le_mul_of_nonneg_left (norm_exp_le_edges (W z) (hSym z) hr) (Real.exp_pos _).le
  have hIntMajor : Integrable (fun z => Real.exp (r*|k|)*(F z+G z))
      (stdGaussian (EuclideanSpace ℝ ι)) := (hF.add hG).const_mul _
  have hInt : Integrable (fun z => matrixAbsoluteDet n k (gaussianToMatrix (W z)))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    apply hIntMajor.mono' (((matrixAbsoluteDet_measurable n k).comp (gaussianToMatrix_measurable (n+1))).comp W.continuous.measurable).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖matrixAbsoluteDet n k (gaussianToMatrix (W z))‖≤Real.exp (r*|k|)*(F z+G z)
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ matrixAbsoluteDet n k (gaussianToMatrix (W z)) from abs_nonneg _)]
      exact hdom z
  refine ⟨hInt,?_⟩
  have hEF := upper_edge_exp_mean W hσ hW hr
  have hEG := upper_edge_exp_mean (-W) hσ hWneg hr
  have hmN : (n+1 : ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hedge : ((Real.sqrt 2*σ)*Real.sqrt (n+1 : ℝ)) ≤ 2*Real.sqrt b := by
    simpa only [σ,Nat.cast_add,Nat.cast_one] using covariance_edge_scale_le hN hb.le
  have hexp : r*((Real.sqrt 2*σ)*Real.sqrt (n+1 : ℝ))+σ^2*r^2/2 ≤ 
      (N:ℝ)*(2*Real.sqrt b+b) := by
    have hs : σ^2=2*b/(N:ℝ) := Real.sq_sqrt (by positivity)
    rw [hs]
    have hrN : r ≤ (N:ℝ) := hmN
    have he := mul_le_mul_of_nonneg_left hedge hr
    have he2 := mul_le_mul_of_nonneg_right hrN (by positivity : 0 ≤ 2*Real.sqrt b)
    have hp : r^2 ≤ (N:ℝ)^2 := pow_le_pow_left₀ hr hrN 2
    have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ b/(N:ℝ))
    have ht' : (2*b/(N:ℝ))*r^2/2 ≤ (N:ℝ)*b := by
      convert ht using 1 <;> field_simp
    nlinarith
  have hFinal : r*|k|+Real.log 2+(N:ℝ)*(2*Real.sqrt b+b) ≤ 
      (N:ℝ)*(crudeConstant b+|k|) := by
    have hk := mul_le_mul_of_nonneg_right hmN (abs_nonneg k)
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hNp
    have hl := mul_le_mul_of_nonneg_right hN1 hlog
    unfold crudeConstant
    nlinarith
  calc
    _ ≤ ∫ z,Real.exp (r*|k|)*(F z+G z) ∂stdGaussian (EuclideanSpace ℝ ι) := integral_mono hInt hIntMajor hdom
    _=Real.exp (r*|k|)*((∫ z,F z ∂stdGaussian (EuclideanSpace ℝ ι))+
      ∫ z,G z ∂stdGaussian (EuclideanSpace ℝ ι)) := by rw [integral_const_mul,integral_add hF hG]
    _ ≤ Real.exp (r*|k|)*(2*Real.exp ((N:ℝ)*(2*Real.sqrt b+b))) := by
      gcongr
      have hf := hEF.trans (Real.exp_le_exp.mpr hexp)
      have hg := hEG.trans (Real.exp_le_exp.mpr hexp)
      linarith
    _=Real.exp (r*|k|+Real.log 2+(N:ℝ)*(2*Real.sqrt b+b)) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hFinal

end
end TensorPCA.RetainedCountProofs.GaussianCrudeDeterminant
