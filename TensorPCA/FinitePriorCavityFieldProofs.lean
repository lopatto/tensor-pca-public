-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorChannelProofs
public import TensorPCA.TensorCavitySubsetProofs
public import TensorPCA.GaussianMaximumComparisonProofs

/-! Exact finite product-prior cavity fields. The old-coordinate background
retains the N+1 coefficient, and the last-coordinate quadratic penalty is
retained for nonunit scalar priors. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityFieldProofs
open MeasureTheory ProbabilityTheory TensorOrbitCountProofs TensorCavitySubsetProofs
open FinitePriorChannelProofs TensorOrbitAggregationProofs GaussianPriorTransferProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S]

def oldConfiguration {N : ℕ} (x : Fin (N+1) → S) : Fin N → S := fun i ↦ x i.castSucc

/-- Actual unordered tensor background normalized by N+1, not N. -/
def backgroundSignal (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) :
    EuclideanSpace ℝ (KSubset N k) :=
  WithLp.toLp 2 (fun T ↦ aggregateCoefficient (N+1) k gamma*∏ i ∈ T.1, a (x i))

/-- Coefficient vector of the fresh last-coordinate linear field. -/
def cavitySignal (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) :
    EuclideanSpace ℝ (KSubset N (k-1)) :=
  WithLp.toLp 2 (fun T ↦ aggregateCoefficient (N+1) k gamma*∏ i ∈ T.1, a (x i))

def disorderReindex {N k : ℕ} (hk : 0 < k) : EuclideanSpace ℝ (KSubset (N+1) k) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (KSubset N k ⊕ KSubset N (k-1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (subsetSplitEquiv hk)

def disorderSplit {N k : ℕ} (hk : 0 < k) : EuclideanSpace ℝ (KSubset (N+1) k) →L[ℝ]
    EuclideanSpace ℝ (KSubset N k) × EuclideanSpace ℝ (KSubset N (k-1)) :=
  GaussianCompactFeatureComparison.sumSplit.comp
    (disorderReindex hk).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem disorderSplit_old_apply {N k : ℕ} (hk : 0 < k)
    (w : EuclideanSpace ℝ (KSubset (N+1) k)) (T : KSubset N k) :
    (disorderSplit hk w).1 T = w (oldSubset T) := rfl

@[simp] theorem disorderSplit_last_apply {N k : ℕ} (hk : 0 < k)
    (w : EuclideanSpace ℝ (KSubset (N+1) k)) (T : KSubset N (k-1)) :
    (disorderSplit hk w).2 T = w (lastSubset hk T) := rfl

/-- The old and fresh tensor-coordinate blocks have the actual independent
canonical Gaussian product law. No covariance hypothesis is supplied. -/
theorem disorderSplit_gaussian_map {N k : ℕ} (hk : 0 < k) :
    (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k))).map (disorderSplit hk) =
      (stdGaussian (EuclideanSpace ℝ (KSubset N k))).prod
        (stdGaussian (EuclideanSpace ℝ (KSubset N (k-1)))) := by
  change (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k))).map
    (GaussianCompactFeatureComparison.sumSplit ∘ disorderReindex hk) = _
  rw [← Measure.map_map GaussianCompactFeatureComparison.sumSplit.continuous.measurable
    (disorderReindex hk).continuous.measurable,stdGaussian_map]
  simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using
    (GaussianCompactFeatureComparison.sumSplit_gaussian_map
      (ι := KSubset N k) (κ := KSubset N (k-1)))

theorem tensorSignal_old {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ) (x : Fin (N+1) → S) :
    (disorderSplit hk (tensorSignal a (N+1) k gamma x)).1 = backgroundSignal a N k gamma (oldConfiguration x) := by
  ext T
  change aggregateCoefficient (N+1) k gamma*(∏ i ∈ (oldSubset T).1, a (x i)) =
    aggregateCoefficient (N+1) k gamma*(∏ i ∈ T.1, a (x i.castSucc))
  rw [prod_oldSubset]

theorem tensorSignal_last {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ) (x : Fin (N+1) → S) :
    (disorderSplit hk (tensorSignal a (N+1) k gamma x)).2 =
      a (x (Fin.last N)) • cavitySignal a N k gamma (oldConfiguration x) := by
  ext T
  change aggregateCoefficient (N+1) k gamma*(∏ i ∈ (lastSubset hk T).1, a (x i)) =
    a (x (Fin.last N))*(aggregateCoefficient (N+1) k gamma*(∏ i ∈ T.1, a (x i.castSucc)))
  rw [prod_lastSubset]
  ring

theorem inner_eq_split {N k : ℕ} (hk : 0 < k) (v w : EuclideanSpace ℝ (KSubset (N+1) k)) :
    inner ℝ v w = inner ℝ (disorderSplit hk v).1 (disorderSplit hk w).1+
      inner ℝ (disorderSplit hk v).2 (disorderSplit hk w).2 := by
  calc
    _ = inner ℝ (disorderReindex hk v) (disorderReindex hk w) :=
      ((disorderReindex hk).inner_map_map v w).symm
    _ = _ := by
      simp only [PiLp.inner_apply,Fintype.sum_sum_type]
      rfl

theorem norm_sq_eq_split {N k : ℕ} (hk : 0 < k) (v : EuclideanSpace ℝ (KSubset (N+1) k)) :
    ‖v‖^2 = ‖(disorderSplit hk v).1‖^2+‖(disorderSplit hk v).2‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_eq_split hk v v

theorem cavitySignal_inner (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x y : Fin N → S) :
    inner ℝ (cavitySignal a N k gamma x) (cavitySignal a N k gamma y) =
      (aggregateCoefficient (N+1) k gamma)^2*
        ∑ T : KSubset N (k-1), ∏ i ∈ T.1, a (x i)*a (y i) := by
  rw [cavitySignal,cavitySignal,EuclideanSpace.inner_toLp_toLp]
  change (∑ T : KSubset N (k-1), (aggregateCoefficient (N+1) k gamma*∏ i ∈ T.1, a (y i))*
      (aggregateCoefficient (N+1) k gamma*∏ i ∈ T.1, a (x i))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib]
  ring

/-- The literal exponent of the actual planted Gaussian likelihood. -/
def plantedHamiltonian (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X x : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : ℝ :=
  inner ℝ (tensorSignal a N k gamma x) (tensorSignal a N k gamma X+w)-‖tensorSignal a N k gamma x‖^2/2

def backgroundHamiltonian (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X x : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : ℝ :=
  inner ℝ (backgroundSignal a N k gamma x) (backgroundSignal a N k gamma X+w)-‖backgroundSignal a N k gamma x‖^2/2

def cavityZ (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X x : Fin N → S) (Xlast : S) (w : EuclideanSpace ℝ (KSubset N (k-1))) : ℝ :=
  inner ℝ (cavitySignal a N k gamma x) (a Xlast • cavitySignal a N k gamma X+w)

def cavityS (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x : Fin N → S) : ℝ :=
  -‖cavitySignal a N k gamma x‖^2/2

/-- Finite cavity decomposition, with no Gaussian distributional or
asymptotic premise and with the complete scalar-square penalty. -/
theorem plantedHamiltonian_cavity {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ)
    (X x : Fin (N+1) → S) (w : EuclideanSpace ℝ (KSubset (N+1) k)) :
    plantedHamiltonian a (N+1) k gamma X x w =
      backgroundHamiltonian a N k gamma (oldConfiguration X) (oldConfiguration x) (disorderSplit hk w).1+
        a (x (Fin.last N))*cavityZ a N k gamma (oldConfiguration X) (oldConfiguration x)
          (X (Fin.last N)) (disorderSplit hk w).2+
        (a (x (Fin.last N)))^2*cavityS a N k gamma (oldConfiguration x) := by
  unfold plantedHamiltonian
  rw [inner_eq_split hk,norm_sq_eq_split hk]
  simp only [map_add,Prod.fst_add,Prod.snd_add,tensorSignal_old hk,tensorSignal_last hk,
    real_inner_smul_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold backgroundHamiltonian cavityZ cavityS
  ring

theorem mixtureWeight_cavity {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ)
    (X x : Fin (N+1) → S) (w : EuclideanSpace ℝ (KSubset (N+1) k)) :
    mixtureWeight (tensorSignal a (N+1) k gamma x) (tensorSignal a (N+1) k gamma X+w) =
      Real.exp (backgroundHamiltonian a N k gamma (oldConfiguration X) (oldConfiguration x) (disorderSplit hk w).1)*
      Real.exp (a (x (Fin.last N))*cavityZ a N k gamma (oldConfiguration X) (oldConfiguration x)
        (X (Fin.last N)) (disorderSplit hk w).2+(a (x (Fin.last N)))^2*cavityS a N k gamma (oldConfiguration x)) := by
  rw [mixtureWeight,show inner ℝ (tensorSignal a (N+1) k gamma x) (tensorSignal a (N+1) k gamma X+w)-
      ‖tensorSignal a (N+1) k gamma x‖^2/2 = plantedHamiltonian a (N+1) k gamma X x w from rfl,
    plantedHamiltonian_cavity hk,← Real.exp_add]
  congr 1
  ring

end
end TensorPCA.FinitePriorCavityFieldProofs
