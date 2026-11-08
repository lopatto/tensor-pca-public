-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramRealization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Continuity of the existing canonical square-root rows and fixed bounded
mark products on the compact unit-Gram domain. The probability law is fixed,
so a canonical Gaussian bank can be used without any physical ambient dimension.
This proves mark-product continuity, separately from log-functional continuity. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteUnitGramRealizationContinuity
open Matrix MeasureTheory Set Filter
open FiniteUnitGramRealization
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
noncomputable section

theorem sqrt_continuousOn_unitGram (r : ℕ) :
    ContinuousOn (CFC.sqrt : Matrix (Fin (r+1)) (Fin (r+1)) ℝ → Matrix (Fin (r+1)) (Fin (r+1)) ℝ)
      (unitGramSet (r+1)) :=
  CFC.continuousOn_sqrt.mono (fun _ hA ↦ hA.1.nonneg)

theorem realization_continuousOn_unitGram (r : ℕ) (i : Fin (r+1)) :
    ContinuousOn (fun A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ ↦ realization A i)
      (unitGramSet (r+1)) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro j
  exact ((continuous_apply j).comp (continuous_apply i)).comp_continuousOn
    (sqrt_continuousOn_unitGram r)

theorem bounded_mark_product_continuousOn {G W : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace W]
    (r : ℕ) (mu : Measure G) [IsProbabilityMeasure mu]
    (F : EuclideanSpace ℝ (Fin (r+1)) → G → W)
    (hF : Continuous (fun p : EuclideanSpace ℝ (Fin (r+1))×G ↦ F p.1 p.2))
    (mark : W → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) :
    ContinuousOn (fun A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ ↦
      ∫ g,∏ i : Fin (r+1),mark (F (realization A i) g) ∂mu) (unitGramSet (r+1)) := by
  have hMeas (A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ) :
      AEStronglyMeasurable (fun g ↦ ∏ i : Fin (r+1),mark (F (realization A i) g)) mu := by
    have hc : Continuous (fun g ↦ ∏ i : Fin (r+1),mark (F (realization A i) g)) :=
      continuous_finsetProd Finset.univ (fun i _ ↦ hMark.comp
        (hF.comp (continuous_const.prodMk continuous_id)))
    exact hc.measurable.aestronglyMeasurable
  have hDom (A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ) (g : G) :
      ‖∏ i : Fin (r+1),mark (F (realization A i) g)‖≤1 := by
    rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun i _ ↦ (hBound _).1))]
    exact Finset.prod_le_one₀ (fun i _ ↦ (hBound _).1) (fun i _ ↦ (hBound _).2)
  apply continuousOn_of_dominated (fun A _ ↦ hMeas A)
    (fun A _ ↦ Eventually.of_forall (hDom A)) (integrable_const (1 : ℝ))
  refine Eventually.of_forall (fun g ↦ ?_)
  apply continuousOn_finsetProd Finset.univ
  intro i _
  exact hMark.comp_continuousOn (hF.comp_continuousOn
    ((realization_continuousOn_unitGram r i).prodMk continuousOn_const))

theorem bounded_mark_product_uniformContinuousOn {G W : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace W]
    (r : ℕ) (mu : Measure G) [IsProbabilityMeasure mu]
    (F : EuclideanSpace ℝ (Fin (r+1)) → G → W)
    (hF : Continuous (fun p : EuclideanSpace ℝ (Fin (r+1))×G ↦ F p.1 p.2))
    (mark : W → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) :
    UniformContinuousOn (fun A : Matrix (Fin (r+1)) (Fin (r+1)) ℝ ↦
      ∫ g,∏ i : Fin (r+1),mark (F (realization A i) g) ∂mu) (unitGramSet (r+1)) :=
  (unitGramSet_isCompact (r+1)).uniformContinuousOn_of_continuous
    (bounded_mark_product_continuousOn r mu F hF mark hMark hBound)

end
end TensorPCA.NonRSLowerProofs.FiniteUnitGramRealizationContinuity
