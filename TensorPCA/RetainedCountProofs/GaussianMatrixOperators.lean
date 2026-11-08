-- SPDX-License-Identifier: Apache-2.0
/- Static matrix-operator port from immutable slowequilibration-palomar
pin a28aaa336343c4caf43791ababd8ed0ee5c7b58e: GOEAsymptotics.lean and
Upstream/OAI/MathematicalPhysics/CriticalSK/{GaussianMatrices,GOESpectrum}.lean.
The upstream files attribute openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Only the literal matrix representation, operator and Borel conversions are
retained; no spectral estimate is imported or assumed. Bodies unchanged apart
from namespace prefixes. Apache-2.0; see repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.SphericalConcentration
public import Mathlib.Analysis.Normed.Lp.Matrix
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
abbrev GaussianMatrix (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℝ ι)

def gaussianMatrixCLM {n : ℕ} (A : GaussianMatrix (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toLpLin 2 2 (fun i j => A i j)).toContinuousLinearMap

def gaussianMatrixToCLM (n : ℕ) : GaussianMatrix (Fin n) →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun := gaussianMatrixCLM
  map_add' A B := by
    ext x i
    change (∑ j, (A i j+B i j)*x j) = (∑ j, A i j*x j)+(∑ j, B i j*x j)
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' r A := by
    ext x i
    change (∑ j, (r*A i j)*x j) = r*(∑ j, A i j*x j)
    simp only [mul_assoc,Finset.mul_sum]

lemma finite_real_linear_continuous {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] (T : D →ₗ[ℝ] F) : Continuous T :=
  T.continuous_of_finiteDimensional

lemma gaussianMatrixCLM_continuous (n : ℕ) : Continuous (gaussianMatrixCLM (n := n)) := by
  change Continuous (gaussianMatrixToCLM n)
  exact finite_real_linear_continuous (gaussianMatrixToCLM n)


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
namespace TensorPCA.RetainedCountProofs.GOEAsymptotics
abbrev GaussianMatrix (k : ℕ) := TensorPCA.RetainedCountProofs.OAI.CriticalSK.GaussianMatrix (Fin k)

def matrixToGaussian {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ) : GaussianMatrix k :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => W i j))

def gaussianToMatrix {k : ℕ} (W : GaussianMatrix k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => W i j

theorem matrixToGaussian_measurable (k : ℕ) : Measurable (matrixToGaussian (k := k)) := by
  unfold matrixToGaussian
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply j).comp (measurable_pi_apply i)

theorem gaussianToMatrix_measurable (k : ℕ) : Measurable (gaussianToMatrix (k := k)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) j).measurable.comp
    (PiLp.continuous_apply 2 (fun _ : Fin k => EuclideanSpace ℝ (Fin k)) i).measurable

@[simp] theorem matrixToGaussian_gaussianToMatrix {k : ℕ} (W : GaussianMatrix k) :
    matrixToGaussian (gaussianToMatrix W) = W := by ext i j; rfl

@[simp] theorem gaussianToMatrix_matrixToGaussian {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ) :
    gaussianToMatrix (matrixToGaussian W) = W := rfl


end TensorPCA.RetainedCountProofs.GOEAsymptotics
