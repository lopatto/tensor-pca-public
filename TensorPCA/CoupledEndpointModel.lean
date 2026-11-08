-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PairWindowReflectionProofs

/-! Concrete unnormalized endpoint quantities shared by the independent
radial comparison and Gaussian integral evaluation. -/
@[expose] public section
namespace TensorPCA.CoupledEndpointModel
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
noncomputable section

/-- Literal Gaussian tail mass used in the verified PT radial remainder. -/
def gaussianTailMass (N : ℕ) (b : ℝ) : ℝ≥0∞ :=
  stdGaussian (Model.Vector N) {g | (N : ℝ)*b ≤ ‖g‖^2}

/-- Literal unnormalized signed-window common-field partition. -/
def signedCommonPartition (N : ℕ) (a u eta : ℝ) (g : Model.Vector N) : ℝ :=
  ∫ xy, Real.exp (Real.sqrt ((N : ℝ)*a)*inner ℝ (xy.1+xy.2) g)
    ∂PairWindowReflectionProofs.signedWindowLaw N u eta

end
end TensorPCA.CoupledEndpointModel
