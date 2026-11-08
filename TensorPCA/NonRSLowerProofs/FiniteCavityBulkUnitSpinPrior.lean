-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.UnitSpinPriorTransport
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition

/-! The bulk Gibbs law as an intrinsic unit-spin probability kernel, with ambient
pushforward and transport of tilt integrals.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityBulkUnitSpinPrior
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteCavityShellGibbsPartition UnitSpinPriorTransport
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem bulkLinear_ae_bounded {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᵐ x ∂Model.spherePrior N, ‖bulkLinear N M k mu beta x‖≤C := by
  obtain ⟨C,hC⟩ := (Geometry.unitSphere_isCompact N).bddAbove_image
    (bulkLinear_continuous N M k mu beta).norm.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  exact (Geometry.spherePrior_norm_ae hN).mono (fun x hx ↦
    (hC ⟨x,hx,rfl⟩).trans (le_max_right _ _))

theorem ambientBulkKernel_apply {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) :
    gibbsKernel (Model.spherePrior N) (bulkLinear N M k mu beta) g=bulkGibbs N M k mu beta g := by
  obtain ⟨C,hC,hbound⟩ := bulkLinear_ae_bounded hN M k mu beta
  exact gibbsKernel_apply _ _ (bulkLinear_continuous N M k mu beta).measurable hC hbound g

/-- Output comap of the bulk Gibbs kernel; no off-sphere default spin or nonmeasurable
selection of representatives is used.
-/
def bulkPriorKernel (N M k : ℕ) (mu beta : ℝ) : Kernel (GroundState.Disorder N k) (UnitSpin N) :=
  priorKernel (gibbsKernel (Model.spherePrior N) (bulkLinear N M k mu beta))

theorem bulkPriorKernel_apply {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) :
    bulkPriorKernel N M k mu beta g=prior (bulkGibbs N M k mu beta g) := by
  change prior (gibbsKernel (Model.spherePrior N) (bulkLinear N M k mu beta) g)=_
  rw [ambientBulkKernel_apply hN M k mu beta g]

theorem bulkPriorKernel_markov {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ) :
    IsMarkovKernel (bulkPriorKernel N M k mu beta) := by
  obtain ⟨C,hC,hbound⟩ := bulkLinear_ae_bounded hN M k mu beta
  let G := gibbsKernel (Model.spherePrior N) (bulkLinear N M k mu beta)
  letI : IsMarkovKernel G := gibbsKernel_markov _ _
    (bulkLinear_continuous N M k mu beta).measurable hC hbound
  exact priorKernel_markov G (fun g ↦ by
    rw [show G g=bulkGibbs N M k mu beta g from ambientBulkKernel_apply hN M k mu beta g]
    exact bulkGibbs_norm_ae hN M k mu beta g)

theorem bulkPriorKernel_probability {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) : IsProbabilityMeasure (bulkPriorKernel N M k mu beta g) := by
  letI := bulkPriorKernel_markov hN M k mu beta
  infer_instance

theorem bulkPriorKernel_measurable (N M k : ℕ) (mu beta : ℝ) :
    Measurable (fun g ↦ bulkPriorKernel N M k mu beta g) := (bulkPriorKernel N M k mu beta).measurable

theorem map_bulkPriorKernel {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) :
    (bulkPriorKernel N M k mu beta g).map ((↑) : UnitSpin N → Model.Vector N)=bulkGibbs N M k mu beta g := by
  rw [bulkPriorKernel_apply hN M k mu beta g]
  exact map_prior _ (bulkGibbs_norm_ae hN M k mu beta g)

theorem integral_bulkPriorKernel {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) (f : Model.Vector N → ℝ) :
    (∫ z : UnitSpin N, f z.val ∂bulkPriorKernel N M k mu beta g)=∫ x, f x ∂bulkGibbs N M k mu beta g := by
  rw [bulkPriorKernel_apply hN M k mu beta g]
  exact integral_prior _ (bulkGibbs_norm_ae hN M k mu beta g) f

theorem map_tilted_bulkPriorKernel {N : ℕ} (hN : 0<N) (M k : ℕ) (mu beta : ℝ)
    (g : GroundState.Disorder N k) (f : Model.Vector N → ℝ) (hf : Measurable f) :
    ((bulkPriorKernel N M k mu beta g).tilted (fun z : UnitSpin N ↦ f z.val)).map
      ((↑) : UnitSpin N → Model.Vector N)=(bulkGibbs N M k mu beta g).tilted f := by
  rw [bulkPriorKernel_apply hN M k mu beta g]
  exact map_tilted_prior _ (bulkGibbs_norm_ae hN M k mu beta g) f hf

theorem map_gibbs_bulkPriorKernel {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (hN : 0<N) (M k : ℕ) (mu beta : ℝ) (g : GroundState.Disorder N k)
    (L : Model.Vector N → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    (gibbsMeasure (bulkPriorKernel N M k mu beta g) (fun z : UnitSpin N ↦ L z.val) w).map
      ((↑) : UnitSpin N → Model.Vector N)=gibbsMeasure (bulkGibbs N M k mu beta g) L w := by
  rw [bulkPriorKernel_apply hN M k mu beta g]
  exact map_gibbs_prior _ (bulkGibbs_norm_ae hN M k mu beta g) L hL w

theorem integral_gibbs_bulkPriorKernel {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (hN : 0<N) (M k : ℕ) (mu beta : ℝ) (g : GroundState.Disorder N k)
    (L : Model.Vector N → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) (f : Model.Vector N → ℝ) :
    (∫ z : UnitSpin N, f z.val ∂gibbsMeasure (bulkPriorKernel N M k mu beta g) (fun z : UnitSpin N ↦ L z.val) w)=
      ∫ x, f x ∂gibbsMeasure (bulkGibbs N M k mu beta g) L w := by
  rw [bulkPriorKernel_apply hN M k mu beta g]
  exact integral_gibbs_prior _ (bulkGibbs_norm_ae hN M k mu beta g) L hL w f

end
end TensorPCA.NonRSLowerProofs.FiniteCavityBulkUnitSpinPrior
