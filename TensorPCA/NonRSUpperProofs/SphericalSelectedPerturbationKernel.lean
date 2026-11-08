-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed port from immutable Apache-2.0 source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SphericalSelectedPerturbationKernel.lean
Only namespace/import paths are adapted to the checked local Gaussian
foundation. Definitions and proof arguments are retained. See LICENSE. -/
module

public import TensorPCA.NonRSUpperProofs.SphericalPositivePerturbationProbe
public import TensorPCA.NonRSUpperProofs.GaussianSelectedReplicaIBP

@[expose] public section

/-! The selected Gaussian covariance of the finite tensor
perturbation is its coefficient squared times the literal overlap power. -/
namespace TensorPCA.NonRSUpperProofs.SphericalPositivePerturbation
noncomputable section
open MeasureTheory Set GaussianReplicaCalculus
open scoped BigOperators RealInnerProductSpace
open TensorPCA.RetainedCountProofs.FiniteModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem selectedKernel_degree {N K : ℕ} (a : Fin K → ℝ) (p : Fin K) (z y : Vector N) :
    selectedKernel (linear a) (degreeLabel p) z y=
      (a p)^2*(inner ℝ z y)^(p.val+1) := by
  classical
  simp only [selectedKernel,linear_coordinate,degreeLabel,decide_eq_true_eq,Fintype.sum_sigma]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true]
    have hEq : (fun I : TensorIndex N (p.val+1) =>
        (a p*tensorMonomial z I)*(a p*tensorMonomial y I))=
        fun I => (a p)^2*(tensorMonomial z I*tensorMonomial y I) := by
      funext I
      ring
    rw [hEq,← Finset.mul_sum,tensorMonomial_gram]
  · intro j _ hj
    simp [hj]
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

abbrev UnitSpin (N : ℕ) := {z : Vector N // ‖z‖=1}

def unitLinear {N K : ℕ} (a : Fin K → ℝ) : UnitSpin N → PerturbationDisorder N K →L[ℝ] ℝ :=
  fun z => linear a z.val

theorem unitLinear_measurable {N K : ℕ} (a : Fin K → ℝ) :
    Measurable (unitLinear (N:=N) a) := (linear_measurable a).comp measurable_subtype_coe

theorem unitLinear_norm_bound {N K : ℕ} {v : ℝ} (hv : 0≤v) (x : Fin K → ℝ)
    (hx : ∀ p,|x p|≤2) (z : UnitSpin N) :
    ‖unitLinear (coefficients v x) z‖ ≤ 2*v :=
  perturbation_linear_bound hv x hx z.val z.property

theorem unit_selectedKernel {N K : ℕ} (a : Fin K → ℝ) (p : Fin K) (z y : UnitSpin N) :
    selectedKernel (unitLinear a) (degreeLabel p) z y=
      (a p)^2*(inner ℝ z.val y.val)^(p.val+1) := selectedKernel_degree a p z.val y.val

theorem unit_selectedKernel_diagonal {N K : ℕ} (a : Fin K → ℝ) (p : Fin K) (z : UnitSpin N) :
    selectedKernel (unitLinear a) (degreeLabel p) z z=(a p)^2 := by
  rw [unit_selectedKernel,real_inner_self_eq_norm_sq,z.property]
  simp

theorem unit_active_diagonal {N K : ℕ} (a : Fin K → ℝ) (p : Fin K) (z : UnitSpin N) :
    (∑ i : TensorCoordinate N K,if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable (unitLinear a) i z)^2 else 0)=(a p)^2 :=
  active_diagonal a p z.val z.property

end
end TensorPCA.NonRSUpperProofs.SphericalPositivePerturbation
