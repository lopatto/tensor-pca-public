-- SPDX-License-Identifier: MIT
/-
MIT License

Copyright (c) 2026 P. M. Aronow and Patrick Lopatto

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Immutable source: pmaronow/aging-temp e28568e30a6ea1e20fce2b8e0a3a72da15759209,
formalization/SphericalAging/SphereInitialLaw.lean, retained byte-identically at
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
vendor/all-lean/SphericalAging/SphereInitialLaw.lean.
Only the sphere-law prefix before Sample/driver is ported; stochastic driver/sample declarations
are outside this static count-foundation scope. The namespace/import prefix is
changed, while retained mathematical definitions/proof bodies are unchanged.
Local porting changes are Apache-2.0.
-/
module

public import TensorPCA.RetainedCountProofs.FiniteModel
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

/-!
# The uniform spherical initial distribution and annealed sample space

The initial point is the radial normalization of a standard Euclidean Gaussian. Rotation invariance is proved by transport of the Gaussian law. Initial state, ordered disorder and all Brownian paths are independent
coordinates of one explicit product probability space.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal

namespace TensorPCA.RetainedCountProofs.SphereInitialLaw
open FiniteModel

/-- Actual standard Euclidean Gaussian law. -/
@[expose] def gaussianLaw (N : ℕ) : Measure (Vector N) := stdGaussian (Vector N)

instance gaussianLaw_probability (N : ℕ) : IsProbabilityMeasure (gaussianLaw N) := by
  unfold gaussianLaw
  infer_instance

/-- Radial normalization onto the sphere of squared radius `N`. -/
@[expose] def normalize (N : ℕ) (x : Vector N) : Vector N := (Real.sqrt N / ‖x‖) • x

theorem normalize_measurable (N : ℕ) : Measurable (normalize N) := by
  unfold normalize
  fun_prop

/-- The canonical rotation-invariant probability law on the manuscript's sphere. -/
@[expose] def sphereLaw (N : ℕ) : Measure (Vector N) := (gaussianLaw N).map (normalize N)

instance sphereLaw_probability (N : ℕ) : IsProbabilityMeasure (sphereLaw N) := by
  unfold sphereLaw
  infer_instance

theorem gaussian_coordinate_hasLaw {N : ℕ} (i : Fin N) :
    HasLaw (fun x : Vector N => x i) (gaussianReal 0 1) (gaussianLaw N) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianLaw,← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (Function.eval i)=_
  exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).map_eq

theorem gaussian_ne_zero_ae {N : ℕ} (hN : 1 ≤ N) : ∀ᵐ x ∂gaussianLaw N, x ≠ 0 := by
  let i : Fin N := ⟨0,by omega⟩
  have ha : ∀ᵐ r ∂gaussianReal 0 1, r ≠ 0 := by
    apply (gaussianReal_absolutelyContinuous 0 (v := 1) one_ne_zero).ae_le
    change ∀ᵐ r : ℝ ∂volume, r ≠ 0
    rw [ae_iff]
    simpa using (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))
  have hb := ((gaussian_coordinate_hasLaw i).ae_iff (by fun_prop)).mpr ha
  filter_upwards [hb] with x hx
  intro he
  exact hx (by rw [he]; rfl)

theorem normalize_norm {N : ℕ} (x : Vector N) (hx : x ≠ 0) :
    ‖normalize N x‖=Real.sqrt N := by
  rw [normalize,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)

theorem normalize_norm_sq {N : ℕ} (x : Vector N) (hx : x ≠ 0) :
    ‖normalize N x‖^2=(N : ℝ) := by
  rw [normalize_norm x hx,Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Exact support on the manuscript sphere, with no support premise. -/
theorem sphereLaw_norm_ae {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂sphereLaw N, ‖x‖=Real.sqrt N := by
  rw [sphereLaw]
  apply (ae_map_iff (normalize_measurable N).aemeasurable ((measurableSet_singleton (Real.sqrt (N : ℝ))).preimage measurable_norm)).mpr
  filter_upwards [gaussian_ne_zero_ae hN] with x hx
  exact normalize_norm x hx

theorem sphereLaw_support {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂sphereLaw N, ‖x‖^2=(N : ℝ) := by
  filter_upwards [sphereLaw_norm_ae hN] with x hx
  rw [hx,Real.sq_sqrt (Nat.cast_nonneg N)]

theorem normalize_equivariant {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) :
    normalize N (U x)=U (normalize N x) := by
  simp [normalize]

/-- Genuine invariance under every orthogonal transformation. -/
theorem sphereLaw_rotation_invariant {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (sphereLaw N).map U=sphereLaw N := by
  have he : U ∘ normalize N=normalize N ∘ U := by
    funext x
    exact (normalize_equivariant U x).symm
  rw [sphereLaw,Measure.map_map (by fun_prop) (normalize_measurable N),he,
    ← Measure.map_map (normalize_measurable N) (by fun_prop)]
  rw [show (gaussianLaw N).map U=gaussianLaw N from stdGaussian_map U]

/-- Every finite or infinite Lp exponent is available from the exact sphere norm. -/
theorem sphereLaw_memLp {N : ℕ} (hN : 1 ≤ N) (q : ℝ≥0∞) :
    MemLp (id : Vector N → Vector N) q (sphereLaw N) :=
  MemLp.of_bound (by fun_prop) (Real.sqrt N) ((sphereLaw_norm_ae hN).mono (fun _ hx => hx.le))



end TensorPCA.RetainedCountProofs.SphereInitialLaw
