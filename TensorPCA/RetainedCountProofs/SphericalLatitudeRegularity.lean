-- SPDX-License-Identifier: Apache-2.0
/- Narrow exact source port from immutable pmaronow/slowequilibration-palomar
 a28aaa336343c4caf43791ababd8ed0ee5c7b58e, SphericalLatitudeRegularity.lean.
 Only the scalar square-root/chord and actual latitude-map distance lemmas
 are retained. Unused field/partition/spatial-modulus sections are omitted.
 Mathematical proof bodies are unchanged; narrow static latitude import
 replaces unrelated spatial regularity. See LICENSE. -/
module

public import TensorPCA.RetainedCountProofs.SphericalLatitude

@[expose] public section

/-!
# Quantitative continuity of the latitude partition

The affine latitude map is uniformly one-half Hölder even at the poles.
The resulting modulus for its log partition is explicit in the tensor disorder norm and supports polynomial finite-grid estimates.
-/

noncomputable section
namespace TensorPCA.RetainedCountProofs.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators InnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sqrt_sub_sq_le_abs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a-Real.sqrt b)^2 ≤ |a-b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) hna
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hba) hnb
    nlinarith

theorem latitude_scalar_chord_bound {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    (q-r)^2+(Real.sqrt (1-q^2)-Real.sqrt (1-r^2))^2 ≤ 4*|q-r| := by
  have hq' : 0 ≤ 1-q^2 := by nlinarith [abs_le.mp hq]
  have hr' : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hs := sqrt_sub_sq_le_abs hq' hr'
  have hd : |q-r| ≤ 2 := by
    exact (abs_sub q r).trans (by linarith)
  have hsum : |q+r| ≤ 2 := (abs_add_le q r).trans (by linarith)
  have he : |(1-q^2)-(1-r^2)| = |q-r| * |q+r| := by
    rw [show (1-q^2)-(1-r^2)=-(q-r)*(q+r) by ring,abs_mul,abs_neg]
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (q-r))
  have hd' := mul_le_mul_of_nonneg_left hd (abs_nonneg (q-r))
  nlinarith [sq_abs (q-r)]

/-- The exact latitude parametrization has a global Hölder modulus with
the correct square-root dimensional scale, including both poles. -/
theorem latitudeMap_dist_le {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    ‖latitudeMap u e q x-latitudeMap u e r x‖ ≤
      2*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt |q-r| := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let v : Vector (n+1) := Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)) • e x
  have hv : ‖v‖^2=((n+1 : ℕ) : ℝ) := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt (by positivity),e.norm_map,hx]
    field_simp
  have huv : inner ℝ u v=0 := by
    dsimp [v]
    rw [inner_smul_right,real_inner_comm,he,mul_zero]
  have hform (s : ℝ) : latitudeMap u e s x = s • u+Real.sqrt (1-s^2) • v := by
    unfold latitudeMap v
    rw [Real.sqrt_mul (by positivity),smul_smul]
    congr 1
    rw [mul_comm]
  have hdiff : latitudeMap u e q x-latitudeMap u e r x =
      (q-r) • u+(Real.sqrt (1-q^2)-Real.sqrt (1-r^2)) • v := by
    rw [hform q,hform r]
    module
  have hnorm : ‖latitudeMap u e q x-latitudeMap u e r x‖^2 =
      ((n+1 : ℕ) : ℝ)*((q-r)^2+(Real.sqrt (1-q^2)-Real.sqrt (1-r^2))^2) := by
    rw [hdiff,norm_add_sq_real,inner_smul_left,inner_smul_right,huv]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu,hv]
    ring
  have hh := mul_le_mul_of_nonneg_left (latitude_scalar_chord_bound hq hr)
    (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)
  have hb : ‖latitudeMap u e q x-latitudeMap u e r x‖^2 ≤
      (2*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt |q-r|)^2 := by
    rw [hnorm,mul_pow,mul_pow,Real.sq_sqrt (abs_nonneg _),Real.sq_sqrt (by positivity)]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

end TensorPCA.RetainedCountProofs.SphericalModel
