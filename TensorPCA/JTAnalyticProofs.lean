-- SPDX-License-Identifier: Apache-2.0
-- Narrow attributed port of inverse-square-root calculus from immutable source
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/InverseSqrtCalculus.lean
-- Original Apache-2.0 proof block is preserved, with only the local namespace
-- and canonical project import added. This is not a ground-state duality theorem.
module

public import TensorPCA.Scalar
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace TensorPCA.JTAnalyticProofs

open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The inverse square root of a real function, using the actual real square root. -/
noncomputable def inverseSqrt (v : ℝ → ℝ) : ℝ → ℝ := fun r => (Real.sqrt (v r))⁻¹

/-- First derivative at a positive differentiability point. -/
theorem hasDerivAt_inverseSqrt {v : ℝ → ℝ} {r v' : ℝ}
    (hv : HasDerivAt v v' r) (hpos : 0 < v r) :
    HasDerivAt (inverseSqrt v) (-v' / (2*(Real.sqrt (v r))^3)) r := by
  have hspos := Real.sqrt_pos.2 hpos
  have h := (hv.sqrt hpos.ne').inv hspos.ne'
  unfold inverseSqrt
  convert h using 1
  field_simp [hspos.ne']

/-- Actual first derivative, rather than a derivative supplied as a field. -/
theorem deriv_inverseSqrt {v : ℝ → ℝ} {r : ℝ}
    (hv : DifferentiableAt ℝ v r) (hpos : 0 < v r) :
    deriv (inverseSqrt v) r = -(deriv v r) / (2*(Real.sqrt (v r))^3) :=
  (hasDerivAt_inverseSqrt hv.hasDerivAt hpos).deriv

/-- The second derivative formula on an open positive twice-differentiable
region. A neighborhood differentiability hypothesis makes the local first
formula legitimate; no preassigned second derivative identity is assumed. -/
theorem deriv2_inverseSqrt {v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hpos : ∀ r ∈ s, 0 < v r)
    (hv : ∀ r ∈ s, DifferentiableAt ℝ v r)
    {r : ℝ} (hr : r ∈ s) (hdv : DifferentiableAt ℝ (deriv v) r) :
    deriv (deriv (inverseSqrt v)) r =
      (3*(deriv v r)^2-2*v r*deriv (deriv v) r) /
        (4*(Real.sqrt (v r))^5) := by
  have hspos : 0 < Real.sqrt (v r) := Real.sqrt_pos.2 (hpos r hr)
  have hsne : Real.sqrt (v r) ≠ 0 := hspos.ne'
  have heq : deriv (inverseSqrt v) =ᶠ[nhds r]
      (fun x => -(deriv v x)/(2*(Real.sqrt (v x))^3)) := by
    filter_upwards [hs.mem_nhds hr] with x hx
    exact deriv_inverseSqrt (hv x hx) (hpos x hx)
  rw [heq.deriv_eq]
  have hsqrt := ((hv r hr).hasDerivAt).sqrt (hpos r hr).ne'
  have hden := (hsqrt.pow 3).const_mul (2:ℝ)
  have hd := (hdv.hasDerivAt.neg).div hden (by positivity : 2*(Real.sqrt (v r))^3 ≠ 0)
  have hvalue := hd.deriv
  change deriv (fun x => -(deriv v x)/(2*(Real.sqrt (v x))^3)) r = _ at hvalue
  rw [hvalue]
  have hsq := Real.sq_sqrt (hpos r hr).le
  dsimp
  have hnum : 3*(deriv v r)^2-2*v r*deriv (deriv v) r =
      3*(deriv v r)^2-2*(Real.sqrt (v r))^2*deriv (deriv v) r := by rw [hsq]
  rw [hnum]
  field_simp [hsne]
  norm_num
  ring

/-- Strict positivity of the ordinary second derivative follows from strict
positivity of its classical numerator. -/
theorem deriv2_inverseSqrt_pos {v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hpos : ∀ r ∈ s, 0 < v r)
    (hv : ∀ r ∈ s, DifferentiableAt ℝ v r)
    {r : ℝ} (hr : r ∈ s) (hdv : DifferentiableAt ℝ (deriv v) r)
    (hcurv : 0 < 3*(deriv v r)^2-2*v r*deriv (deriv v) r) :
    0 < deriv (deriv (inverseSqrt v)) r := by
  rw [deriv2_inverseSqrt hs hpos hv hr hdv]
  have hsqrtpos := Real.sqrt_pos.2 (hpos r hr)
  exact div_pos hcurv (by positivity)

/-- Strict convexity on a convex region, including its boundary, when the
positive curvature formula holds in its interior. -/
theorem strictConvexOn_inverseSqrt {v : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hc : ContinuousOn v s) (hp : ∀ r ∈ s, 0 < v r)
    (hv : ∀ r ∈ interior s, DifferentiableAt ℝ v r)
    (hdv : ∀ r ∈ interior s, DifferentiableAt ℝ (deriv v) r)
    (hcurv : ∀ r ∈ interior s,
      0 < 3*(deriv v r)^2-2*v r*deriv (deriv v) r) :
    StrictConvexOn ℝ s (inverseSqrt v) := by
  apply strictConvexOn_of_deriv2_pos hs
  · exact (hc.sqrt).inv₀ (fun r hr => (Real.sqrt_pos.2 (hp r hr)).ne')
  · intro r hr
    simpa [Function.iterate_succ_apply] using deriv2_inverseSqrt_pos isOpen_interior
      (fun r hr => hp r (interior_subset hr)) hv hr (hdv r hr) (hcurv r hr)

/-- The initial slope is a right derivative. Nonincreasing profiles have
nonpositive slope in this convention; a nonzero slope is strictly negative. -/
theorem admissibleProfile_rightSlope_nonpos {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p) :
    derivWithin p (Icc (0 : ℝ) 1) 0 ≤ 0 := hp.2.1.derivWithin_nonpos

theorem admissibleProfile_rightSlope_neg {p : ℝ → ℝ} (hp : Scalar.AdmissibleProfile p)
    (hne : derivWithin p (Icc (0 : ℝ) 1) 0 ≠ 0) :
    derivWithin p (Icc (0 : ℝ) 1) 0 < 0 :=
  lt_of_le_of_ne (admissibleProfile_rightSlope_nonpos hp) hne

theorem fourParameter_zero_overlap (delta a b t : ℝ) (ht : 0 ≤ t) :
    Scalar.fourParameterProfile delta a b 0 t = delta+(a+b)*(1-t) := by
  rw [Scalar.fourParameterProfile,max_eq_left ht]
  ring

theorem fourParameter_initial_derivative_of_pos (delta a b : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (Scalar.fourParameterProfile delta a b q) (-a) 0 := by
  have hd : HasDerivAt (fun t : ℝ => delta+a*(1-t)+b*(1-q)) (-a) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => 1-t) (-1) 0 := (hasDerivAt_id (0 : ℝ)).const_sub 1
    convert (((hlin.const_mul a).const_add delta).add_const (b*(1-q))) using 1
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hq] with t ht
  simp only [Scalar.fourParameterProfile,max_eq_right ht.le]

/-- At q=0 the two downward-slope coefficients merge; omitting b here would
misidentify the atom at zero in the degenerate parameterization. -/
theorem fourParameter_initial_derivative_at_zero (delta a b : ℝ) :
    HasDerivWithinAt (Scalar.fourParameterProfile delta a b 0) (-(a+b)) (Ici 0) 0 := by
  have hd : HasDerivAt (fun t : ℝ => delta+(a+b)*(1-t)) (-(a+b)) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => 1-t) (-1) 0 := (hasDerivAt_id (0 : ℝ)).const_sub 1
    convert ((hlin.const_mul (a+b)).const_add delta) using 1
    ring
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem ?_ (by norm_num)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fourParameter_zero_overlap delta a b t ht


end TensorPCA.JTAnalyticProofs
