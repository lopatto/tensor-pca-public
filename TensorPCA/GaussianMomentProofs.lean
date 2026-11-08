-- SPDX-License-Identifier: Apache-2.0
-- Adapted from the immutable slowequilibration-palomar pin
-- a28aaa336343c4caf43791ababd8ed0ee5c7b58e:
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GaussianQuadratic.lean
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GaussianShell.lean
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SourceSphericalSharpMoments.lean
-- Only the Gaussian quadratic integral and Gaussian radius moment portions
-- are adapted; no dynamics or spherical-prior premise is imported.
module

public import TensorPCA.GaussianDensityProofs
public import TensorPCA.Geometry
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact Gaussian quadratic integrals and radius moments

The density theorem concerns canonical Mathlib stdGaussian. Differentiation of
its squared-radius MGF gives every even radius moment. These are
finite-dimensional prerequisites, not spherical ground-state limit assumptions.
-/
@[expose] public section
namespace TensorPCA.GaussianMomentProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integrable_quadratic_lebesgue {b : ℝ} (hb : 0 < b) (w : E) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2 + inner ℝ w x)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (b : ℂ)) (by simpa using hb) 1 w).re
  convert h using 1
  ext x
  simp only [one_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_add]
  exact (Complex.exp_ofReal_re _).symm

theorem integral_quadratic_lebesgue {b : ℝ} (hb : 0 < b) (w : E) :
    (∫ x : E, Real.exp (-b * ‖x‖ ^ 2 + inner ℝ w x)) =
      (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (‖w‖ ^ 2 / (4 * b)) := by
  rw [← Complex.ofReal_inj]
  calc
    _ = ∫ x : E, Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + 1 * inner ℝ w x) := by
      rw [← integral_complex_ofReal]
      congr 1
      ext x
      simp only [one_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.ofReal_exp]
    _ = _ := by
      rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]
      simp only [one_pow, one_mul]
      rw [← Complex.ofReal_div]
      have he : ((Module.finrank ℝ E : ℂ) / 2) = (((Module.finrank ℝ E : ℝ) / 2) : ℝ) := by push_cast; rfl
      rw [he, ← Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl

omit [MeasurableSpace E] [BorelSpace E] in

theorem weighted_density_eq (z : ℝ) (w x : E) :
    GaussianDensityProofs.density x * Real.exp (inner ℝ w x - (z - 1) / 2 * ‖x‖ ^ 2) =
      GaussianDensityProofs.normalizer E * Real.exp (-(z / 2) * ‖x‖ ^ 2 + inner ℝ w x) := by
  unfold GaussianDensityProofs.density
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrable_exp_quadratic {z : ℝ} (hz : 0 < z) (w : E) :
    Integrable (fun x => Real.exp (inner ℝ w x - (z - 1) / 2 * ‖x‖ ^ 2))
      (stdGaussian E) := by
  rw [GaussianDensityProofs.stdGaussian_eq_withDensity]
  apply (integrable_withDensity_iff_integrable_smul'
    GaussianDensityProofs.density_continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (GaussianDensityProofs.density_pos _).le,
    smul_eq_mul, weighted_density_eq] using
      (integrable_quadratic_lebesgue (by positivity : 0 < z / 2) w).const_mul
        (GaussianDensityProofs.normalizer E)

theorem integral_exp_quadratic {z : ℝ} (hz : 0 < z) (w : E) :
    (∫ x, Real.exp (inner ℝ w x - (z - 1) / 2 * ‖x‖ ^ 2) ∂stdGaussian E) =
      z ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (‖w‖ ^ 2 / (2 * z)) := by
  rw [GaussianDensityProofs.stdGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      GaussianDensityProofs.density_continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (GaussianDensityProofs.density_pos _).le,
    smul_eq_mul, weighted_density_eq]
  rw [integral_const_mul, integral_quadratic_lebesgue (by positivity : 0 < z / 2)]
  have harg : (4 : ℝ) * (z / 2) = 2 * z := by ring
  rw [harg, ← mul_assoc]
  congr 1
  unfold GaussianDensityProofs.normalizer
  rw [show Real.pi / (z / 2) = (2 * Real.pi) / z by field_simp,
    Real.div_rpow (by positivity) hz.le, Real.rpow_neg hz.le]
  field_simp

theorem integrable_exp_norm_sq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : E => Real.exp (t * ‖x‖ ^ 2)) (stdGaussian E) := by
  have h := integrable_exp_quadratic (by linarith : 0 < 1 - 2 * t) (0 : E)
  convert h using 1
  ext x
  simp only [inner_zero_left]
  congr 1
  ring

theorem integral_exp_norm_sq {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : E, Real.exp (t * ‖x‖ ^ 2) ∂stdGaussian E) =
      (1 - 2 * t) ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  have h := integral_exp_quadratic (by linarith : 0 < 1 - 2 * t) (0 : E)
  simp only [inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Real.exp_zero, mul_one] at h
  convert h using 1
  congr 1
  ext x
  congr 1
  ring


/-- Exact rising-product normalization of the even Gaussian radius moment. -/
def radialMomentProduct (m k : ℕ) : ℝ := ∏ j ∈ Finset.range k, ((m+2*j:ℕ):ℝ)

private theorem radialMomentProduct_succ (m k : ℕ) :
    radialMomentProduct m (k+1)=radialMomentProduct m k*((m+2*k:ℕ):ℝ) := by
  exact Finset.prod_range_succ _ _

private theorem iteratedDeriv_radius_mgf {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) {t : ℝ} (ht : t < 1/2) :
    iteratedDeriv k (mgf (fun g : E => ‖g‖^2) (stdGaussian E)) t =
      radialMomentProduct (Module.finrank ℝ E) k *
        (1-2*t)^(-((Module.finrank ℝ E:ℝ)/2)-(k:ℝ)) := by
  induction k generalizing t with
  | zero => simp [mgf,radialMomentProduct,integral_exp_norm_sq ht]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (mgf (fun g : E => ‖g‖^2) (stdGaussian E)) =ᶠ[𝓝 t]
        (fun t : ℝ => radialMomentProduct (Module.finrank ℝ E) k *
          (1-2*t)^(-((Module.finrank ℝ E:ℝ)/2)-(k:ℝ))) := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      exact ih hu
    rw [heq.deriv_eq]
    have hbase : 0 < 1-2*t := by linarith
    have hd := (((hasDerivAt_const t (1:ℝ)).sub
      ((hasDerivAt_id t).const_mul 2)).rpow_const
        (p := -((Module.finrank ℝ E:ℝ)/2)-(k:ℝ))
        (Or.inl hbase.ne')).const_mul (radialMomentProduct (Module.finrank ℝ E) k)
    simp only [Pi.sub_apply,id_eq,mul_one,zero_sub] at hd
    rw [hd.deriv,radialMomentProduct_succ]
    push_cast
    rw [show -((Module.finrank ℝ E:ℝ)/2)-((k:ℝ)+1) =
      -((Module.finrank ℝ E:ℝ)/2)-(k:ℝ)-1 by ring]
    ring

/-- Exact even Gaussian radius moments, valid in every finite dimension. -/
theorem gaussian_radius_even_moment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) :
    (∫ g : E, ‖g‖^(2*k) ∂stdGaussian E)=radialMomentProduct (Module.finrank ℝ E) k := by
  have hmem : (0:ℝ) ∈ interior (integrableExpSet (fun g : E => ‖g‖^2) (stdGaussian E)) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
    intro t ht
    exact integrable_exp_norm_sq ht
  have hh := iteratedDeriv_mgf_zero hmem k
  rw [iteratedDeriv_radius_mgf k (by norm_num)] at hh
  simpa only [mul_zero,sub_zero,Real.one_rpow,mul_one,Pi.pow_apply,←pow_mul] using hh.symm


end

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology BigOperators

/-- Every even normalized Gaussian radius moment is an explicit finite product. -/
theorem normalized_radius_even_moment {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (∫ g : Model.Vector N, (‖g‖/Real.sqrt N)^(2*r) ∂stdGaussian (Model.Vector N)) =
      ∏ j ∈ Finset.range r, (1+2*(j : ℝ)/(N : ℝ)) := by
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hpow : (Real.sqrt (N : ℝ))^(2*r) = (N : ℝ)^r := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp_rw [div_pow]
  rw [integral_div, gaussian_radius_even_moment, finrank_euclideanSpace, Fintype.card_fin, hpow]
  calc
    _ = ∏ j ∈ Finset.range r, (((N+2*j : ℕ) : ℝ)/(N : ℝ)) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      push_cast
      field_simp [hNz]

/-- Fixed-order normalized Gaussian radius moments tend to one as the actual
positive ambient dimension tends to infinity. -/
theorem normalized_radius_even_moment_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦ ∫ g : Model.Vector (n+1),
      (‖g‖/Real.sqrt (n+1 : ℕ))^(2*r) ∂stdGaussian (Model.Vector (n+1))) atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht (j : ℕ) : Tendsto (fun n : ℕ ↦ 1+2*(j : ℝ)/((n+1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add
        (hd.const_div_atTop (2*(j : ℝ)))
  have heq : (fun n : ℕ ↦ ∫ g : Model.Vector (n+1),
      (‖g‖/Real.sqrt (n+1 : ℕ))^(2*r) ∂stdGaussian (Model.Vector (n+1))) =
      (fun n : ℕ ↦ ∏ j ∈ Finset.range r, (1+2*(j : ℝ)/((n+1 : ℕ) : ℝ))) := by
    funext n
    exact normalized_radius_even_moment (Nat.succ_pos n) r
  rw [heq]
  have hp := tendsto_finsetProd
    (f := fun (j : ℕ) (n : ℕ) ↦ 1+2*(j : ℝ)/((n+1 : ℕ) : ℝ))
    (a := fun _ : ℕ ↦ (1 : ℝ)) (Finset.range r) (fun j _ ↦ ht j)
  simpa only [Finset.prod_const_one] using hp

/-- All normalized even radius powers are integrable, including degree zero. -/
theorem normalized_radius_even_integrable (N r : ℕ) :
    Integrable (fun g : Model.Vector N ↦ (‖g‖/Real.sqrt N)^(2*r))
      (stdGaussian (Model.Vector N)) := by
  have h := (IsGaussian.memLp_id (stdGaussian (Model.Vector N)) (2*r : ℕ)
    (ENNReal.natCast_ne_top (2*r))).integrable_norm_pow'
  simpa only [id_eq, div_pow] using h.div_const ((Real.sqrt (N : ℝ))^(2*r))

private theorem even_power_centered_sq (a : ℝ) (r : ℕ) :
    (a^(2*r)-1)^2 = a^(2*(2*r))-2*a^(2*r)+1 := by
  have he : a^(2*(2*r)) = (a^(2*r))^2 := by rw [Nat.mul_comm 2 (2*r), pow_mul]
  rw [he]
  ring

/-- The polynomial majorant used in radial tensor coupling is integrable. -/
theorem normalized_radius_power_centered_sq_integrable (N r : ℕ) :
    Integrable (fun g : Model.Vector N ↦ ((‖g‖/Real.sqrt N)^(2*r)-1)^2)
      (stdGaussian (Model.Vector N)) := by
  have hmul : Integrable (fun g : Model.Vector N ↦ 2*(‖g‖/Real.sqrt N)^(2*r))
      (stdGaussian (Model.Vector N)) := (normalized_radius_even_integrable N r).const_mul 2
  have hdiff : Integrable (fun g : Model.Vector N ↦ (‖g‖/Real.sqrt N)^(2*(2*r))-
      2*(‖g‖/Real.sqrt N)^(2*r)) (stdGaussian (Model.Vector N)) :=
    (normalized_radius_even_integrable N (2*r)).sub hmul
  have hexp : Integrable (fun g : Model.Vector N ↦ (‖g‖/Real.sqrt N)^(2*(2*r))-
      2*(‖g‖/Real.sqrt N)^(2*r)+1) (stdGaussian (Model.Vector N)) :=
    hdiff.add (integrable_const 1)
  apply hexp.congr
  filter_upwards [] with g
  exact (even_power_centered_sq _ r).symm

/-- The centered even-power squared error is evaluated by two actual even
radius moments, with all integral linearity hypotheses proved. -/
theorem integral_normalized_radius_power_centered_sq (N r : ℕ) :
    (∫ g : Model.Vector N, ((‖g‖/Real.sqrt N)^(2*r)-1)^2 ∂stdGaussian (Model.Vector N)) =
      (∫ g : Model.Vector N, (‖g‖/Real.sqrt N)^(2*(2*r)) ∂stdGaussian (Model.Vector N)) -
      2*(∫ g : Model.Vector N, (‖g‖/Real.sqrt N)^(2*r) ∂stdGaussian (Model.Vector N)) +1 := by
  have hmul : Integrable (fun g : Model.Vector N ↦ 2*(‖g‖/Real.sqrt N)^(2*r))
      (stdGaussian (Model.Vector N)) := (normalized_radius_even_integrable N r).const_mul 2
  have hdiff : Integrable (fun g : Model.Vector N ↦ (‖g‖/Real.sqrt N)^(2*(2*r))-
      2*(‖g‖/Real.sqrt N)^(2*r)) (stdGaussian (Model.Vector N)) :=
    (normalized_radius_even_integrable N (2*r)).sub hmul
  calc
    _ = ∫ g : Model.Vector N, (‖g‖/Real.sqrt N)^(2*(2*r))-
        2*(‖g‖/Real.sqrt N)^(2*r)+1 ∂stdGaussian (Model.Vector N) := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact even_power_centered_sq _ r
    _ = _ := by
      rw [integral_add hdiff (integrable_const 1),
        integral_sub (normalized_radius_even_integrable N (2*r)) hmul, integral_const_mul]
      simp

/-- Every fixed normalized even-radius power approaches one in L2, expressed
as the actual expectation under each dimension's canonical Gaussian law. -/
theorem normalized_radius_power_centered_sq_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ ↦ ∫ g : Model.Vector (n+1),
      ((‖g‖/Real.sqrt (n+1 : ℕ))^(2*r)-1)^2 ∂stdGaussian (Model.Vector (n+1))) atTop (𝓝 0) := by
  simp_rw [integral_normalized_radius_power_centered_sq]
  have h := ((normalized_radius_even_moment_tendsto (2*r)).sub
    ((normalized_radius_even_moment_tendsto r).const_mul 2)).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  convert h using 1
  norm_num

/-- The actual spherical/Gaussian tensor error is bounded by an even-radius
polynomial. No independence between radius and angle is required. -/
theorem tensor_radial_error_bound {N : ℕ} (hN : 0 < N) (k : ℕ)
    (g : Model.Vector N) (hg : g ≠ 0) :
    ‖Model.feature k ((Real.sqrt N)⁻¹ • g)-Model.feature k (Model.normalize g)‖^2 ≤
      ((‖g‖/Real.sqrt N)^(2*k)-1)^2 := by
  have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have hscale : (Real.sqrt N)⁻¹ • g = (‖g‖/Real.sqrt N) • Model.normalize g := by
    unfold Model.normalize
    rw [smul_smul]
    congr 1
    field_simp [hn, hs]
  have hfn : ‖Model.feature k (Model.normalize g)‖ = 1 :=
    Geometry.feature_unit_norm _ (Model.norm_normalize g hg)
  have hdiff : Model.feature k ((Real.sqrt N)⁻¹ • g)-Model.feature k (Model.normalize g) =
      ((‖g‖/Real.sqrt N)^k-1) • Model.feature k (Model.normalize g) := by
    rw [hscale, Geometry.feature_smul, sub_smul, one_smul]
  rw [hdiff, norm_smul, Real.norm_eq_abs, hfn, mul_one, sq_abs]
  have hb : 0 ≤ (‖g‖/Real.sqrt N)^k :=
    pow_nonneg (div_nonneg (norm_nonneg g) (Real.sqrt_nonneg _)) k
  have hh : 0 ≤ ((‖g‖/Real.sqrt N)^k-1)^2*(‖g‖/Real.sqrt N)^k*((‖g‖/Real.sqrt N)^k+2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hb) (by linarith)
  have hp : (‖g‖/Real.sqrt N)^(2*k) = ((‖g‖/Real.sqrt N)^k)^2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  rw [hp]
  nlinarith [hh]

/-- The actual squared tensor coupling error is integrable in every positive
ambient dimension. -/
theorem tensor_radial_error_integrable {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Integrable (fun g : Model.Vector N ↦
      ‖Model.feature k ((Real.sqrt N)⁻¹ • g)-Model.feature k (Model.normalize g)‖^2)
      (stdGaussian (Model.Vector N)) := by
  have hA : Measurable (fun g : Model.Vector N ↦ Model.feature k ((Real.sqrt N)⁻¹ • g)) :=
    (Model.continuous_feature N k).measurable.comp (continuous_const_smul ((Real.sqrt N)⁻¹)).measurable
  have hB : Measurable (fun g : Model.Vector N ↦ Model.feature k (Model.normalize g)) :=
    (Model.continuous_feature N k).measurable.comp (Model.measurable_normalize N)
  have hF : AEStronglyMeasurable (fun g : Model.Vector N ↦
      ‖Model.feature k ((Real.sqrt N)⁻¹ • g)-Model.feature k (Model.normalize g)‖^2)
      (stdGaussian (Model.Vector N)) :=
    ((continuous_norm.measurable.comp (hA.sub hB)).pow_const 2).aestronglyMeasurable
  apply (normalized_radius_power_centered_sq_integrable N k).mono' hF
  filter_upwards [Geometry.gaussian_ne_zero_ae hN] with g hg
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact tensor_radial_error_bound hN k g hg

/-- Unit spherical features and Gaussian features scaled by 1/sqrt(N) admit
the explicit common-Gaussian coupling whose expected squared tensor error tends
to zero. This is the L2 coupling prerequisite, not a free-energy transfer theorem. -/
theorem tensor_radial_error_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ ↦ ∫ g : Model.Vector (n+1),
      ‖Model.feature k ((Real.sqrt (n+1 : ℕ))⁻¹ • g)-Model.feature k (Model.normalize g)‖^2
        ∂stdGaussian (Model.Vector (n+1))) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) _
    (normalized_radius_power_centered_sq_tendsto k)
  intro n
  apply integral_mono_ae (tensor_radial_error_integrable (Nat.succ_pos n) k)
    (normalized_radius_power_centered_sq_integrable (n+1) k)
  exact (Geometry.gaussian_ne_zero_ae (Nat.succ_pos n)).mono
    (fun g hg ↦ tensor_radial_error_bound (Nat.succ_pos n) k g hg)

/-- Exact Frobenius norm scaling for the actual Gaussian-prior feature. -/
theorem scaled_gaussian_feature_norm_sq (N k : ℕ) (g : Model.Vector N) :
    ‖Model.feature k ((Real.sqrt N)⁻¹ • g)‖^2 = (‖g‖/Real.sqrt N)^(2*k) := by
  rw [Geometry.feature_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [show (Real.sqrt N)⁻¹ * ‖g‖ = ‖g‖/Real.sqrt N by ring, ← pow_mul, Nat.mul_comm k 2]

/-- The actual Gaussian-prior tensor second moment approaches the unit
spherical feature second moment. -/
theorem gaussian_feature_second_moment_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ ↦ ∫ g : Model.Vector (n+1),
      ‖Model.feature k ((Real.sqrt (n+1 : ℕ))⁻¹ • g)‖^2
        ∂stdGaussian (Model.Vector (n+1))) atTop (𝓝 1) := by
  simpa only [scaled_gaussian_feature_norm_sq] using normalized_radius_even_moment_tendsto k

end
end TensorPCA.GaussianMomentProofs
