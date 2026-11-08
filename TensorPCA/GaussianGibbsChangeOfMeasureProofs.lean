-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianMomentProofs
public import TensorPCA.GaussianReplicaMomentProofs
public import TensorPCA.GaussianPosteriorProofs
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Dimension-free Gaussian moments of bounded Gibbs density ratios. -/
@[expose] public section
namespace TensorPCA.GaussianGibbsChangeOfMeasureProofs
open MeasureTheory ProbabilityTheory Set Real
open GaussianMomentProofs GaussianReplicaMomentProofs
open scoped RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def exponent (F : Omega → E) (b : Omega → ℝ) (W : E) (x : Omega) : ℝ := ⟪F x,W⟫+b x

def normalizer (q : Measure Omega) (F : Omega → E) (b : Omega → ℝ) (W : E) : ℝ :=
  ∫ x, Real.exp (exponent F b W x) ∂q

def gibbsDensity (q : Measure Omega) (F : Omega → E) (b : Omega → ℝ) (W : E) (x : Omega) : ℝ :=
  Real.exp (exponent F b W x)/normalizer q F b W

def tiltedLaw (q : Measure Omega) (F : Omega → E) (b : Omega → ℝ) (W : E) : Measure Omega :=
  q.withDensity (fun x ↦ ENNReal.ofReal (gibbsDensity q F b W x))

theorem exponent_measurable (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F)
    (hb : Measurable b) (W : E) : Measurable (exponent F b W) :=
  (continuous_inner.measurable.comp (hF.prodMk measurable_const)).add hb

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem exponent_norm_le (q : Measure Omega) (F : Omega → E) (b : Omega → ℝ)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    ∀ᵐ x ∂q, ‖exponent F b W x‖ ≤ C*‖W‖+B := by
  filter_upwards [hFB,hbB] with x hx hb
  change |⟪F x,W⟫+b x| ≤ _
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))) hb)

theorem exponent_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    Integrable (exponent F b W) q :=
  (integrable_const (C*‖W‖+B)).mono' (exponent_measurable F b hF hb W).aestronglyMeasurable
    (exponent_norm_le q F b hFB hbB W)

theorem weight_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    Integrable (fun x ↦ Real.exp (exponent F b W x)) q := by
  apply (integrable_const (Real.exp (C*‖W‖+B))).mono'
    (exponent_measurable F b hF hb W).exp.aestronglyMeasurable
  filter_upwards [exponent_norm_le q F b hFB hbB W] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (exponent F b W x)).trans (by simpa only [Real.norm_eq_abs] using hx)

theorem normalizer_pos (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    0 < normalizer q F b W := integral_exp_pos (weight_integrable q F b hF hb hFB hbB W)

theorem tiltedLaw_probability (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    IsProbabilityMeasure (tiltedLaw q F b W) := by
  have hz := normalizer_pos q F b hF hb hFB hbB W
  have hi := (weight_integrable q F b hF hb hFB hbB W).div_const (normalizer q F b W)
  constructor
  change (q.withDensity (fun x ↦ ENNReal.ofReal
    (Real.exp (exponent F b W x)/normalizer q F b W))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun x ↦ (div_pos (Real.exp_pos _) hz).le)),
    integral_div]
  change ENNReal.ofReal (normalizer q F b W/normalizer q F b W) = 1
  rw [div_self hz.ne', ENNReal.ofReal_one]

/-- Jensen is applied to the actual partition function, retaining its
original random linear mean instead of a dimension-dependent norm bound. -/
theorem normalizer_jensen_lower (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    Real.exp (⟪∫ x, F x ∂q,W⟫+(∫ x, b x ∂q)) ≤ normalizer q F b W := by
  have hiF := signal_integrable q F hF hFB
  have hib : Integrable b q := (integrable_const B).mono' hb.aestronglyMeasurable
    (hbB.mono (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx))
  have he : (∫ x, exponent F b W x ∂q) = ⟪∫ x, F x ∂q,W⟫+(∫ x, b x ∂q) := by
    change (∫ x, ⟪F x,W⟫+b x ∂q) = _
    rw [integral_add (hiF.inner_const W) hib]
    congr 1
    simpa only [real_inner_comm] using integral_inner hiF W
  have H := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ ↦ Set.mem_univ _))
    (exponent_integrable q F b hF hb hFB hbB W) (weight_integrable q F b hF hb hFB hbB W)
  rw [he] at H
  exact H

theorem density_le_exp_centered (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) (x : Omega) :
    gibbsDensity q F b W x ≤ Real.exp (⟪F x-(∫ y, F y ∂q),W⟫+b x-(∫ y, b y ∂q)) := by
  have hj := normalizer_jensen_lower q F b hF hb hFB hbB W
  have H := div_le_div_of_nonneg_left (Real.exp_pos (exponent F b W x)).le (Real.exp_pos _) hj
  change gibbsDensity q F b W x ≤ Real.exp (exponent F b W x)/
    Real.exp (⟪∫ y, F y ∂q,W⟫+(∫ y, b y ∂q)) at H
  apply H.trans_eq
  rw [← Real.exp_sub]
  congr 1
  unfold exponent
  rw [inner_sub_left]
  ring

theorem integrable_exp_inner_add (v : E) (c : ℝ) :
    Integrable (fun W ↦ Real.exp (⟪v,W⟫+c)) (stdGaussian E) := by
  have h := integrable_exp_quadratic (E := E) (z := 1) (by norm_num) v
  simp only [sub_self, zero_div, zero_mul, sub_zero] at h
  simpa only [Real.exp_add, mul_comm] using h.const_mul (Real.exp c)

theorem integral_exp_inner_add (v : E) (c : ℝ) :
    (∫ W, Real.exp (⟪v,W⟫+c) ∂stdGaussian E) = Real.exp (c+‖v‖^2/2) := by
  have h := integral_exp_quadratic (E := E) (z := 1) (by norm_num) v
  simp only [sub_self, zero_div, zero_mul, sub_zero, one_rpow, one_mul, mul_one] at h
  have he : (fun W ↦ Real.exp (⟪v,W⟫+c)) = (fun W ↦ Real.exp c*Real.exp ⟪v,W⟫) := by
    funext W
    rw [Real.exp_add, mul_comm]
  rw [he, integral_const_mul, h, ← Real.exp_add]

theorem measurable_normalizer (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b) :
    Measurable (normalizer q F b) := by
  have hm : StronglyMeasurable (fun p : E × Omega ↦ Real.exp (exponent F b p.1 p.2)) :=
    (((continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)).add
      (hb.comp measurable_snd)).exp).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := q)).measurable

theorem measurable_gibbsDensity (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b) :
    Measurable (fun p : E × Omega ↦ gibbsDensity q F b p.1 p.2) := by
  exact (((continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)).add
    (hb.comp measurable_snd)).exp).div ((measurable_normalizer q F b hF hb).comp measurable_fst)

theorem gibbsDensity_nonneg (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) (x : Omega) :
    0 ≤ gibbsDensity q F b W x :=
  (div_pos (Real.exp_pos _) (normalizer_pos q F b hF hb hFB hbB W)).le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mean_norm_le (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) {C : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) : ‖∫ x, F x ∂q‖ ≤ C := by
  have H := norm_integral_le_of_norm_le_const (μ := q) hFB
  simpa only [probReal_univ,mul_one] using H

theorem mean_bias_abs_le (q : Measure Omega) [IsProbabilityMeasure q]
    (b : Omega → ℝ) {B : ℝ} (hbB : ∀ᵐ x ∂q, |b x| ≤ B) : |∫ x, b x ∂q| ≤ B := by
  have H := norm_integral_le_of_norm_le_const (μ := q) (f := b)
    (hbB.mono (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx))
  simpa only [probReal_univ,mul_one,Real.norm_eq_abs] using H

theorem density_pow_le_exp_affine (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B)
    (r : ℕ) (W : E) (x : Omega) :
    (gibbsDensity q F b W x)^r ≤ Real.exp
      (⟪(r : ℝ) • (F x-(∫ y, F y ∂q)),W⟫+(r : ℝ)*(b x-(∫ y, b y ∂q))) := by
  have H := pow_le_pow_left₀ (gibbsDensity_nonneg q F b hF hb hFB hbB W x)
    (density_le_exp_centered q F b hF hb hFB hbB W x) r
  apply H.trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  simp only [inner_smul_left, conj_trivial]
  ring

theorem density_pow_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B)
    (r : ℕ) (x : Omega) :
    Integrable (fun W ↦ (gibbsDensity q F b W x)^r) (stdGaussian E) := by
  apply (integrable_exp_inner_add ((r : ℝ) • (F x-(∫ y, F y ∂q)))
    ((r : ℝ)*(b x-(∫ y, b y ∂q)))).mono'
    (((measurable_gibbsDensity q F b hF hb).comp (measurable_id.prodMk measurable_const)).pow_const r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun W ↦ by
    change ‖(gibbsDensity q F b W x)^r‖ ≤ _
    rw [Real.norm_of_nonneg (pow_nonneg (gibbsDensity_nonneg q F b hF hb hFB hbB W x) r)]
    exact density_pow_le_exp_affine q F b hF hb hFB hbB r W x)

/-- Genuine Gaussian moments of the actual normalized Gibbs density ratio.
The uniform estimate is asserted only on original-prior almost-everywhere
states, so null-state feature bounds are never added as hypotheses. -/
theorem density_pow_moment_le (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (r : ℕ) :
    ∀ᵐ x ∂q, (∫ W, (gibbsDensity q F b W x)^r ∂stdGaussian E) ≤
      Real.exp (2*(r : ℝ)*B+2*(r : ℝ)^2*C^2) := by
  have hmF := mean_norm_le q F hFB
  have hmb := mean_bias_abs_le q b hbB
  have hC : 0 ≤ C := (norm_nonneg _).trans hmF
  filter_upwards [hFB,hbB] with x hx hbx
  have hcenter : ‖F x-(∫ y, F y ∂q)‖ ≤ 2*C :=
    (norm_sub_le _ _).trans (by linarith)
  have hbias : b x-(∫ y, b y ∂q) ≤ 2*B := by
    linarith [le_abs_self (b x),neg_abs_le (∫ y, b y ∂q)]
  have hn : ‖(r : ℝ) • (F x-(∫ y, F y ∂q))‖ ≤ (r : ℝ)*(2*C) := by
    rw [norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg r)]
    exact mul_le_mul_of_nonneg_left hcenter (Nat.cast_nonneg r)
  have hnsq := mul_self_le_mul_self (norm_nonneg ((r : ℝ) • (F x-(∫ y, F y ∂q)))) hn
  have H := integral_mono_ae (density_pow_integrable q F b hF hb hFB hbB r x)
    (integrable_exp_inner_add ((r : ℝ) • (F x-(∫ y, F y ∂q))) ((r : ℝ)*(b x-(∫ y, b y ∂q))))
    (Filter.Eventually.of_forall (fun W ↦ density_pow_le_exp_affine q F b hF hb hFB hbB r W x))
  rw [integral_exp_inner_add] at H
  apply H.trans (Real.exp_le_exp.mpr ?_)
  have hbiasr := mul_le_mul_of_nonneg_left hbias (Nat.cast_nonneg r)
  nlinarith

def pairDensity (q : Measure Omega) (F : Omega → E) (b : Omega → ℝ) (W : E) (z : Omega × Omega) : ℝ :=
  gibbsDensity q F b W z.1*gibbsDensity q F b W z.2

theorem pairDensity_sq_le_exp_affine (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B)
    (W : E) (z : Omega × Omega) :
    (pairDensity q F b W z)^2 ≤ Real.exp
      (⟪(2 : ℝ) • ((F z.1-(∫ x, F x ∂q))+(F z.2-(∫ x, F x ∂q))),W⟫+
        2*((b z.1-(∫ x, b x ∂q))+(b z.2-(∫ x, b x ∂q)))) := by
  have hp := mul_le_mul (density_le_exp_centered q F b hF hb hFB hbB W z.1)
    (density_le_exp_centered q F b hF hb hFB hbB W z.2)
    (gibbsDensity_nonneg q F b hF hb hFB hbB W z.2) (Real.exp_pos _).le
  have H := pow_le_pow_left₀ (mul_nonneg (gibbsDensity_nonneg q F b hF hb hFB hbB W z.1)
    (gibbsDensity_nonneg q F b hF hb hFB hbB W z.2)) hp 2
  apply H.trans_eq
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  simp only [inner_smul_left, conj_trivial, inner_add_left, Nat.cast_ofNat]
  ring

theorem measurable_pairDensity (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b) :
    Measurable (fun p : (Omega × Omega) × E ↦ pairDensity q F b p.2 p.1) := by
  exact ((measurable_gibbsDensity q F b hF hb).comp
    (measurable_snd.prodMk measurable_fst.fst)).mul
      ((measurable_gibbsDensity q F b hF hb).comp (measurable_snd.prodMk measurable_fst.snd))

theorem pairDensity_sq_integrable_gaussian (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (z : Omega × Omega) :
    Integrable (fun W ↦ (pairDensity q F b W z)^2) (stdGaussian E) := by
  have hm : Measurable (fun W ↦ pairDensity q F b W z) :=
    (measurable_pairDensity q F b hF hb).comp (measurable_const.prodMk measurable_id)
  apply (integrable_exp_inner_add
    ((2 : ℝ) • ((F z.1-(∫ x, F x ∂q))+(F z.2-(∫ x, F x ∂q))))
    (2*((b z.1-(∫ x, b x ∂q))+(b z.2-(∫ x, b x ∂q))))).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun W ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pairDensity_sq_le_exp_affine q F b hF hb hFB hbB W z)

theorem pairDensity_sq_moment_le_of_bounds (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B)
    (z : Omega × Omega) (hz1 : ‖F z.1‖ ≤ C) (hz2 : ‖F z.2‖ ≤ C)
    (hb1 : |b z.1| ≤ B) (hb2 : |b z.2| ≤ B) :
    (∫ W, (pairDensity q F b W z)^2 ∂stdGaussian E) ≤ Real.exp (8*B+32*C^2) := by
  have hmF := mean_norm_le q F hFB
  have hmb := mean_bias_abs_le q b hbB
  have hcx : ‖F z.1-(∫ x, F x ∂q)‖ ≤ 2*C := (norm_sub_le _ _).trans (by linarith)
  have hcy : ‖F z.2-(∫ x, F x ∂q)‖ ≤ 2*C := (norm_sub_le _ _).trans (by linarith)
  have hv : ‖(2 : ℝ) • ((F z.1-(∫ x, F x ∂q))+(F z.2-(∫ x, F x ∂q)))‖ ≤ 8*C := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos zero_lt_two]
    have hh := norm_add_le (F z.1-(∫ x, F x ∂q)) (F z.2-(∫ x, F x ∂q))
    linarith
  have hvsq := mul_self_le_mul_self (norm_nonneg
    ((2 : ℝ) • ((F z.1-(∫ x, F x ∂q))+(F z.2-(∫ x, F x ∂q))))) hv
  have hbc : 2*((b z.1-(∫ x, b x ∂q))+(b z.2-(∫ x, b x ∂q))) ≤ 8*B := by
    linarith [le_abs_self (b z.1),le_abs_self (b z.2),neg_abs_le (∫ x, b x ∂q)]
  have H := integral_mono_ae (pairDensity_sq_integrable_gaussian q F b hF hb hFB hbB z)
    (integrable_exp_inner_add
      ((2 : ℝ) • ((F z.1-(∫ x, F x ∂q))+(F z.2-(∫ x, F x ∂q))))
      (2*((b z.1-(∫ x, b x ∂q))+(b z.2-(∫ x, b x ∂q)))))
    (Filter.Eventually.of_forall (fun W ↦ pairDensity_sq_le_exp_affine q F b hF hb hFB hbB W z))
  rw [integral_exp_inner_add] at H
  apply H.trans (Real.exp_le_exp.mpr ?_)
  nlinarith

/-- The pair-replica density second moment has a dimension-free Gaussian
bound, with all original-prior almost-everywhere bounds discharged. -/
theorem pairDensity_sq_moment_le (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) :
    ∀ᵐ z ∂q.prod q, (∫ W, (pairDensity q F b W z)^2 ∂stdGaussian E) ≤ Real.exp (8*B+32*C^2) := by
  have h1 : ∀ᵐ z : Omega × Omega ∂q.prod q, ‖F z.1‖ ≤ C := Measure.quasiMeasurePreserving_fst.ae hFB
  have h2 : ∀ᵐ z : Omega × Omega ∂q.prod q, ‖F z.2‖ ≤ C := Measure.quasiMeasurePreserving_snd.ae hFB
  have hb1 : ∀ᵐ z : Omega × Omega ∂q.prod q, |b z.1| ≤ B := Measure.quasiMeasurePreserving_fst.ae hbB
  have hb2 : ∀ᵐ z : Omega × Omega ∂q.prod q, |b z.2| ≤ B := Measure.quasiMeasurePreserving_snd.ae hbB
  filter_upwards [h1,h2,hb1,hb2] with z hz1 hz2 hzb1 hzb2
  exact pairDensity_sq_moment_le_of_bounds q F b hF hb hFB hbB z hz1 hz2 hzb1 hzb2

theorem pairDensity_sq_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) :
    Integrable (fun p : (Omega × Omega) × E ↦ (pairDensity q F b p.2 p.1)^2)
      ((q.prod q).prod (stdGaussian E)) := by
  have hm := ((measurable_pairDensity q F b hF hb).pow_const 2).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (pairDensity_sq_integrable_gaussian q F b hF hb hFB hbB), ?_⟩
  have hparam : AEStronglyMeasurable (fun z : Omega × Omega ↦
      ∫ W, ‖(pairDensity q F b W z)^2‖ ∂stdGaussian E) (q.prod q) :=
    (hm.norm.integral_prod_right' (ν := stdGaussian E)).aestronglyMeasurable
  apply (integrable_const (Real.exp (8*B+32*C^2))).mono' hparam
  filter_upwards [pairDensity_sq_moment_le q F b hF hb hFB hbB] with z hz
  rw [Real.norm_of_nonneg (integral_nonneg (fun W ↦ norm_nonneg _))]
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz

theorem pairDensity_memLp_two (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) :
    MemLp (fun p : (Omega × Omega) × E ↦ pairDensity q F b p.2 p.1) 2
      ((q.prod q).prod (stdGaussian E)) :=
  (memLp_two_iff_integrable_sq (measurable_pairDensity q F b hF hb).aestronglyMeasurable).mpr
    (pairDensity_sq_integrable q F b hF hb hFB hbB)

theorem integral_pairDensity_sq_le (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) :
    (∫ p : (Omega × Omega) × E, (pairDensity q F b p.2 p.1)^2
      ∂(q.prod q).prod (stdGaussian E)) ≤ Real.exp (8*B+32*C^2) := by
  have hi := pairDensity_sq_integrable q F b hF hb hFB hbB
  rw [integral_prod _ hi]
  have H := integral_mono_ae hi.integral_prod_left (integrable_const (Real.exp (8*B+32*C^2)))
    (pairDensity_sq_moment_le q F b hF hb hFB hbB)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem tiltedLaw_prod_eq_withDensity (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) :
    (tiltedLaw q F b W).prod (tiltedLaw q F b W) =
      (q.prod q).withDensity (fun z ↦ ENNReal.ofReal (pairDensity q F b W z)) := by
  have hm : Measurable (fun x ↦ ENNReal.ofReal (gibbsDensity q F b W x)) :=
    ((measurable_gibbsDensity q F b hF hb).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [tiltedLaw,prod_withDensity hm hm]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (gibbsDensity_nonneg q F b hF hb hFB hbB W z.1)]
  rfl

theorem integral_tiltedLaw_pair (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B) (W : E) (f : Omega × Omega → ℝ) :
    (∫ z, f z ∂(tiltedLaw q F b W).prod (tiltedLaw q F b W)) =
      ∫ z, pairDensity q F b W z*f z ∂q.prod q := by
  have hm : Measurable (fun z ↦ ENNReal.ofReal (pairDensity q F b W z)) :=
    ((measurable_pairDensity q F b hF hb).comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
  rw [tiltedLaw_prod_eq_withDensity q F b hF hb hFB hbB W,
    integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z ↦ by
    have hp : 0 ≤ pairDensity q F b W z := mul_nonneg
      (gibbsDensity_nonneg q F b hF hb hFB hbB W z.1) (gibbsDensity_nonneg q F b hF hb hFB hbB W z.2)
    change (ENNReal.ofReal (pairDensity q F b W z)).toReal • f z = pairDensity q F b W z*f z
    rw [ENNReal.toReal_ofReal hp,smul_eq_mul])

/-- Actual Gaussian-averaged Gibbs-pair change of measure. The factor is
dimension-free and is proved from Jensen and the exact Gaussian MGF,
without a density-moment hypothesis or coordinate independence premise. -/
theorem tilted_pair_observable_bound (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (b : Omega → ℝ) (hF : Measurable F) (hb : Measurable b)
    {C B : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ C) (hbB : ∀ᵐ x ∂q, |b x| ≤ B)
    (f : Omega × Omega → ℝ) (hf : MemLp f 2 (q.prod q)) :
    (∫ W, ∫ z, |f z| ∂(tiltedLaw q F b W).prod (tiltedLaw q F b W) ∂stdGaussian E) ≤
      Real.exp (4*B+16*C^2)*Real.sqrt (∫ z, (f z)^2 ∂q.prod q) := by
  have hR := pairDensity_memLp_two q F b hF hb hFB hbB
  have hfprod : MemLp (fun p : (Omega × Omega) × E ↦ |f p.1|) 2
      ((q.prod q).prod (stdGaussian E)) := by
    simpa only [Real.norm_eq_abs] using hf.norm.comp_fst (stdGaussian E)
  have hi := hR.integrable_mul hfprod
  have hpq : Real.HolderConjugate (2 : ℝ) 2 := by norm_num [Real.holderConjugate_iff]
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (q.prod q).prod (stdGaussian E)) hpq
    (f := fun p : (Omega × Omega) × E ↦ pairDensity q F b p.2 p.1)
    (g := fun p : (Omega × Omega) × E ↦ |f p.1|)
    (Filter.Eventually.of_forall (fun p ↦ mul_nonneg
      (gibbsDensity_nonneg q F b hF hb hFB hbB p.2 p.1.1)
      (gibbsDensity_nonneg q F b hF hb hFB hbB p.2 p.1.2)))
    (Filter.Eventually.of_forall (fun p ↦ abs_nonneg (f p.1)))
    (by simpa only [ENNReal.ofReal_ofNat] using hR)
    (by simpa only [ENNReal.ofReal_ofNat] using hfprod)
  simp only [Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] at H
  have hfint : (∫ p : (Omega × Omega) × E, (f p.1)^2 ∂(q.prod q).prod (stdGaussian E)) =
      ∫ z, (f z)^2 ∂q.prod q := by
    simpa only [probReal_univ,one_smul] using
      (integral_fun_fst (μ := q.prod q) (ν := stdGaussian E) (fun z ↦ (f z)^2))
  rw [hfint] at H
  have hroot : Real.sqrt (∫ p : (Omega × Omega) × E, (pairDensity q F b p.2 p.1)^2
      ∂(q.prod q).prod (stdGaussian E)) ≤ Real.exp (4*B+16*C^2) := by
    apply (Real.sqrt_le_sqrt (integral_pairDensity_sq_le q F b hF hb hFB hbB)).trans_eq
    have he : Real.exp (8*B+32*C^2) = (Real.exp (4*B+16*C^2))^2 := by
      calc
        _ = Real.exp ((4*B+16*C^2)+(4*B+16*C^2)) := by congr 1; ring
        _ = _ := by rw [Real.exp_add]; ring
    rw [he,Real.sqrt_sq (Real.exp_pos _).le]
  have he : (∫ W, ∫ z, |f z| ∂(tiltedLaw q F b W).prod (tiltedLaw q F b W) ∂stdGaussian E) =
      ∫ p : (Omega × Omega) × E, pairDensity q F b p.2 p.1*|f p.1|
        ∂(q.prod q).prod (stdGaussian E) := by
    simp_rw [integral_tiltedLaw_pair q F b hF hb hFB hbB]
    have hi' : Integrable (fun p : (Omega × Omega) × E ↦ pairDensity q F b p.2 p.1*|f p.1|)
        ((q.prod q).prod (stdGaussian E)) := by convert! hi using 1
    exact (integral_prod_symm (fun p : (Omega × Omega) × E ↦ pairDensity q F b p.2 p.1*|f p.1|) hi').symm
  rw [he]
  exact H.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))

/-- The exact normalized tilt used above is the actual Gaussian posterior
at a shifted observation when the deterministic bias includes the full
squared-signal penalty. No constant-norm simplification is made. -/
theorem tiltedLaw_eq_posteriorKernel (q : Measure Omega) [IsProbabilityMeasure q]
    (F : Omega → E) (hF : Measurable F) (shift W : E) :
    tiltedLaw q F (fun x ↦ ⟪F x,shift⟫-‖F x‖^2/2) W =
      GaussianPosteriorProofs.posteriorKernel q F (shift+W) := by
  rw [GaussianPosteriorProofs.posteriorKernel_apply q F hF]
  have he (x : Omega) : exponent F (fun x ↦ ⟪F x,shift⟫-‖F x‖^2/2) W x =
      ⟪F x,shift+W⟫-‖F x‖^2/2 := by
    unfold exponent
    rw [inner_add_right]
    ring
  have hz : normalizer q F (fun x ↦ ⟪F x,shift⟫-‖F x‖^2/2) W =
      GaussianPriorTransferProofs.mixtureLikelihood q F (shift+W) := by
    unfold normalizer GaussianPriorTransferProofs.mixtureLikelihood
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      change Real.exp (exponent F (fun x ↦ ⟪F x,shift⟫-‖F x‖^2/2) W x) =
        Real.exp (⟪F x,shift+W⟫-‖F x‖^2/2)
      rw [he])
  unfold tiltedLaw
  congr 1
  funext x
  change ENNReal.ofReal (Real.exp (exponent F (fun x ↦ ⟪F x,shift⟫-‖F x‖^2/2) W x)/
    normalizer q F (fun x ↦ ⟪F x,shift⟫-‖F x‖^2/2) W) =
      ENNReal.ofReal (GaussianPosteriorProofs.posteriorWeight q F (shift+W) x)
  rw [hz,he]
  congr 1
  unfold GaussianPosteriorProofs.posteriorWeight GaussianPriorTransferProofs.mixtureWeight
  ring

end
end TensorPCA.GaussianGibbsChangeOfMeasureProofs
