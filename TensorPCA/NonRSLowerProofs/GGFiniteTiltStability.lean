-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteEmpiricalNormalizer

/-! Bounded-score exponential and normalized-tilt stability in the L1 norm of an
arbitrary spin probability.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteTiltStability
open MeasureTheory ProbabilityTheory Set Filter
open GGFiniteEmpiricalNormalizer
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem exp_lipschitz_bounded {M x y : ℝ} (hx : |x|≤M) (hy : |y|≤M) (t : ℝ) :
    |Real.exp (t*x)-Real.exp (t*y)|≤(|t| *Real.exp (|t| *M))*|x-y| := by
  let f : ℝ → ℝ := fun z ↦ Real.exp (t*z)
  have hd (z : ℝ) : HasDerivAt f (t*Real.exp (t*z)) z := by
    simpa only [f,mul_one,mul_comm,id_eq] using (((hasDerivAt_id z).const_mul t).exp)
  have hb (z : ℝ) (hz : z ∈ Icc (-M) M) : ‖deriv f z‖≤|t| *Real.exp (|t| *M) := by
    rw [(hd z).deriv,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg t)
    calc
      t*z ≤ |t*z| := le_abs_self _
      _ = |t| *|z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_le.mpr hz) (abs_nonneg t)
  have H := Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ ↦ (hd z).differentiableAt)
    hb (convex_Icc (-M) M) (abs_le.mp hy) (abs_le.mp hx)
  simpa only [f,Real.norm_eq_abs] using H

theorem exp_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V → ℝ} (hF : Measurable F) {M : ℝ} (hb : ∀ z, |F z|≤M) (t : ℝ) :
    Integrable (fun z ↦ Real.exp (t*F z)) nu := by
  apply Integrable.of_bound (hF.const_mul t).exp.aestronglyMeasurable (Real.exp (|t| *M))
  exact Eventually.of_forall (fun z ↦ by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (exp_score_bounds hb t z).2)

theorem weighted_exp_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F G b : V → ℝ} (hF : Measurable F) (hG : Measurable G) (hbM : Measurable b)
    {M : ℝ} (hFb : ∀ z, |F z|≤M) (hGb : ∀ z, |G z|≤M) (hbb : ∀ z, |b z|≤1) (t : ℝ) :
    |(∫ z, b z*Real.exp (t*F z) ∂nu)-(∫ z, b z*Real.exp (t*G z) ∂nu)|≤
      (|t| *Real.exp (|t| *M))*(∫ z, |F z-G z| ∂nu) := by
  have hIF := (exp_integrable nu hF hFb t).bdd_mul hbM.aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hbb z))
  have hIG := (exp_integrable nu hG hGb t).bdd_mul hbM.aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hbb z))
  have hFi : Integrable F nu := Integrable.of_bound hF.aestronglyMeasurable M
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hFb z))
  have hGi : Integrable G nu := Integrable.of_bound hG.aestronglyMeasurable M
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hGb z))
  rw [← integral_sub hIF hIG]
  calc
    _ ≤ ∫ z, |b z*Real.exp (t*F z)-b z*Real.exp (t*G z)| ∂nu := abs_integral_le_integral_abs
    _ ≤ ∫ z, (|t| *Real.exp (|t| *M))*|F z-G z| ∂nu := by
      apply integral_mono (hIF.sub hIG).norm ((hFi.sub hGi).norm.const_mul _)
      intro z
      change |b z*Real.exp (t*F z)-b z*Real.exp (t*G z)|≤_
      rw [← mul_sub,abs_mul]
      exact (mul_le_mul_of_nonneg_right (hbb z) (abs_nonneg _)).trans
        (by simpa only [one_mul,Real.norm_eq_abs,Pi.sub_apply] using exp_lipschitz_bounded (hFb z) (hGb z) t)
    _ = _ := integral_const_mul _ _

theorem normalizer_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F G : V → ℝ} (hF : Measurable F) (hG : Measurable G)
    {M : ℝ} (hFb : ∀ z, |F z|≤M) (hGb : ∀ z, |G z|≤M) (t : ℝ) :
    |normalizer nu F t-normalizer nu G t|≤
      (|t| *Real.exp (|t| *M))*(∫ z, |F z-G z| ∂nu) := by
  simpa only [normalizer,one_mul] using weighted_exp_sub_le nu hF hG
    (b := fun _ ↦ 1) measurable_const hFb hGb (fun _ ↦ by norm_num) t

private theorem ratio_difference_le {a b x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hb0 : 0≤b) (hby : b≤y) :
    |a/x-b/y|≤(|a-b|+|x-y|)/x := by
  have hf0 : 0≤b/y := div_nonneg hb0 hy.le
  have hf1 : b/y≤1 := (div_le_one hy).mpr hby
  have he : a/x-b/y=(a-b)/x+(b/y)*((y-x)/x) := by field_simp [hx.ne',hy.ne']; ring
  rw [he]
  have h1 : |(a-b)/x|=|a-b|/x := by rw [abs_div,abs_of_pos hx]
  have h2 : |(b/y)*((y-x)/x)|≤|x-y|/x := by
    rw [abs_mul,abs_of_nonneg hf0,abs_div,abs_of_pos hx,abs_sub_comm y x]
    exact (mul_le_mul_of_nonneg_right hf1 (div_nonneg (abs_nonneg _) hx.le)).trans_eq (one_mul _)
  exact (abs_add_le _ _).trans ((add_le_add h1.le h2).trans_eq (by ring))

theorem normalized_mean_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F G b : V → ℝ} (hF : Measurable F) (hG : Measurable G) (hbM : Measurable b)
    {M : ℝ} (hFb : ∀ z, |F z|≤M) (hGb : ∀ z, |G z|≤M)
    (hb0 : ∀ z, 0≤b z) (hb1 : ∀ z, b z≤1) (t : ℝ) :
    |(∫ z, b z*Real.exp (t*F z) ∂nu)/normalizer nu F t-
      (∫ z, b z*Real.exp (t*G z) ∂nu)/normalizer nu G t|≤
      (2*|t| *Real.exp (2*|t| *M))*(∫ z, |F z-G z| ∂nu) := by
  let E := ∫ z, |F z-G z| ∂nu
  let K := |t| *Real.exp (|t| *M)
  have hE : 0≤E := integral_nonneg (fun z ↦ abs_nonneg _)
  have hK : 0≤K := mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have hbabs (z : V) : |b z|≤1 := by rw [abs_of_nonneg (hb0 z)]; exact hb1 z
  have hZF := normalizer_mem_Icc nu hF hFb t
  have hZG := normalizer_mem_Icc nu hG hGb t
  have hzF : 0<normalizer nu F t := (Real.exp_pos _).trans_le hZF.1
  have hzG : 0<normalizer nu G t := (Real.exp_pos _).trans_le hZG.1
  have hIG := (exp_integrable nu hG hGb t).bdd_mul hbM.aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hbabs z))
  have hN0 : 0≤∫ z, b z*Real.exp (t*G z) ∂nu := integral_nonneg (fun z ↦ mul_nonneg (hb0 z) (Real.exp_nonneg _))
  have hNle : (∫ z, b z*Real.exp (t*G z) ∂nu)≤normalizer nu G t := by
    exact integral_mono hIG (exp_integrable nu hG hGb t) (fun z ↦
      (mul_le_mul_of_nonneg_right (hb1 z) (Real.exp_nonneg _)).trans_eq (one_mul _))
  have hN := weighted_exp_sub_le nu hF hG hbM hFb hGb hbabs t
  have hZ := normalizer_sub_le nu hF hG hFb hGb t
  have hs : |(∫ z, b z*Real.exp (t*F z) ∂nu)-(∫ z, b z*Real.exp (t*G z) ∂nu)|+
      |normalizer nu F t-normalizer nu G t|≤2*K*E := by
    change _≤2*(|t| *Real.exp (|t| *M))*(∫ z, |F z-G z| ∂nu)
    linarith
  have hnum : 0≤2*K*E := mul_nonneg (mul_nonneg (by norm_num) hK) hE
  calc
    _ ≤ (|(∫ z, b z*Real.exp (t*F z) ∂nu)-(∫ z, b z*Real.exp (t*G z) ∂nu)|+
        |normalizer nu F t-normalizer nu G t|)/normalizer nu F t := ratio_difference_le hzF hzG hN0 hNle
    _ ≤ (2*K*E)/normalizer nu F t := div_le_div_of_nonneg_right hs hzF.le
    _ ≤ (2*K*E)/Real.exp (-|t| *M) := div_le_div_of_nonneg_left hnum (Real.exp_pos _) hZF.1
    _ = _ := by
      dsimp only [K,E]
      rw [show -|t| *M= -(|t| *M) by ring,Real.exp_neg,div_inv_eq_mul,
        show 2*|t| *M=|t| *M+|t| *M by ring,Real.exp_add]
      ring

private theorem exp_neg_power_inverse (a : ℝ) (k : ℕ) :
    1/(Real.exp (-a))^k=Real.exp ((k : ℝ)*a) := by
  rw [← Real.exp_nat_mul,one_div,← Real.exp_neg]
  congr 1
  ring

theorem inverse_normalizer_power_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V → ℝ} (hF : Measurable F) {M : ℝ} (hb : ∀ z, |F z|≤M) (t : ℝ) (k : ℕ) :
    1/(normalizer nu F t)^k≤Real.exp ((k : ℝ)*|t| *M) := by
  have hLow : Real.exp (-(|t| *M))≤normalizer nu F t := by
    simpa only [neg_mul] using (normalizer_mem_Icc nu hF hb t).1
  have hPow := pow_le_pow_left₀ (Real.exp_nonneg _) hLow k
  have H := one_div_le_one_div_of_le (pow_pos (Real.exp_pos _) k) hPow
  simpa only [exp_neg_power_inverse,mul_assoc] using H

theorem inverse_normalizer_power_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F G : V → ℝ} (hF : Measurable F) (hG : Measurable G)
    {M : ℝ} (hFb : ∀ z, |F z|≤M) (hGb : ∀ z, |G z|≤M) (t : ℝ) (k : ℕ) :
    |1/(normalizer nu F t)^k-1/(normalizer nu G t)^k|≤
      ((k : ℝ)*|t| *Real.exp (((k : ℝ)+2)*|t| *M))*(∫ z, |F z-G z| ∂nu) := by
  let a := Real.exp (-(|t| *M))
  have ha : 0<a := Real.exp_pos _
  have hLF : a≤normalizer nu F t := by simpa only [a,neg_mul] using (normalizer_mem_Icc nu hF hFb t).1
  have hLG : a≤normalizer nu G t := by simpa only [a,neg_mul] using (normalizer_mem_Icc nu hG hGb t).1
  have H := inverse_power_lipschitz ha hLF hLG k
  have hZ := normalizer_sub_le nu hF hG hFb hGb t
  calc
    _ ≤ ((k : ℝ)/a^(k+1))*|normalizer nu F t-normalizer nu G t| := H
    _ ≤ ((k : ℝ)/a^(k+1))*((|t| *Real.exp (|t| *M))*(∫ z, |F z-G z| ∂nu)) :=
      mul_le_mul_of_nonneg_left hZ (div_nonneg (Nat.cast_nonneg _) (pow_nonneg ha.le _))
    _ = _ := by
      have he : (k : ℝ)/a^(k+1)=(k : ℝ)*Real.exp (((k : ℝ)+1)*|t| *M) := by
        dsimp only [a]
        rw [div_eq_mul_one_div,exp_neg_power_inverse]
        push_cast
        congr 2
        ring
      rw [he,show ((k : ℝ)+2)*|t| *M=(((k : ℝ)+1)*|t| *M)+(|t| *M) by ring,Real.exp_add]
      ring

theorem root_density_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F G : V → ℝ} (hF : Measurable F) (hG : Measurable G)
    {M : ℝ} (hM : 0≤M) (hFb : ∀ z, |F z|≤M) (hGb : ∀ z, |G z|≤M)
    (k : ℕ) {H H' : ℝ} (hH : |H|≤(k : ℝ)*M) (hH' : |H'|≤(k : ℝ)*M) (t : ℝ) :
    |Real.exp (t*H)/(normalizer nu F t)^k-Real.exp (t*H')/(normalizer nu G t)^k|≤
      (|t| *Real.exp ((2*(k : ℝ)+2)*|t| *M))*(|H-H'|+(k : ℝ)*(∫ z, |F z-G z| ∂nu)) := by
  let E := ∫ z, |F z-G z| ∂nu
  let a := Real.exp (t*H)
  let b := Real.exp (t*H')
  let x := normalizer nu F t
  let y := normalizer nu G t
  have hx : 0<x := (Real.exp_pos _).trans_le (normalizer_mem_Icc nu hF hFb t).1
  have hy : 0<y := (Real.exp_pos _).trans_le (normalizer_mem_Icc nu hG hGb t).1
  have he : a/x^k-b/y^k=(a-b)*(1/x^k)+b*(1/x^k-1/y^k) := by ring
  have hExp := exp_lipschitz_bounded hH hH' t
  have hInv := inverse_normalizer_power_le nu hF hFb t k
  have hInvDiff := inverse_normalizer_power_sub_le nu hF hG hFb hGb t k
  have hb : b≤Real.exp ((k : ℝ)*|t| *M) := by
    apply Real.exp_le_exp.mpr
    calc
      t*H' ≤ |t*H'| := le_abs_self _
      _ = |t| *|H'| := abs_mul _ _
      _ ≤ |t| *((k : ℝ)*M) := mul_le_mul_of_nonneg_left hH' (abs_nonneg _)
      _ = _ := by ring
  have hA : |(a-b)*(1/x^k)|≤(|t| *Real.exp (2*(k : ℝ)*|t| *M))*|H-H'| := by
    rw [abs_mul,abs_of_nonneg (one_div_nonneg.mpr (pow_nonneg hx.le _))]
    calc
      _ ≤ ((|t| *Real.exp (|t| *((k : ℝ)*M)))*|H-H'|)*Real.exp ((k : ℝ)*|t| *M) :=
        mul_le_mul hExp hInv (one_div_nonneg.mpr (pow_nonneg hx.le _)) (by positivity)
      _ = _ := by rw [show 2*(k : ℝ)*|t| *M=(|t| *((k : ℝ)*M))+((k : ℝ)*|t| *M) by ring,Real.exp_add]; ring
  have hB : |b*(1/x^k-1/y^k)|≤((k : ℝ)*|t| *Real.exp ((2*(k : ℝ)+2)*|t| *M))*E := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp ((k : ℝ)*|t| *M)*(((k : ℝ)*|t| *Real.exp (((k : ℝ)+2)*|t| *M))*E) :=
        mul_le_mul hb hInvDiff (abs_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [show (2*(k : ℝ)+2)*|t| *M=((k : ℝ)*|t| *M)+(((k : ℝ)+2)*|t| *M) by ring,Real.exp_add]; ring
  have hExpMono : Real.exp (2*(k : ℝ)*|t| *M)≤Real.exp ((2*(k : ℝ)+2)*|t| *M) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (abs_nonneg t) hM]
  change |a/x^k-b/y^k|≤_
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add
    (hA.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hExpMono (abs_nonneg t)) (abs_nonneg _))) hB).trans_eq (by ring))


end
end TensorPCA.NonRSLowerProofs.GGFiniteTiltStability
