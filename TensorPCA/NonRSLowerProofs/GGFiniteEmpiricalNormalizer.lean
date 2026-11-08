-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Dimension-free empirical normalization under a finite iid product law. Anchors and
any eventual tilt numerator are held fixed. No directing representation or
structural GG/invariance theorem is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteEmpiricalNormalizer
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
noncomputable section
variable {V : Type*} [MeasurableSpace V]

def empiricalMean (m : ℕ) (Y : V → ℝ) (v : Fin m → V) : ℝ :=
  (∑ i : Fin m, Y (v i))/(m : ℝ)

theorem empiricalMean_measurable (m : ℕ) {Y : V → ℝ} (hY : Measurable Y) :
    Measurable (empiricalMean m Y) :=
  (Finset.measurable_sum _ (fun i _ ↦ hY.comp (measurable_pi_apply i))).div_const _

theorem empiricalMean_abs_le {m : ℕ} (hm : 0<m) {Y : V → ℝ} {b : ℝ}
    (hb : ∀ v, |Y v|≤b) (v : Fin m → V) : |empiricalMean m Y v|≤b := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  unfold empiricalMean
  rw [abs_div,abs_of_pos hmR,div_le_iff₀ hmR]
  calc
    _ ≤ ∑ i : Fin m, |Y (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum (fun i _ ↦ hb (v i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem empiricalMean_integral {m : ℕ} (hm : 0<m) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : Measurable Y) {b : ℝ} (hb : ∀ v, |Y v|≤b) :
    (∫ v : Fin m → V, empiricalMean m Y v ∂Measure.pi (fun _ : Fin m ↦ nu))=∫ v, Y v ∂nu := by
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  have hI : Integrable Y nu := Integrable.of_bound hY.aestronglyMeasurable b
    (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using hb v))
  have hi (i : Fin m) : Integrable (fun v : Fin m → V ↦ Y (v i)) (Measure.pi (fun _ : Fin m ↦ nu)) :=
    ((measurePreserving_eval (fun _ : Fin m ↦ nu) i).hasLaw.integrable_comp hI)
  unfold empiricalMean
  rw [integral_div,integral_finsetSum _ (fun i _ ↦ hi i)]
  have he (i : Fin m) : (∫ v : Fin m → V, Y (v i) ∂Measure.pi (fun _ : Fin m ↦ nu))=
      ∫ v, Y v ∂nu := (measurePreserving_eval (fun _ : Fin m ↦ nu) i).hasLaw.integral_comp hY.aestronglyMeasurable
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem empiricalMean_variance {m : ℕ} (hm : 0<m) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : Measurable Y) {b : ℝ} (hb : ∀ v, |Y v|≤b) :
    variance (empiricalMean m Y) (Measure.pi (fun _ : Fin m ↦ nu))=variance Y nu/(m : ℝ) := by
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  have hLp : MemLp Y 2 nu := MemLp.of_bound hY.aestronglyMeasurable b
    (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using hb v))
  have H := variance_sum_pi (ι := Fin m) (μ := fun _ : Fin m ↦ nu) (X := fun _ : Fin m ↦ Y) (fun _ ↦ hLp)
  have heval : (∑ i : Fin m, fun v : Fin m → V ↦ Y (v i))=
      (fun v : Fin m → V ↦ ∑ i : Fin m, Y (v i)) := by
    funext v
    simp only [Finset.sum_apply]
  rw [heval] at H
  have hs : variance (fun v : Fin m → V ↦ ∑ i : Fin m, Y (v i))
      (Measure.pi (fun _ : Fin m ↦ nu))=(m : ℝ)*variance Y nu := by
    simpa only [Finset.sum_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
  have he : empiricalMean m Y=(fun v : Fin m → V ↦ (1/(m : ℝ))*(∑ i : Fin m, Y (v i))) := by
    funext v
    unfold empiricalMean
    ring
  rw [he,variance_const_mul,hs]
  field_simp

theorem empiricalMean_L1_error_le {m : ℕ} (hm : 0<m) (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V → ℝ} (hY : Measurable Y) {b : ℝ} (hb0 : 0≤b) (hb : ∀ v, |Y v|≤b) :
    (∫ v : Fin m → V, |empiricalMean m Y v-(∫ w, Y w ∂nu)|
      ∂Measure.pi (fun _ : Fin m ↦ nu))≤b/Real.sqrt (m : ℝ) := by
  let P := Measure.pi (fun _ : Fin m ↦ nu)
  have hLpY : MemLp Y 2 nu := MemLp.of_bound hY.aestronglyMeasurable b
    (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using hb v))
  have hVarY : variance Y nu≤b^2 := by
    have H := variance_le_expectation_sq (μ := nu) hY.aestronglyMeasurable
    have H2 : (∫ v, (Y v)^2 ∂nu)≤b^2 := by
      have HH := integral_mono_ae hLpY.integrable_sq (integrable_const (b^2))
        (Eventually.of_forall (fun v ↦ by
          have H := pow_le_pow_left₀ (abs_nonneg _) (hb v) 2
          simpa only [sq_abs] using H))
      simpa only [integral_const,probReal_univ,one_smul] using HH
    exact H.trans H2
  have hEmpM := empiricalMean_measurable m hY
  have hLpEmp : MemLp (empiricalMean m Y) 2 P := MemLp.of_bound hEmpM.aestronglyMeasurable b
    (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using empiricalMean_abs_le hm hb v))
  let X : (Fin m → V) → ℝ := fun v ↦ empiricalMean m Y v-(∫ w, Y w ∂nu)
  have hLpX : MemLp X 2 P := hLpEmp.sub (memLp_const _)
  have hAbs : MemLp (fun v ↦ |X v|) 2 P := by simpa only [Real.norm_eq_abs] using hLpX.norm
  have hCS : (∫ v, |X v| ∂P)^2≤∫ v, (X v)^2 ∂P := by
    have H := variance_nonneg (fun v ↦ |X v|) P
    rw [variance_eq_sub hAbs] at H
    change 0≤(∫ v, |X v|^2 ∂P)-(∫ v, |X v| ∂P)^2 at H
    simp only [sq_abs] at H
    linarith
  have hVar : (∫ v, (X v)^2 ∂P)≤b^2/(m : ℝ) := by
    have H := empiricalMean_variance hm nu hY hb
    rw [variance_eq_integral hEmpM.aemeasurable,empiricalMean_integral hm nu hY hb] at H
    change (∫ v, (X v)^2 ∂P)=variance Y nu/(m : ℝ) at H
    rw [H]
    exact div_le_div_of_nonneg_right hVarY (Nat.cast_nonneg m)
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hs : 0<Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hSq : (b/Real.sqrt (m : ℝ))^2=b^2/(m : ℝ) := by
    rw [div_pow,Real.sq_sqrt hmR.le]
  apply (sq_le_sq₀ (integral_nonneg (fun _ ↦ abs_nonneg _)) (div_nonneg hb0 hs.le)).mp
  exact (hCS.trans hVar).trans_eq hSq.symm

def normalizer (nu : Measure V) (F : V → ℝ) (t : ℝ) : ℝ := ∫ v, Real.exp (t*F v) ∂nu

def empiricalNormalizer (m : ℕ) (F : V → ℝ) (t : ℝ) : (Fin m → V) → ℝ :=
  empiricalMean m (fun v ↦ Real.exp (t*F v))

theorem exp_score_bounds {F : V → ℝ} {B : ℝ} (hB : ∀ v, |F v|≤B) (t : ℝ) (v : V) :
    Real.exp (-|t| *B)≤Real.exp (t*F v) ∧ Real.exp (t*F v)≤Real.exp (|t| *B) := by
  have H : |t*F v|≤|t| *B := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB v) (abs_nonneg t)
  exact ⟨Real.exp_le_exp.mpr (by simpa only [neg_mul] using (abs_le.mp H).1),
    Real.exp_le_exp.mpr (abs_le.mp H).2⟩

theorem normalizer_mem_Icc (nu : Measure V) [IsProbabilityMeasure nu] {F : V → ℝ}
    (hF : Measurable F) {B : ℝ} (hB : ∀ v, |F v|≤B) (t : ℝ) :
    normalizer nu F t∈Set.Icc (Real.exp (-|t| *B)) (Real.exp (|t| *B)) := by
  have hi : Integrable (fun v ↦ Real.exp (t*F v)) nu :=
    Integrable.of_bound ((hF.const_mul t).exp).aestronglyMeasurable (Real.exp (|t| *B))
      (Eventually.of_forall (fun v ↦ by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact (exp_score_bounds hB t v).2))
  have hlo := integral_mono (integrable_const (Real.exp (-|t| *B))) hi (fun v ↦ (exp_score_bounds hB t v).1)
  have hhi := integral_mono hi (integrable_const (Real.exp (|t| *B))) (fun v ↦ (exp_score_bounds hB t v).2)
  simpa only [Set.mem_Icc,integral_const,probReal_univ,one_smul,normalizer] using And.intro hlo hhi

theorem empiricalNormalizer_mem_Icc {m : ℕ} (hm : 0<m) {F : V → ℝ}
    {B : ℝ} (hB : ∀ v, |F v|≤B) (t : ℝ) (v : Fin m → V) :
    empiricalNormalizer m F t v∈Set.Icc (Real.exp (-|t| *B)) (Real.exp (|t| *B)) := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  unfold empiricalNormalizer empiricalMean
  constructor
  · rw [le_div_iff₀ hmR]
    calc
      _ = ∑ _i : Fin m, Real.exp (-|t| *B) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ (exp_score_bounds hB t (v i)).1)
  · rw [div_le_iff₀ hmR]
    calc
      _ ≤ ∑ _i : Fin m, Real.exp (|t| *B) := Finset.sum_le_sum (fun i _ ↦ (exp_score_bounds hB t (v i)).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem empiricalNormalizer_L1_error_le {m : ℕ} (hm : 0<m) (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V → ℝ} (hF : Measurable F) {B : ℝ} (hB : ∀ v, |F v|≤B) (t : ℝ) :
    (∫ v : Fin m → V, |empiricalNormalizer m F t v-normalizer nu F t|
      ∂Measure.pi (fun _ : Fin m ↦ nu))≤Real.exp (|t| *B)/Real.sqrt (m : ℝ) := by
  apply empiricalMean_L1_error_le hm nu (hF.const_mul t).exp (Real.exp_pos _).le
  intro v
  rw [abs_of_pos (Real.exp_pos _)]
  exact (exp_score_bounds hB t v).2

theorem inverse_power_lipschitz {a x y : ℝ} (ha : 0<a) (hx : a≤x) (hy : a≤y) (n : ℕ) :
    |1/x^n-1/y^n|≤((n : ℝ)/a^(n+1))*|x-y| := by
  let f : ℝ → ℝ := fun z ↦ z^(-(n : ℤ))
  have hd (z : ℝ) (hz : z∈Set.Ici a) : HasDerivAt f (-(n : ℝ)/z^(n+1)) z := by
    have hz0 : z≠0 := (ha.trans_le hz).ne'
    have H := hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz0)
    have he : (-(n : ℤ))-1= -((n+1 : ℕ) : ℤ) := by omega
    simpa only [f,he,Int.cast_neg,Int.cast_natCast,zpow_neg,zpow_natCast,div_eq_mul_inv] using H
  have hb (z : ℝ) (hz : z∈Set.Ici a) : ‖deriv f z‖≤(n : ℝ)/a^(n+1) := by
    rw [(hd z hz).deriv,Real.norm_eq_abs,abs_div,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ)≤n),abs_of_pos (pow_pos (ha.trans_le hz) _)]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (pow_pos ha _) (pow_le_pow_left₀ ha.le hz _)
  have H := Convex.norm_image_sub_le_of_norm_deriv_le (fun z hz ↦ (hd z hz).differentiableAt)
    hb (convex_Ici a) hy hx
  simpa only [f,Real.norm_eq_abs,zpow_neg,zpow_natCast,one_div] using H

theorem weighted_inverse_normalizer_error_le {m : ℕ} (hm : 0<m)
    (nu : Measure V) [IsProbabilityMeasure nu] {F : V → ℝ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ v, |F v|≤B) (t numerator : ℝ) (n : ℕ)
    (hNumerator : |numerator|≤Real.exp ((n : ℝ)*|t| *B)) :
    (∫ v : Fin m → V,
      |numerator/(empiricalNormalizer m F t v)^n-numerator/(normalizer nu F t)^n|
      ∂Measure.pi (fun _ : Fin m ↦ nu))≤
      (n : ℝ)*Real.exp ((2*(n : ℝ)+2)*|t| *B)/Real.sqrt (m : ℝ) := by
  let P := Measure.pi (fun _ : Fin m ↦ nu)
  let a := Real.exp (-|t| *B)
  let b := Real.exp (|t| *B)
  let C := Real.exp ((n : ℝ)*|t| *B)*((n : ℝ)/a^(n+1))
  have ha : 0<a := Real.exp_pos _
  have hC : 0≤C := by dsimp only [C]; positivity
  have hZ := normalizer_mem_Icc nu hF hB t
  have hEmp (v : Fin m → V) := empiricalNormalizer_mem_Icc hm hB t v
  have hEm := empiricalMean_measurable m (hF.const_mul t).exp
  change Measurable (empiricalNormalizer m F t) at hEm
  have hZabs : |normalizer nu F t|≤b := by
    rw [abs_of_nonneg (ha.le.trans hZ.1)]
    exact hZ.2
  have hEmpAbs (v : Fin m → V) : |empiricalNormalizer m F t v|≤b := by
    rw [abs_of_nonneg (ha.le.trans (hEmp v).1)]
    exact (hEmp v).2
  have hpoint (v : Fin m → V) :
      |numerator/(empiricalNormalizer m F t v)^n-numerator/(normalizer nu F t)^n|≤
      C*|empiricalNormalizer m F t v-normalizer nu F t| := by
    calc
      _ = |numerator| *|1/(empiricalNormalizer m F t v)^n-1/(normalizer nu F t)^n| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ Real.exp ((n : ℝ)*|t| *B)*
          (((n : ℝ)/a^(n+1))*|empiricalNormalizer m F t v-normalizer nu F t|) :=
        mul_le_mul hNumerator (inverse_power_lipschitz ha (hEmp v).1 hZ.1 n)
          (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by dsimp only [C]; ring
  have hErrI : Integrable (fun v : Fin m → V ↦ |empiricalNormalizer m F t v-normalizer nu F t|) P := by
    have hErrM : Measurable (fun v : Fin m → V ↦ |empiricalNormalizer m F t v-normalizer nu F t|) :=
      continuous_abs.measurable.comp (hEm.sub measurable_const)
    apply Integrable.of_bound hErrM.aestronglyMeasurable (2*b)
    apply Eventually.of_forall
    intro v
    change ‖|empiricalNormalizer m F t v-normalizer nu F t|‖≤2*b
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans ((add_le_add (hEmpAbs v) hZabs).trans_eq (by ring))
  have hLm : Measurable (fun v : Fin m → V ↦
      |numerator/(empiricalNormalizer m F t v)^n-numerator/(normalizer nu F t)^n|) :=
    continuous_abs.measurable.comp ((measurable_const.div (hEm.pow_const n)).sub measurable_const)
  have hLI : Integrable (fun v : Fin m → V ↦
      |numerator/(empiricalNormalizer m F t v)^n-numerator/(normalizer nu F t)^n|) P := by
    apply (hErrI.const_mul C).mono' hLm.aestronglyMeasurable
    apply Eventually.of_forall
    intro v
    change ‖|numerator/(empiricalNormalizer m F t v)^n-numerator/(normalizer nu F t)^n|‖≤_
    rw [Real.norm_eq_abs,abs_abs]
    exact hpoint v
  have hCoeff : C*b=(n : ℝ)*Real.exp ((2*(n : ℝ)+2)*|t| *B) := by
    have hPow : (Real.exp (-|t| *B))^(n+1)=
        Real.exp (-(((n+1 : ℕ) : ℝ)*(|t| *B))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp only [C,a,b]
    rw [hPow,Real.exp_neg,div_eq_mul_inv,inv_inv]
    calc
      _ = (n : ℝ)*(Real.exp ((n : ℝ)*|t| *B)*
        Real.exp (((n+1 : ℕ) : ℝ)*(|t| *B))*Real.exp (|t| *B)) := by ring
      _ = _ := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        rw [Nat.cast_add,Nat.cast_one]
        ring
  calc
    _ ≤ ∫ v : Fin m → V, C*|empiricalNormalizer m F t v-normalizer nu F t| ∂P :=
      integral_mono hLI (hErrI.const_mul C) hpoint
    _ = C*(∫ v : Fin m → V, |empiricalNormalizer m F t v-normalizer nu F t| ∂P) := integral_const_mul _ _
    _ ≤ C*(b/Real.sqrt (m : ℝ)) := mul_le_mul_of_nonneg_left
      (empiricalNormalizer_L1_error_le hm nu hF hB t) hC
    _ = (C*b)/Real.sqrt (m : ℝ) := by ring
    _ = _ := by rw [hCoeff]

end
end TensorPCA.NonRSLowerProofs.GGFiniteEmpiricalNormalizer
