-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedIIDMarkedMoments
public import Mathlib.Probability.Independence.Basic

/-! Independent uniform finite labels and a collision union bound. The ordered-pair
constant is sufficient for the finite replica passage.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteIIDLabelCollision
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section

def uniformLabelPMF (K : ℕ) (hK : 0<K) : PMF (Fin K) :=
  PMF.ofFintype (fun _ => (K : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (ne_of_gt hK)) (ENNReal.natCast_ne_top K))

def uniformLabelLaw (K : ℕ) (hK : 0<K) : Measure (Fin K) := (uniformLabelPMF K hK).toMeasure

instance uniformLabelLaw_probability (K : ℕ) (hK : 0<K) :
    IsProbabilityMeasure (uniformLabelLaw K hK) := by unfold uniformLabelLaw; infer_instance

def iidLabelLaw (n K : ℕ) (hK : 0<K) : Measure (Fin n→Fin K) :=
  Measure.pi (fun _ : Fin n => uniformLabelLaw K hK)

instance iidLabelLaw_probability (n K : ℕ) (hK : 0<K) :
    IsProbabilityMeasure (iidLabelLaw n K hK) := by unfold iidLabelLaw; infer_instance

theorem uniformLabelLaw_singleton (K : ℕ) (hK : 0<K) (j : Fin K) :
    uniformLabelLaw K hK {j}=(K : ℝ≥0∞)⁻¹ := by
  rw [uniformLabelLaw,PMF.toMeasure_apply_singleton (uniformLabelPMF K hK) j (measurableSet_singleton j)]
  rfl

theorem uniformLabelLaw_diagonal (K : ℕ) (hK : 0<K) :
    ((uniformLabelLaw K hK).prod (uniformLabelLaw K hK)) {p : Fin K×Fin K | p.1=p.2}=
      (K : ℝ≥0∞)⁻¹ := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have H (j : Fin K) : Prod.mk j ⁻¹' {p : Fin K×Fin K | p.1=p.2}={j} := by
    ext i
    simp [eq_comm]
  simp_rw [H,uniformLabelLaw_singleton]
  simp

theorem iidLabelLaw_pair_collision {n K : ℕ} (hK : 0<K) (i j : Fin n) (hij : i≠j) :
    iidLabelLaw n K hK {s | s i=s j}=(K : ℝ≥0∞)⁻¹ := by
  have hi := (measurePreserving_eval (fun _ : Fin n => uniformLabelLaw K hK) i).map_eq
  have hj := (measurePreserving_eval (fun _ : Fin n => uniformLabelLaw K hK) j).map_eq
  have hInd := (iIndepFun_pi (μ := fun _ : Fin n => uniformLabelLaw K hK)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have H := hInd.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  rw [hi,hj] at H
  have HM := congrArg (fun m : Measure (Fin K×Fin K) => m {p | p.1=p.2}) H
  rw [Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    (measurableSet_eq_fun measurable_fst measurable_snd),uniformLabelLaw_diagonal] at HM
  exact HM

theorem iidLabelLaw_collision_le (n K : ℕ) (hK : 0<K) :
    (iidLabelLaw n K hK).real {s | ¬Function.Injective s}≤
      ((n*(n-1) : ℕ) : ℝ)/(K : ℝ) := by
  classical
  let S := (Finset.univ : Finset (Fin n)).offDiag
  have HS : {s : Fin n→Fin K | ¬Function.Injective s}=
      ⋃p∈S,{s : Fin n→Fin K | s p.1=s p.2} := by
    ext s
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp h
      exact ⟨(i,j),Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hij⟩,he⟩
    · rintro ⟨p,hp,he⟩
      exact Function.not_injective_iff.mpr ⟨p.1,p.2,he,(Finset.mem_offDiag.mp hp).2.2⟩
  rw [HS]
  calc
    _ ≤ ∑p∈S,(iidLabelLaw n K hK).real {s | s p.1=s p.2} := measureReal_biUnion_finset_le _ _
    _ = ∑_p∈S,(K : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Measure.real,iidLabelLaw_pair_collision hK p.1 p.2 (Finset.mem_offDiag.mp hp).2.2]
      simp
    _ = ((n*(n-1) : ℕ) : ℝ)/(K : ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul,S,Finset.offDiag_card,Finset.card_univ,Fintype.card_fin]
      rw [← Nat.mul_sub_one]
      rfl

theorem integral_sub_le_collision {n K : ℕ} (hK : 0<K) {F G : (Fin n→Fin K)→ℝ}
    (hF : Measurable F) (hG : Measurable G) {C : ℝ} (hC : 0≤C)
    (hb : ∀s,0≤F s ∧ F s≤C ∧ 0≤G s ∧ G s≤C)
    (heq : ∀s,Function.Injective s→F s=G s) :
    |(∫s,F s ∂iidLabelLaw n K hK)-(∫s,G s ∂iidLabelLaw n K hK)|≤
      C*((n*(n-1) : ℕ) : ℝ)/(K : ℝ) := by
  classical
  let S : Set (Fin n→Fin K) := {s | ¬Function.Injective s}
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  have hiF : Integrable F (iidLabelLaw n K hK) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun s => by rw [Real.norm_eq_abs,abs_of_nonneg (hb s).1]; exact (hb s).2.1))
  have hiG : Integrable G (iidLabelLaw n K hK) :=
    Integrable.of_bound hG.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun s => by rw [Real.norm_eq_abs,abs_of_nonneg (hb s).2.2.1]; exact (hb s).2.2.2))
  have hbound : ∀s,‖F s-G s‖≤S.indicator (fun _ => C) s := by
    intro s
    by_cases hs : s∈S
    · rw [Set.indicator_of_mem hs,Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith only [(hb s).1,(hb s).2.2.2],by linarith only [(hb s).2.1,(hb s).2.2.1]⟩
    · have hsi : Function.Injective s := by simpa only [S,Set.mem_setOf_eq,not_not] using hs
      rw [heq s hsi,sub_self,norm_zero,Set.indicator_of_notMem hs]
  have HB := norm_integral_le_of_norm_le (μ := iidLabelLaw n K hK) ((integrable_const C).indicator hS)
    (Filter.Eventually.of_forall hbound)
  rw [integral_sub hiF hiG] at HB
  have HB' : |(∫s,F s ∂iidLabelLaw n K hK)-(∫s,G s ∂iidLabelLaw n K hK)|≤
      C*(iidLabelLaw n K hK).real S := by
    simpa only [Real.norm_eq_abs,integral_indicator_const C hS,smul_eq_mul,mul_comm] using HB
  exact HB'.trans (by
    have H := mul_le_mul_of_nonneg_left (iidLabelLaw_collision_le n K hK) hC
    simpa only [S,mul_div_assoc] using H)

theorem replica_product_integral_sub_le_collision {n K : ℕ} (hK : 0<K)
    {R S : (Fin n→Fin K)→Fin n→ℝ}
    (hR : ∀i,Measurable (fun labels => R labels i))
    (hS : ∀i,Measurable (fun labels => S labels i)) {a : ℝ} (ha : 0≤a)
    (hb : ∀labels i,0≤R labels i ∧ R labels i≤a ∧ 0≤S labels i ∧ S labels i≤a)
    (heq : ∀labels,Function.Injective labels→∀i,R labels i=S labels i) :
    |(∫labels,∏i,R labels i ∂iidLabelLaw n K hK)-
      (∫labels,∏i,S labels i ∂iidLabelLaw n K hK)|≤
        a^n*((n*(n-1) : ℕ) : ℝ)/(K : ℝ) := by
  classical
  apply integral_sub_le_collision hK
    (Finset.measurable_prod _ (fun i _ => hR i))
    (Finset.measurable_prod _ (fun i _ => hS i)) (pow_nonneg ha n)
  · intro labels
    have hR0 : 0≤∏i,R labels i := Finset.prod_nonneg (fun i _ => (hb labels i).1)
    have hS0 : 0≤∏i,S labels i := Finset.prod_nonneg (fun i _ => (hb labels i).2.2.1)
    have hR1 : (∏i,R labels i)≤a^n := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => (hb labels i).1) (fun i _ => (hb labels i).2.1))
    have hS1 : (∏i,S labels i)≤a^n := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => (hb labels i).2.2.1) (fun i _ => (hb labels i).2.2.2))
    exact ⟨hR0,hR1,hS0,hS1⟩
  · intro labels hi
    exact Finset.prod_congr rfl (fun i _ => heq labels hi i)

theorem collision_cost_tendsto_zero (n : ℕ) (C : ℝ) :
    Filter.Tendsto (fun K : ℕ => C*((n*(n-1) : ℕ) : ℝ)/(K : ℝ)) Filter.atTop (nhds 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat _

end
end TensorPCA.NonRSLowerProofs.FiniteIIDLabelCollision
