-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A deterministic product-measure estimate for candidate duplication mass. It proves a
quantitative bound from measurable sets and their masses; no probabilistic
duplication principle is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGNoDuplicationMass
open MeasureTheory Set
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Omega : Type*} [MeasurableSpace Omega]

private theorem prod_mass_le_of_sections (nu : Measure Omega) [IsProbabilityMeasure nu]
    (S : Set Omega) (hS : MeasurableSet S) (C : Set (Omega×Omega)) (hC : MeasurableSet C)
    (hFirst : ∀p∈C,p.1∈S) {tau : ℝ}
    (hSection : ∀u∈S,nu.real {v | (u,v)∈C}≤tau) :
    (nu.prod nu).real C≤nu.real S*tau := by
  have hi : Integrable (C.indicator (fun _ : Omega×Omega ↦ (1 : ℝ))) (nu.prod nu) :=
    (integrable_const _).indicator hC
  have hInner (u : Omega) :
      (∫v,(C.indicator (fun _ : Omega×Omega ↦ (1 : ℝ))) (u,v) ∂nu)=nu.real {v | (u,v)∈C} := by
    have hSec : MeasurableSet {v | (u,v)∈C} := hC.preimage (measurable_const.prodMk measurable_id)
    change (∫v,({v | (u,v)∈C}.indicator (fun _ ↦ (1 : ℝ))) v ∂nu)=_
    rw [integral_indicator_const 1 hSec,smul_eq_mul,mul_one]
  have hMass : (∫p,C.indicator (fun _ : Omega×Omega ↦ (1 : ℝ)) p ∂nu.prod nu)=(nu.prod nu).real C := by
    rw [integral_indicator_const 1 hC,smul_eq_mul,mul_one]
  have H := integral_mono hi.integral_prod_left ((integrable_const tau).indicator hS) (fun u ↦ by
    rw [hInner]
    by_cases hu : u∈S
    · rw [indicator_of_mem hu]
      exact hSection u hu
    · rw [indicator_of_notMem hu]
      have he : {v | (u,v)∈C}=∅ := by
        ext v
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        exact fun hv ↦ hu (hFirst (u,v) hv)
      rw [he,measureReal_empty])
  rw [←hMass,integral_prod _ hi]
  simpa only [integral_indicator_const tau hS,smul_eq_mul] using H

 theorem bad_pair_mass_lower (nu : Measure Omega) [IsProbabilityMeasure nu]
    (B : Omega→Set Omega) (hB : MeasurableSet {p : Omega×Omega | p.2∈B p.1})
    (S : Set Omega) (hS : MeasurableSet S) {tau : ℝ}
    (hSmall : ∀u∈S,nu.real (B u)≤tau) :
    nu.real S*(nu.real S-tau)≤
      (nu.prod nu).real {p : Omega×Omega | p.1∈S ∧ p.2∈S ∧ p.2∉B p.1} := by
  let G := {p : Omega×Omega | p.2∈B p.1}
  let C := (S×ˢS)∩G
  have hC : MeasurableSet C := (hS.prod hS).inter hB
  have hFirst : ∀p∈C,p.1∈S := fun p hp ↦ hp.1.1
  have hSection : ∀u∈S,nu.real {v | (u,v)∈C}≤tau := by
    intro u hu
    exact (measureReal_mono (fun v hv ↦ hv.2)).trans (hSmall u hu)
  have hGood := prod_mass_le_of_sections nu S hS C hC hFirst hSection
  have hSplit := measureReal_inter_add_sdiff (μ := nu.prod nu) (s := S×ˢS) hB
  rw [measureReal_prod_prod] at hSplit
  have hBad : (S×ˢS)\G={p : Omega×Omega | p.1∈S ∧ p.2∈S ∧ p.2∉B p.1} := by
    ext p
    simp only [mem_sdiff,mem_prod,mem_setOf_eq,G,and_assoc]
  change (nu.prod nu).real C+(nu.prod nu).real ((S×ˢS)\G)=nu.real S*nu.real S at hSplit
  rw [hBad] at hSplit
  nlinarith only [hGood,hSplit]

 theorem small_section_set_mass_le (nu : Measure Omega) [IsProbabilityMeasure nu]
    (B : Omega→Set Omega) (hB : MeasurableSet {p : Omega×Omega | p.2∈B p.1})
    (S : Set Omega) (hS : MeasurableSet S) {tau : ℝ} (hTau : 0≤tau)
    (hSmall : ∀u∈S,nu.real (B u)≤tau) :
    nu.real S≤tau+Real.sqrt ((nu.prod nu).real {p : Omega×Omega | p.1∈S ∧ p.2∈S ∧ p.2∉B p.1}) := by
  have H := bad_pair_mass_lower nu B hB S hS hSmall
  by_cases h : nu.real S≤tau
  · exact h.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have hDiff : 0≤nu.real S-tau := sub_nonneg.mpr (le_of_not_ge h)
    have hSq : (nu.real S-tau)^2≤
        (nu.prod nu).real {p : Omega×Omega | p.1∈S ∧ p.2∈S ∧ p.2∉B p.1} := by
      nlinarith only [H,mul_nonneg hTau hDiff]
    have hRoot := Real.le_sqrt_of_sq_le hSq
    linarith only [hRoot]

end
end TensorPCA.NonRSLowerProofs.FiniteGGNoDuplicationMass
