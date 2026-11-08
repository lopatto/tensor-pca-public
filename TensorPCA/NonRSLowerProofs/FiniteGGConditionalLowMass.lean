-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowLowerMass
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Moments.Variance

/-! Conditional candidate masses under a Markov spin kernel. All measurability and
product/conditional averaging identities are proved from measurable graphs; no
duplication or GG principle is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGConditionalLowMass
open MeasureTheory ProbabilityTheory Set
open FiniteGGNoDuplicationMass FiniteGGWindowLowerMass FiniteGGWindowScalar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {P V : Type*} [MeasurableSpace P] [MeasurableSpace V]

def candidateMass (G : Kernel P V) (B : Set (P×(V×V))) (q : P×V) : ℝ :=
  (G q.1).real {v | (q.1,(q.2,v))∈B}

def badPairMass (G : Kernel P V) (Omega : Set (P×V)) (B : Set (P×(V×V))) (p : P) : ℝ :=
  ((G p).prod (G p)).real {r : V×V | (p,r.1)∈Omega ∧ (p,r.2)∈Omega ∧ (p,r)∉B}

 theorem candidateMass_measurable (G : Kernel P V) [IsMarkovKernel G]
    (B : Set (P×(V×V))) (hB : MeasurableSet B) : Measurable (candidateMass G B) := by
  have hLift : MeasurableSet {q : (P×V)×V | (q.1.1,(q.1.2,q.2))∈B} :=
    hB.preimage (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have H := (Kernel.measurable_kernel_prodMk_left (κ := G.comap Prod.fst measurable_fst) hLift).ennreal_toReal
  unfold candidateMass
  simpa only [Measure.real,Kernel.comap_apply,Set.preimage,Set.mem_setOf_eq] using H

 theorem candidateMass_mem_Icc (G : Kernel P V) [IsMarkovKernel G]
    (B : Set (P×(V×V))) (q : P×V) : candidateMass G B q∈Icc (0 : ℝ) 1 := by
  refine ⟨measureReal_nonneg,?_⟩
  simpa only [candidateMass,probReal_univ] using
    (measureReal_mono (μ := G q.1) (subset_univ {v | (q.1,(q.2,v))∈B}))

 theorem badPairMass_measurable (G : Kernel P V) [IsMarkovKernel G]
    (Omega : Set (P×V)) (hOmega : MeasurableSet Omega)
    (B : Set (P×(V×V))) (hB : MeasurableSet B) : Measurable (badPairMass G Omega B) := by
  have hBad : MeasurableSet {q : P×(V×V) | (q.1,q.2.1)∈Omega ∧ (q.1,q.2.2)∈Omega ∧ q∉B} :=
    (hOmega.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      ((hOmega.preimage (measurable_fst.prodMk measurable_snd.snd)).inter hB.compl)
  have H := (Kernel.measurable_kernel_prodMk_left (κ := G×ₖG) hBad).ennreal_toReal
  unfold badPairMass
  simpa only [Measure.real,Kernel.prod_apply,Set.preimage,Set.mem_setOf_eq] using H

 theorem badPairMass_mem_Icc (G : Kernel P V) [IsMarkovKernel G]
    (Omega : Set (P×V)) (B : Set (P×(V×V))) (p : P) : badPairMass G Omega B p∈Icc (0 : ℝ) 1 := by
  refine ⟨measureReal_nonneg,?_⟩
  simpa only [badPairMass,probReal_univ] using (measureReal_mono (μ := (G p).prod (G p))
    (subset_univ {r : V×V | (p,r.1)∈Omega ∧ (p,r.2)∈Omega ∧ (p,r)∉B}))

 theorem conditional_low_mass_le (mu : Measure P) [IsProbabilityMeasure mu]
    (G : Kernel P V) [IsMarkovKernel G]
    (Omega : Set (P×V)) (hOmega : MeasurableSet Omega)
    (B : Set (P×(V×V))) (hB : MeasurableSet B)
    (A : Set (P×V)) (hA : MeasurableSet A) (hAOmega : A⊆Omega)
    {kappa : ℝ} (hK : 0≤kappa) :
    (mu⊗ₘG).real (A∩{q | candidateMass G B q≤kappa})≤
      kappa+Real.sqrt (∫p,badPairMass G Omega B p ∂mu) := by
  let Low := A∩{q | candidateMass G B q≤kappa}
  let L := fun p : P ↦ (G p).real {u | (p,u)∈Low}
  let D := badPairMass G Omega B
  have hWm := candidateMass_measurable G B hB
  have hLow : MeasurableSet Low := hA.inter (measurableSet_le hWm measurable_const)
  have hLm : Measurable L := (Kernel.measurable_kernel_prodMk_left (κ := G) hLow).ennreal_toReal
  have hDm : Measurable D := badPairMass_measurable G Omega hOmega B hB
  have hPoint (p : P) : L p≤kappa+Real.sqrt (D p) := by
    let S := {u : V | (p,u)∈Low}
    let Bp := fun u : V ↦ {v | (p,(u,v))∈B}
    have hS : MeasurableSet S := hLow.preimage (measurable_const.prodMk measurable_id)
    have hBp : MeasurableSet {r : V×V | r.2∈Bp r.1} := hB.preimage (measurable_const.prodMk measurable_id)
    have hSmall : ∀u∈S,(G p).real (Bp u)≤kappa := fun u hu ↦ hu.2
    have H := small_section_set_mass_le (G p) Bp hBp S hS hK hSmall
    have hDle : ((G p).prod (G p)).real {r : V×V | r.1∈S ∧ r.2∈S ∧ r.2∉Bp r.1}≤D p :=
      measureReal_mono (fun r hr ↦ ⟨hAOmega hr.1.1,hAOmega hr.2.1.1,hr.2.2⟩)
    exact H.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hDle))
  have hLi : Integrable L mu := Integrable.of_bound hLm.aestronglyMeasurable 1 (.of_forall (fun p ↦ by
    rw [Real.norm_of_nonneg measureReal_nonneg]
    simpa only [probReal_univ] using (measureReal_mono (μ := G p) (subset_univ {u | (p,u)∈Low}))))
  have hRootLp : MemLp (fun p ↦ Real.sqrt (D p)) 2 mu := MemLp.of_bound hDm.sqrt.aestronglyMeasurable 1
    (.of_forall (fun p ↦ by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (badPairMass_mem_Icc G Omega B p).2))
  have hRoot : (∫p,Real.sqrt (D p) ∂mu)≤Real.sqrt (∫p,D p ∂mu) := by
    have H := variance_nonneg (fun p ↦ Real.sqrt (D p)) mu
    rw [variance_eq_sub hRootLp] at H
    change 0≤(∫p,(Real.sqrt (D p))^2 ∂mu)-(∫p,Real.sqrt (D p) ∂mu)^2 at H
    have he : (fun p ↦ (Real.sqrt (D p))^2)=D := by
      funext p
      exact Real.sq_sqrt (badPairMass_mem_Icc G Omega B p).1
    rw [he] at H
    exact Real.le_sqrt_of_sq_le (by linarith only [H])
  have hRooti := hRootLp.integrable (by norm_num)
  have hRi : Integrable (fun p ↦ kappa+Real.sqrt (D p)) mu := (integrable_const kappa).add hRooti
  have hInt := integral_mono hLi hRi hPoint
  rw [integral_add (integrable_const kappa) hRooti,integral_const,probReal_univ,one_smul] at hInt
  have hMass : (mu⊗ₘG).real Low=∫p,L p ∂mu := by
    have hi : Integrable (Low.indicator (fun _ : P×V ↦ (1 : ℝ))) (mu⊗ₘG) := (integrable_const _).indicator hLow
    calc
      _=∫q,Low.indicator (fun _ : P×V ↦ (1 : ℝ)) q ∂(mu⊗ₘG) := by
        rw [integral_indicator_const 1 hLow,smul_eq_mul,mul_one]
      _=∫p,∫u,Low.indicator (fun _ : P×V ↦ (1 : ℝ)) (p,u) ∂G p ∂mu := Measure.integral_compProd hi
      _=∫p,L p ∂mu := integral_congr_ae (.of_forall (fun p ↦ by
        have hSec : MeasurableSet {u | (p,u)∈Low} := hLow.preimage (measurable_const.prodMk measurable_id)
        change (∫u,({u | (p,u)∈Low}.indicator (fun _ ↦ (1 : ℝ))) u ∂G p)=L p
        rw [integral_indicator_const 1 hSec,smul_eq_mul,mul_one]))
  rw [hMass]
  exact hInt.trans (add_le_add le_rfl hRoot)

 theorem conditional_window_integral_lower (mu : Measure P) [IsProbabilityMeasure mu]
    (G : Kernel P V) [IsMarkovKernel G]
    (Omega : Set (P×V)) (hOmega : MeasurableSet Omega)
    (B : Set (P×(V×V))) (hB : MeasurableSet B)
    (A : Set (P×V)) (hA : MeasurableSet A) (hAOmega : A⊆Omega)
    {kappa eta : ℝ} (hK : 0<kappa) (n : ℕ) (hn : 2≤n)
    (hMoment : (∫q,A.indicator (candidateMass G B) q ∂(mu⊗ₘG))≤(mu⊗ₘG).real A/(n : ℝ)+eta) :
    (mu⊗ₘG).real A/3-kappa-Real.sqrt (∫p,badPairMass G Omega B p ∂mu)-4*eta/3≤
      ∫q,A.indicator (fun q ↦ window kappa (candidateMass G B q)) q ∂(mu⊗ₘG) := by
  let W : P×V→Icc (0 : ℝ) 1 := fun q ↦ ⟨candidateMass G B q,candidateMass_mem_Icc G B q⟩
  have hW : Measurable W := (candidateMass_measurable G B hB).subtype_mk
  have hLow := conditional_low_mass_le mu G Omega hOmega B hB A hA hAOmega hK.le
  have H := window_integral_lower_of_moment (mu⊗ₘG) A hA W hW hK n hn hLow hMoment
  convert H using 1 <;> ring

end
end TensorPCA.NonRSLowerProofs.FiniteGGConditionalLowMass
