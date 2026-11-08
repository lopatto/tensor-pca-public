-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingMeasure

/-! Iid spin samples with one shared random mark parameter. The mean is `empiricalMean`,
and the independent sample law is mu.prod(nu^K); the mark parameter is shared by
every sample.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.NumeratorMarkClippingEmpirical
open MeasureTheory ProbabilityTheory Filter
open GGFiniteEmpiricalNormalizer NumeratorMarkClippingMeasure
open scoped BigOperators
noncomputable section
variable {G V : Type*} [MeasurableSpace G] [MeasurableSpace V]

theorem joint_empiricalMean_integrable (K : ℕ) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Integrable (fun p : G×V => F p.1 p.2) (mu.prod nu)) :
    Integrable (fun p : G×(Fin K→V) => empiricalMean K (F p.1) p.2)
      (mu.prod (Measure.pi (fun _ : Fin K => nu))) := by
  have hi (i : Fin K) : Integrable (fun p : G×(Fin K→V) => F p.1 (p.2 i))
      (mu.prod (Measure.pi (fun _ : Fin K => nu))) :=
    ((MeasurePreserving.id mu).prod (measurePreserving_eval (fun _ : Fin K => nu) i)).hasLaw.integrable_comp hF
  exact (integrable_finset_sum _ (fun i _ => hi i)).div_const (K : ℝ)

theorem joint_empiricalMean_integral {K : ℕ} (hK : 0<K) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Integrable (fun p : G×V => F p.1 p.2) (mu.prod nu)) :
    (∫p : G×(Fin K→V),empiricalMean K (F p.1) p.2
      ∂mu.prod (Measure.pi (fun _ : Fin K => nu)))=∫p : G×V,F p.1 p.2 ∂mu.prod nu := by
  have hi (i : Fin K) : Integrable (fun p : G×(Fin K→V) => F p.1 (p.2 i))
      (mu.prod (Measure.pi (fun _ : Fin K => nu))) :=
    ((MeasurePreserving.id mu).prod (measurePreserving_eval (fun _ : Fin K => nu) i)).hasLaw.integrable_comp hF
  have he (i : Fin K) : (∫p : G×(Fin K→V),F p.1 (p.2 i)
      ∂mu.prod (Measure.pi (fun _ : Fin K => nu)))=∫p : G×V,F p.1 p.2 ∂mu.prod nu :=
    ((MeasurePreserving.id mu).prod (measurePreserving_eval (fun _ : Fin K => nu) i)).hasLaw.integral_comp hF.aestronglyMeasurable
  unfold empiricalMean
  rw [integral_div,integral_finset_sum _ (fun i _ => hi i)]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

private theorem empirical_one_le {K : ℕ} (hK : 0<K) (Y : Fin K→ℝ) (hb : ∀i,1≤Y i) :
    1≤(∑i,Y i)/(K : ℝ) := by
  rw [le_div_iff₀ (Nat.cast_pos.mpr hK)]
  have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_mul] using H

theorem joint_empirical_clip_bounds {K : ℕ} (hK : 0<K)
    (mu : Measure G) [IsProbabilityMeasure mu] (nu : Measure V) [IsProbabilityMeasure nu]
    {F : G→V→ℝ} (hF1 : ∀ᵐp : G×V∂mu.prod nu,1≤F p.1 p.2) {L : ℝ} (hL : 1≤L) :
    ∀ᵐp : G×(Fin K→V)∂mu.prod (Measure.pi (fun _ : Fin K => nu)),
      1≤empiricalMean K (fun x => min (F p.1 x) L) p.2 ∧
      empiricalMean K (fun x => min (F p.1 x) L) p.2≤empiricalMean K (F p.1) p.2 := by
  have H : ∀ᵐp : G×(Fin K→V)∂mu.prod (Measure.pi (fun _ : Fin K => nu)),∀i,1≤F p.1 (p.2 i) :=
    ae_all_iff.mpr (fun i => ((MeasurePreserving.id mu).prod
      (measurePreserving_eval (fun _ : Fin K => nu) i)).quasiMeasurePreserving.ae hF1)
  filter_upwards [H] with p hp
  refine ⟨empirical_one_le hK _ (fun i => le_min (hp i) hL),?_⟩
  unfold empiricalMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => min_le_left _ _)) (Nat.cast_nonneg K)

theorem joint_empirical_clip_tail_le {K : ℕ} (hK : 0<K)
    (mu : Measure G) [IsProbabilityMeasure mu] (nu : Measure V) [IsProbabilityMeasure nu]
    {F : G→V→ℝ} (hF : Measurable (fun p : G×V => F p.1 p.2))
    (hF1 : ∀ᵐp : G×V∂mu.prod nu,1≤F p.1 p.2)
    (hF2 : Integrable (fun p : G×V => (F p.1 p.2)^2) (mu.prod nu)) {L : ℝ} (hL : 1≤L) :
    (∫p : G×(Fin K→V),empiricalMean K (F p.1) p.2-
      empiricalMean K (fun x => min (F p.1 x) L) p.2
      ∂mu.prod (Measure.pi (fun _ : Fin K => nu)))≤
      (∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/L := by
  have hI := mark_integrable_of_square (mu.prod nu) hF hF1 hF2
  have hC := clip_integrable (mu.prod nu) hF hF1 hL
  rw [integral_sub (joint_empiricalMean_integrable K mu nu hI) (joint_empiricalMean_integrable (F := fun g x => min (F g x) L) K mu nu hC),
    joint_empiricalMean_integral hK mu nu hI,joint_empiricalMean_integral (F := fun g x => min (F g x) L) hK mu nu hC,
    ← integral_sub hI hC]
  exact (clip_tail_integrable_and_bound (mu.prod nu) hF hF1 hF2 hL).2.2

theorem empirical_log_clip_error_le {K : ℕ} (hK : 0<K)
    (mu : Measure G) [IsProbabilityMeasure mu] (nu : Measure V) [IsProbabilityMeasure nu]
    {F : G→V→ℝ} (hF : Measurable (fun p : G×V => F p.1 p.2))
    (hF1 : ∀ᵐp : G×V∂mu.prod nu,1≤F p.1 p.2)
    (hF2 : Integrable (fun p : G×V => (F p.1 p.2)^2) (mu.prod nu)) {L : ℝ} (hL : 1≤L) :
    let P := mu.prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun p : G×(Fin K→V) => empiricalMean K (F p.1) p.2
    let C := fun p : G×(Fin K→V) => empiricalMean K (fun x => min (F p.1 x) L) p.2
    Integrable (fun p => Real.log (A p)) P ∧ Integrable (fun p => Real.log (C p)) P ∧
      0≤(∫p,Real.log (A p) ∂P)-(∫p,Real.log (C p) ∂P) ∧
      (∫p,Real.log (A p) ∂P)-(∫p,Real.log (C p) ∂P)≤(∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/L := by
  dsimp only
  have hI := joint_empiricalMean_integrable K mu nu (mark_integrable_of_square (mu.prod nu) hF hF1 hF2)
  have hC := joint_empiricalMean_integrable (F := fun g x => min (F g x) L) K mu nu (clip_integrable (mu.prod nu) hF hF1 hL)
  have hb := joint_empirical_clip_bounds hK mu nu hF1 hL
  have H := expected_log_sub_le_expected_sub _ hI hC hb
  refine ⟨log_integrable_of_one_le _ hI (hb.mono (fun _ hv => hv.1.trans hv.2)),
    log_integrable_of_one_le _ hC (hb.mono (fun _ hv => hv.1)),H.1,?_⟩
  exact H.2.trans (joint_empirical_clip_tail_le hK mu nu hF hF1 hF2 hL)

theorem empirical_power_clip_error_le {K : ℕ} (hK : 0<K)
    (mu : Measure G) [IsProbabilityMeasure mu] (nu : Measure V) [IsProbabilityMeasure nu]
    {F : G→V→ℝ} (hF : Measurable (fun p : G×V => F p.1 p.2))
    (hF1 : ∀ᵐp : G×V∂mu.prod nu,1≤F p.1 p.2)
    (hF2 : Integrable (fun p : G×V => (F p.1 p.2)^2) (mu.prod nu)) {L r : ℝ} (hL : 1≤L)
    (hr0 : 0≤r) (hr1 : r≤1) :
    let P := mu.prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun p : G×(Fin K→V) => empiricalMean K (F p.1) p.2
    let C := fun p : G×(Fin K→V) => empiricalMean K (fun x => min (F p.1 x) L) p.2
    Integrable (fun p => (A p)^r) P ∧ Integrable (fun p => (C p)^r) P ∧
      0≤(∫p,(A p)^r ∂P)-(∫p,(C p)^r ∂P) ∧
      (∫p,(A p)^r ∂P)-(∫p,(C p)^r ∂P)≤r*((∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/L) := by
  dsimp only
  have hI := joint_empiricalMean_integrable K mu nu (mark_integrable_of_square (mu.prod nu) hF hF1 hF2)
  have hC := joint_empiricalMean_integrable (F := fun g x => min (F g x) L) K mu nu (clip_integrable (mu.prod nu) hF hF1 hL)
  have hb := joint_empirical_clip_bounds hK mu nu hF1 hL
  have H := expected_power_sub_le_expected_sub _ hI hC hb hr0 hr1
  refine ⟨power_integrable_of_one_le _ hI (hb.mono (fun _ hv => hv.1.trans hv.2)) hr1,
    power_integrable_of_one_le _ hC (hb.mono (fun _ hv => hv.1)) hr1,H.1,?_⟩
  exact H.2.trans (mul_le_mul_of_nonneg_left (joint_empirical_clip_tail_le hK mu nu hF hF1 hF2 hL) hr0)

theorem normalized_empirical_power_clip_error_le {K : ℕ} (hK : 0<K)
    (mu : Measure G) [IsProbabilityMeasure mu] (nu : Measure V) [IsProbabilityMeasure nu]
    {F : G→V→ℝ} (hF : Measurable (fun p : G×V => F p.1 p.2))
    (hF1 : ∀ᵐp : G×V∂mu.prod nu,1≤F p.1 p.2)
    (hF2 : Integrable (fun p : G×V => (F p.1 p.2)^2) (mu.prod nu)) {L r : ℝ} (hL : 1≤L)
    (hr0 : 0<r) (hr1 : r≤1) :
    let P := mu.prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun p : G×(Fin K→V) => empiricalMean K (F p.1) p.2
    let C := fun p : G×(Fin K→V) => empiricalMean K (fun x => min (F p.1 x) L) p.2
    0≤((∫p,(A p)^r ∂P)-(∫p,(C p)^r ∂P))/r ∧
      ((∫p,(A p)^r ∂P)-(∫p,(C p)^r ∂P))/r≤(∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/L := by
  dsimp only
  have H := empirical_power_clip_error_le hK mu nu hF hF1 hF2 hL hr0.le hr1
  dsimp only at H
  refine ⟨div_nonneg H.2.2.1 hr0.le,?_⟩
  rw [div_le_iff₀ hr0]
  simpa only [mul_comm] using H.2.2.2

end
end TensorPCA.NonRSLowerProofs.NumeratorMarkClippingEmpirical
