-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteReweightingDerivative

/-! Exact mass preservation when a zero-test fresh replica is added to the reweighted
ensemble. No GG/invariance premise is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteReweightingPadding
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet GGFiniteFirstJetPadding
open GGFiniteEmpiricalNormalizer GGFiniteReweightingDerivative
open scoped BigOperators ProbabilityTheory
noncomputable section
variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

private theorem scalar_weight_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hb : ∀ v, |S v|≤B)
    {H phi K C : ℝ} (hH : |H|≤K) (hp : |phi|≤C) (k : ℕ) (t : ℝ) :
    |phi*Real.exp (t*H)/(normalizer nu S t)^k|≤C*Real.exp (|t| *(K+(k : ℝ)*B)) := by
  have hZ := (normalizer_mem_Icc nu hS hb t).1
  have hZ0 : 0<normalizer nu S t := (Real.exp_pos _).trans_le hZ
  have hPow : Real.exp (-(|t| *B))^k≤normalizer nu S t^k :=
    by simpa only [neg_mul] using pow_le_pow_left₀ (Real.exp_nonneg _) hZ k
  have hC : 0≤C := (abs_nonneg _).trans hp
  have he : Real.exp (t*H)≤Real.exp (|t| *K) := by
    apply Real.exp_le_exp.mpr
    calc
      t*H ≤ |t*H| := le_abs_self _
      _ = |t| *|H| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (abs_nonneg t)
  rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (pow_pos hZ0 _)]
  calc
    _ ≤ (C*Real.exp (|t| *K))/(Real.exp (-(|t| *B))^k) :=
      div_le_div₀ (mul_nonneg hC (Real.exp_nonneg _))
        (mul_le_mul hp he (Real.exp_nonneg _) hC) (pow_pos (Real.exp_pos _) _) hPow
    _ = _ := by
      rw [← Real.exp_nat_mul,mul_div_assoc,← Real.exp_sub]
      congr 2
      ring

theorem weight_measurable (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means : Fin (n+1) → ℝ) {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) (t : ℝ) :
    Measurable (fun p : Ω×(Fin (n+1) → V) ↦
      Phi p.2*Real.exp (t*(∑ l, correctedScore n overlap psi means p.2 l))/
        (reweightingNormalizer n G overlap psi t p.1 p.2)^(n+1)) := by
  have hH := corrected_sum_measurable n hR hpsi means
  have hZ : Measurable (fun p : Ω×(Fin (n+1) → V) ↦ reweightingNormalizer n G overlap psi t p.1 p.2) :=
    (normalizer_joint_measurable G n hR hpsi).1.comp (measurable_const.prodMk measurable_id)
  exact ((hPhi.comp measurable_snd).mul ((hH.comp measurable_snd).const_mul t).exp).div (hZ.pow_const _)

theorem weight_abs_le (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ} {C : ℝ}
    (hp : ∀ old, |Phi old|≤C) (t : ℝ) (w : Ω) (old : Fin (n+1) → V) :
    |Phi old*Real.exp (t*(∑ l, correctedScore n overlap psi means old l))/
      (reweightingNormalizer n G overlap psi t w old)^(n+1)|≤
        C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)) := by
  have hS : Measurable (score n overlap psi old) :=
    (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
  have H := scalar_weight_bound (G w) hS (score_abs_le n overlap psi B hb old)
    (corrected_sum_abs_le n overlap psi means B hb hm old) (hp old) (n+1) t
  unfold reweightingNormalizer
  convert H using 1 <;> push_cast <;> ring

theorem weight_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hp : ∀ old, |Phi old|≤C) (t : ℝ) :
    Integrable (fun p : Ω×(Fin (n+1) → V) ↦
      Phi p.2*Real.exp (t*(∑ l, correctedScore n overlap psi means p.2 l))/
        (reweightingNormalizer n G overlap psi t p.1 p.2)^(n+1)) (d ⊗ₘ iid G (n+1)) := by
  exact Integrable.of_bound (weight_measurable G n hR hpsi means hPhi t).aestronglyMeasurable
    (C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)))
    (Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs] using (weight_abs_le G n hR hpsi means B hb hm hp t p.1 p.2)))

theorem reweightingExpectation_abs_le_mass (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C) (t : ℝ) :
    |reweightingExpectation n d G overlap psi means Phi t|≤
      C*reweightingExpectation n d G overlap psi means (fun _ ↦ 1) t := by
  let mu := d ⊗ₘ iid G (n+1)
  let W : Ω×(Fin (n+1) → V) → ℝ := fun p ↦
    Real.exp (t*(∑ l, correctedScore n overlap psi means p.2 l))/
      (reweightingNormalizer n G overlap psi t p.1 p.2)^(n+1)
  have hW : Integrable W mu := by
    simpa only [one_mul] using weight_integrable d G n hR hpsi means B hb hm
      (Phi := fun _ ↦ 1) measurable_const (fun _ ↦ by norm_num : ∀ old, |(1 : ℝ)|≤1) t
  have hP : Integrable (fun p ↦ Phi p.2*W p) mu := by
    simpa only [W,mul_div_assoc] using weight_integrable d G n hR hpsi means B hb hm hPhi hp t
  have hW0 (p : Ω×(Fin (n+1) → V)) : 0≤W p :=
    div_nonneg (Real.exp_nonneg _) (pow_nonneg (le_of_lt (reweightingNormalizer_pos G n hR hpsi B hb t p.1 p.2)) _)
  have hEq : reweightingExpectation n d G overlap psi means Phi t=∫ p, Phi p.2*W p ∂mu := by
    rw [Measure.integral_compProd hP]
    simp only [iid_apply,W,mul_div_assoc,reweightingExpectation]
  have hEq1 : reweightingExpectation n d G overlap psi means (fun _ ↦ 1) t=∫ p, W p ∂mu := by
    rw [Measure.integral_compProd hW]
    simp only [iid_apply,W,one_mul,reweightingExpectation]
  rw [hEq,hEq1]
  calc
    _ ≤ ∫ p, |Phi p.2*W p| ∂mu := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := fun p ↦ Phi p.2*W p)
    _ ≤ ∫ p, C*W p ∂mu := by
      apply integral_mono hP.norm (hW.const_mul C)
      intro p
      change |Phi p.2*W p|≤C*W p
      rw [abs_mul,abs_of_nonneg (hW0 p)]
      exact mul_le_mul_of_nonneg_right (hp p.2) (hW0 p)
    _ = _ := integral_const_mul C W

theorem reweightingMass_nonneg (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    (d : Measure Ω) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (t : ℝ) :
    0≤reweightingExpectation n d G overlap psi means (fun _ ↦ 1) t := by
  apply integral_nonneg
  intro w
  apply integral_nonneg
  intro old
  exact div_nonneg (mul_nonneg zero_le_one (Real.exp_nonneg _))
    (pow_nonneg (reweightingNormalizer_pos G n hR hpsi B hb t w old).le _)

theorem reweightingMass_le (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) (t : ℝ) :
    reweightingExpectation n d G overlap psi means (fun _ ↦ 1) t≤
      Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)) := by
  let W : Ω×(Fin (n+1) → V) → ℝ := fun p ↦
    1*Real.exp (t*(∑ l, correctedScore n overlap psi means p.2 l))/
      (reweightingNormalizer n G overlap psi t p.1 p.2)^(n+1)
  have hi : Integrable W (d ⊗ₘ iid G (n+1)) :=
    weight_integrable d G n hR hpsi means B hb hm (Phi := fun _ ↦ 1) measurable_const
      (fun _ ↦ by norm_num : ∀ old, |(1 : ℝ)|≤1) t
  have hbW (p : Ω×(Fin (n+1) → V)) : |W p|≤Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)) := by
    simpa only [W,one_mul] using weight_abs_le G n hR hpsi means B hb hm
      (Phi := fun _ ↦ 1) (fun _ ↦ by norm_num : ∀ old, |(1 : ℝ)|≤1) t p.1 p.2
  have hh := norm_integral_le_of_norm_le_const (μ := d ⊗ₘ iid G (n+1)) (f := W)
    (C := Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)))
    (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hbW p))
  rw [Measure.integral_compProd hi] at hh
  simp only [iid_apply,probReal_univ,mul_one,Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans hh

theorem normalized_fresh_mass (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hb : ∀ v, |S v|≤B) (t : ℝ) :
    (∫ v, Real.exp (t*S v)/normalizer nu S t ∂nu)=1 := by
  rw [integral_div]
  exact div_self ((Real.exp_pos _).trans_le (normalizer_mem_Icc nu hS hb t).1).ne'

/-- The new fresh exponential factor integrates to its exact normalizer. The old
observable and the disorder dependence remain in their laws.
-/
theorem reweightingExpectation_snoc_zero (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hp : ∀ old, |Phi old|≤C) (t : ℝ) :
    reweightingExpectation (n+1) d G overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0)
      (fun s ↦ Phi (initial s)) t=reweightingExpectation n d G overlap psi means Phi t := by
  unfold reweightingExpectation
  apply integral_congr_ae
  refine Eventually.of_forall (fun w ↦ ?_)
  let H : (Fin (n+1) → V) → ℝ := fun old ↦ ∑ l, correctedScore n overlap psi means old l
  let Z : (Fin (n+1) → V) → ℝ := fun old ↦ reweightingNormalizer n G overlap psi t w old
  let F : (Fin (n+2) → V) → ℝ := fun s ↦
    Phi (initial s)*Real.exp (t*(H (initial s)+score n overlap psi (initial s) (s (Fin.last (n+1)))))/
      (Z (initial s))^(n+2)
  have hi := initial_measurable (V := V) (n+1)
  have hH : Measurable H := corrected_sum_measurable n hR hpsi means
  have hscore : Measurable (fun s : Fin (n+2) → V ↦ score n overlap psi (initial s) (s (Fin.last (n+1)))) :=
    (score_joint_measurable n hR hpsi).comp (hi.prodMk (measurable_pi_apply _))
  have hZ : Measurable (fun s : Fin (n+2) → V ↦ Z (initial s)) :=
    (normalizer_joint_measurable G n hR hpsi).1.comp
      (measurable_const.prodMk (measurable_const.prodMk hi))
  have hF : Measurable F := ((hPhi.comp hi).mul (((hH.comp hi).add hscore).const_mul t).exp).div (hZ.pow_const _)
  have hFb (s : Fin (n+2) → V) : |F s|≤
      C*Real.exp (|t| *((((n : ℝ)+1)*(∑ j, B j))+(∑ j, B j)+((n+2 : ℕ) : ℝ)*(∑ j, B j))) := by
    have hs := score_abs_le n overlap psi B hb (initial s) (s (Fin.last (n+1)))
    have hh := corrected_sum_abs_le n overlap psi means B hb hm (initial s)
    have hHS := (abs_add_le (H (initial s)) (score n overlap psi (initial s) (s (Fin.last (n+1))))).trans (add_le_add hh hs)
    have hS : Measurable (score n overlap psi (initial s)) :=
      (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
    exact scalar_weight_bound (G w) hS (score_abs_le n overlap psi B hb (initial s)) hHS (hp _) (n+2) t
  have hsnoc := GGFiniteReplicaSnocIntegration.integral_pi_snoc (G w) n F hF hFb
  calc
    _ = ∫ s, F s ∂Measure.pi (fun _ : Fin (n+2) ↦ G w) := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun s ↦ ?_)
      dsimp only
      rw [sum_correctedScore_snoc_zero,reweightingNormalizer_snoc_zero]
    _ = ∫ old : Fin (n+1) → V, ∫ v, F (Fin.snoc old v) ∂G w
        ∂Measure.pi (fun _ : Fin (n+1) ↦ G w) := hsnoc
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun old ↦ ?_)
      have hS : Measurable (score n overlap psi old) :=
        (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
      have hz : 0<Z old := reweightingNormalizer_pos G n hR hpsi B hb t w old
      have he : (fun v ↦ F (Fin.snoc old v))=(fun v ↦
          (Phi old*Real.exp (t*H old)/(Z old)^(n+1))*(Real.exp (t*score n overlap psi old v)/(Z old))) := by
        funext v
        have hinit : initial (Fin.snoc old v)=old := by funext j; simp only [initial,Fin.snoc_castSucc]
        simp only [F,hinit,Fin.snoc_last,mul_add,Real.exp_add]
        rw [show n+2=(n+1)+1 by omega,pow_succ]
        field_simp [hz.ne'] <;> ring
      dsimp only
      rw [he,integral_const_mul]
      have hnorm := normalized_fresh_mass (G w) hS (score_abs_le n overlap psi B hb old) t
      change (Phi old*Real.exp (t*H old)/(Z old)^(n+1))*
        (∫ v, Real.exp (t*score n overlap psi old v)/normalizer (G w) (score n overlap psi old) t ∂G w)=_
      rw [hnorm,mul_one]


end
end TensorPCA.NonRSLowerProofs.GGFiniteReweightingPadding
