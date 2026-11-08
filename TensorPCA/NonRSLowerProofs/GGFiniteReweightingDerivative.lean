-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteFirstJetPadding
public import TensorPCA.NonRSLowerProofs.GGFiniteEmpiricalNormalizer
public import TensorPCA.NonRSLowerProofs.GGFiniteReplicaSnocIntegration
public import TensorPCA.GaussianSpinInterpolationProofs
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Finite-spin reweighting under a disorder ensemble. The index n follows the first-jet
convention with n+1 old anchors.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteReweightingDerivative
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet GGFiniteFirstJetPadding
open GGFiniteEmpiricalNormalizer GaussianSpinInterpolation
open scoped BigOperators ProbabilityTheory Topology
noncomputable section
variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

def reweightingNormalizer (n : ℕ) (G : Kernel Ω V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (t : ℝ) (w : Ω) (old : Fin (n+1) → V) : ℝ :=
  normalizer (G w) (score n overlap psi old) t

def reweightingExpectation (n : ℕ) (d : Measure Ω) (G : Kernel Ω V)
    (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ)
    (Phi : (Fin (n+1) → V) → ℝ) (t : ℝ) : ℝ :=
  ∫ w, (∫ old : Fin (n+1) → V,
    Phi old*Real.exp (t*(∑ l, correctedScore n overlap psi means old l))/
      (reweightingNormalizer n G overlap psi t w old)^(n+1)
    ∂Measure.pi (fun _ : Fin (n+1) ↦ G w)) ∂d

private theorem bounded_normalizer_hasDerivAt (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hB : 0≤B) (hb : ∀ v, |S v|≤B) (t : ℝ) :
    HasDerivAt (fun u ↦ normalizer nu S u) (∫ v, S v*Real.exp (t*S v) ∂nu) t := by
  let L : V → ℝ →L[ℝ] ℝ := fun v ↦ S v • ContinuousLinearMap.id ℝ ℝ
  have hL : Measurable L := hS.smul measurable_const
  have hbL : ∀ᵐ v ∂nu, ‖L v‖≤B := Eventually.of_forall (fun v ↦ by
    simpa only [L,norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_id,mul_one] using hb v)
  have hb1 : ∀ᵐ v ∂nu, |(1 : ℝ)|≤1 ∧ ‖L v‖≤B := hbL.mono (fun _ hv ↦ ⟨by norm_num,hv⟩)
  have H := (moment_hasFDerivAt nu (fun _ ↦ 1) L measurable_const hL zero_le_one hB hb1 t).hasDerivAt
  rw [momentDerivative_apply nu (fun _ ↦ 1) L measurable_const hL hb1] at H
  have heq : GaussianSpinInterpolation.moment nu (fun _ ↦ 1) L=(fun u ↦ normalizer nu S u) := by
    funext u
    simp only [normalizer,GaussianSpinInterpolation.moment,weight,L,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,one_mul,mul_comm]
  rw [heq] at H
  simpa only [normalizer,GaussianSpinInterpolation.moment,weight,L,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,one_mul,mul_one,mul_comm] using H

private theorem bounded_exp_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hb : ∀ v, |S v|≤B) (t : ℝ) :
    Integrable (fun v ↦ Real.exp (t*S v)) nu := by
  apply Integrable.of_bound (hS.const_mul t).exp.aestronglyMeasurable (Real.exp (|t| *B))
  exact Eventually.of_forall (fun v ↦ by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (exp_score_bounds hb t v).2)

private theorem scalar_reweight_hasDerivAt (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hB : 0≤B) (hb : ∀ v, |S v|≤B)
    (H phi : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun u ↦ phi*Real.exp (u*H)/(normalizer nu S u)^k)
      ((phi*Real.exp (t*H)/(normalizer nu S t)^k)*
        (H-(k : ℝ)*(∫ v, S v*Real.exp (t*S v) ∂nu)/normalizer nu S t)) t := by
  have hz : 0<normalizer nu S t := (Real.exp_pos _).trans_le (normalizer_mem_Icc nu hS hb t).1
  have hdZ := bounded_normalizer_hasDerivAt nu hS hB hb t
  have hpow := (hasDerivAt_zpow (-(k : ℤ)) (normalizer nu S t) (Or.inl hz.ne')).comp t hdZ
  have hnum := (((hasDerivAt_id t).mul_const H).exp).const_mul phi
  have hd := hnum.mul hpow
  have he : (-(k : ℤ))-1= -((k+1 : ℕ) : ℤ) := by omega
  convert hd using 1
  · funext u
    simp only [Function.comp_def,id_eq,Pi.mul_apply,zpow_neg,zpow_natCast,div_eq_mul_inv]
  · simp only [Function.comp_def,id_eq,Pi.mul_apply,one_mul,he,Int.cast_neg,Int.cast_natCast,zpow_neg,zpow_natCast]
    rw [pow_succ]
    field_simp [hz.ne'] <;> ring

private theorem scalar_derivative_eq_fresh (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hb : ∀ v, |S v|≤B)
    (H phi : ℝ) (k : ℕ) (t : ℝ) :
    (phi*Real.exp (t*H)/(normalizer nu S t)^k)*
        (H-(k : ℝ)*(∫ v, S v*Real.exp (t*S v) ∂nu)/normalizer nu S t)=
      ∫ v, phi*(H-(k : ℝ)*S v)*Real.exp (t*(H+S v))/(normalizer nu S t)^(k+1) ∂nu := by
  have hz : 0<normalizer nu S t := (Real.exp_pos _).trans_le (normalizer_mem_Icc nu hS hb t).1
  have hI := bounded_exp_integrable nu hS hb t
  have hSI : Integrable (fun v ↦ S v*Real.exp (t*S v)) nu := hI.bdd_mul hS.aestronglyMeasurable
    (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using hb v))
  have he : (fun v ↦ phi*(H-(k : ℝ)*S v)*Real.exp (t*(H+S v))/(normalizer nu S t)^(k+1))=
      (fun v ↦ (phi*Real.exp (t*H)/(normalizer nu S t)^(k+1))*
        (H*Real.exp (t*S v)-(k : ℝ)*(S v*Real.exp (t*S v)))) := by
    funext v
    rw [mul_add,Real.exp_add]
    ring
  rw [he,integral_const_mul,integral_sub (hI.const_mul H) (hSI.const_mul (k : ℝ)),
    integral_const_mul,integral_const_mul]
  change _=(phi*Real.exp (t*H)/(normalizer nu S t)^(k+1))*
    (H*normalizer nu S t-(k : ℝ)*(∫ v, S v*Real.exp (t*S v) ∂nu))
  rw [pow_succ]
  field_simp [hz.ne']

theorem score_joint_measurable (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2)) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) :
    Measurable (fun p : (Fin (n+1) → V)×V ↦ score n overlap psi p.1 p.2) := by
  unfold GGFiniteFirstJet.score
  apply Finset.measurable_sum
  intro j _
  have hp : Measurable (fun p : (Fin (n+1) → V)×V ↦ (p.1 j,p.2)) :=
    ((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd
  have hr : Measurable (fun p : (Fin (n+1) → V)×V ↦ overlap (p.1 j) p.2) := by
    simpa only [Function.comp_def] using hR.comp hp
  exact (hpsi j).comp hr

theorem corrected_sum_measurable (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2)) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (means : Fin (n+1) → ℝ) :
    Measurable (fun old : Fin (n+1) → V ↦ ∑ l, correctedScore n overlap psi means old l) := by
  apply Finset.measurable_sum
  intro l _
  have h1 : Measurable (fun old : Fin (n+1) → V ↦ GGFiniteFirstJet.score n overlap psi old (old l)) := by
    simpa only [Function.comp_def,id_eq] using
      (score_joint_measurable n hR hpsi).comp (measurable_id.prodMk (measurable_pi_apply l))
  have hp : Measurable (fun old : Fin (n+1) → V ↦ (old l,old l)) :=
    (measurable_pi_apply l).prodMk (measurable_pi_apply l)
  have hr : Measurable (fun old : Fin (n+1) → V ↦ overlap (old l) (old l)) := by
    simpa only [Function.comp_def] using hR.comp hp
  have h2 : Measurable (fun old : Fin (n+1) → V ↦ psi l (overlap (old l) (old l))) :=
    (hpsi l).comp hr
  exact (h1.sub h2).add measurable_const

theorem corrected_sum_abs_le (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means B : Fin (n+1) → ℝ)
    (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j) (old : Fin (n+1) → V) :
    |∑ l, correctedScore n overlap psi means old l|≤((n : ℝ)+1)*(∑ j, B j) := by
  calc
    _ ≤ ∑ l, |correctedScore n overlap psi means old l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin (n+1), (∑ j, B j) := Finset.sum_le_sum (fun l _ ↦ correctedScore_abs_le n overlap psi means B hb hm old l)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

theorem normalizer_joint_measurable (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j)) :
    Measurable (fun p : ℝ×(Ω×(Fin (n+1) → V)) ↦ reweightingNormalizer n G overlap psi p.1 p.2.1 p.2.2) ∧
    Measurable (fun p : ℝ×(Ω×(Fin (n+1) → V)) ↦ ∫ v,
      score n overlap psi p.2.2 v*Real.exp (p.1*score n overlap psi p.2.2 v) ∂G p.2.1) := by
  let P := ℝ×(Ω×(Fin (n+1) → V))
  let K : Kernel P V := G.comap (fun p : P ↦ p.2.1) measurable_snd.fst
  have hS : Measurable (fun p : P×V ↦ score n overlap psi p.1.2.2 p.2) :=
    (score_joint_measurable n hR hpsi).comp (measurable_fst.snd.snd.prodMk measurable_snd)
  have he := (measurable_fst.fst.mul hS).exp
  have H0 := (he.stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable
  have H1 := ((hS.mul he).stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable
  exact ⟨H0,H1⟩

theorem reweightingNormalizer_pos (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (t : ℝ) (w : Ω) (old : Fin (n+1) → V) :
    0<reweightingNormalizer n G overlap psi t w old := by
  have hm : Measurable (score n overlap psi old) :=
    (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
  have H := normalizer_mem_Icc (G w) hm (score_abs_le n overlap psi B hb old) t
  exact (Real.exp_pos _).trans_le H.1

theorem reweightingNormalizer_snoc_zero (G : Kernel Ω V) (n : ℕ)
    (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ) (t : ℝ) (w : Ω)
    (s : Fin (n+2) → V) :
    reweightingNormalizer (n+1) G overlap (Fin.snoc psi (fun _ ↦ 0)) t w s=
      reweightingNormalizer n G overlap psi t w (initial s) := by
  unfold reweightingNormalizer normalizer
  simp_rw [score_snoc_zero]

private theorem scalar_reweight_abs_le (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hb : ∀ v, |S v|≤B)
    {H phi K C : ℝ} (hH : |H|≤K) (hp : |phi|≤C) (k : ℕ) (t : ℝ) :
    |phi*Real.exp (t*H)/(normalizer nu S t)^k|≤
      C*Real.exp (|t| *(K+(k : ℝ)*B)) := by
  have hZ := (normalizer_mem_Icc nu hS hb t).1
  have hZ0 : 0<normalizer nu S t := (Real.exp_pos _).trans_le hZ
  have hPow : Real.exp (-(|t| *B))^k≤normalizer nu S t^k :=
    by simpa only [neg_mul] using pow_le_pow_left₀ (Real.exp_nonneg _) hZ k
  have hC : 0≤C := (abs_nonneg _).trans hp
  have hExp : Real.exp (t*H)≤Real.exp (|t| *K) := by
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans ((by rw [abs_mul] : |t*H|=|t| *|H|) ▸
      mul_le_mul_of_nonneg_left hH (abs_nonneg t))
  rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (pow_pos hZ0 _)]
  calc
    _ ≤ (C*Real.exp (|t| *K))/(Real.exp (-(|t| *B))^k) :=
      div_le_div₀ (mul_nonneg hC (Real.exp_nonneg _))
        (mul_le_mul hp hExp (Real.exp_nonneg _) hC)
        (pow_pos (Real.exp_pos _) _) hPow
    _ = _ := by
      rw [← Real.exp_nat_mul,mul_div_assoc,← Real.exp_sub]
      congr 2
      ring

private theorem scalar_derivative_abs_le (nu : Measure V) [IsProbabilityMeasure nu]
    {S : V → ℝ} (hS : Measurable S) {B : ℝ} (hB : 0≤B) (hb : ∀ v, |S v|≤B)
    {H phi K C : ℝ} (hH : |H|≤K) (hp : |phi|≤C) (k : ℕ) (t : ℝ) :
    |(phi*Real.exp (t*H)/(normalizer nu S t)^k)*
        (H-(k : ℝ)*(∫ v, S v*Real.exp (t*S v) ∂nu)/normalizer nu S t)|≤
      (C*(K+(k : ℝ)*B))*Real.exp (|t| *(K+B+((k+1 : ℕ) : ℝ)*B)) := by
  rw [scalar_derivative_eq_fresh nu hS hb]
  have hK : 0≤K := (abs_nonneg _).trans hH
  have hC : 0≤C := (abs_nonneg _).trans hp
  have hkb : 0≤K+(k : ℝ)*B := add_nonneg hK (mul_nonneg (Nat.cast_nonneg _) hB)
  have hbound (v : V) :
      |phi*(H-(k : ℝ)*S v)*Real.exp (t*(H+S v))/(normalizer nu S t)^(k+1)|≤
        (C*(K+(k : ℝ)*B))*Real.exp (|t| *(K+B+((k+1 : ℕ) : ℝ)*B)) := by
    have hHS : |H+S v|≤K+B := (abs_add_le _ _).trans (add_le_add hH (hb v))
    have hInsert : |H-(k : ℝ)*S v|≤K+(k : ℝ)*B := by
      calc
        _ ≤ |H|+|(k : ℝ)*S v| := abs_sub _ _
        _ = |H|+(k : ℝ)*|S v| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ)≤k)]
        _ ≤ _ := add_le_add hH (mul_le_mul_of_nonneg_left (hb v) (Nat.cast_nonneg _))
    have hp' : |phi*(H-(k : ℝ)*S v)|≤C*(K+(k : ℝ)*B) := by
      rw [abs_mul]
      exact mul_le_mul hp hInsert (abs_nonneg _) hC
    exact scalar_reweight_abs_le nu hS hb hHS hp' (k+1) t
  have HH := norm_integral_le_of_norm_le_const (μ := nu)
    (f := fun v ↦ phi*(H-(k : ℝ)*S v)*Real.exp (t*(H+S v))/(normalizer nu S t)^(k+1))
    (C := (C*(K+(k : ℝ)*B))*Real.exp (|t| *(K+B+((k+1 : ℕ) : ℝ)*B)))
    (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using hbound v))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using HH

/-- Differentiation of the disorder-averaged bounded reweighting. The fixed pair means
need only satisfy the same bounds as their tests.
-/
theorem reweightingExpectation_hasDerivAt_quotient
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C) (t0 : ℝ) :
    HasDerivAt (reweightingExpectation n d G overlap psi means Phi)
      (∫ w, (∫ old : Fin (n+1) → V,
        (Phi old*Real.exp (t0*(∑ l, correctedScore n overlap psi means old l))/
          (reweightingNormalizer n G overlap psi t0 w old)^(n+1))*
          ((∑ l, correctedScore n overlap psi means old l)-((n+1 : ℕ) : ℝ)*
            (∫ v, score n overlap psi old v*Real.exp (t0*score n overlap psi old v) ∂G w)/
              reweightingNormalizer n G overlap psi t0 w old)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ G w)) ∂d) t0 := by
  let P := Ω×(Fin (n+1) → V)
  let mu : Measure P := d ⊗ₘ iid G (n+1)
  let b : ℝ := ∑ j, B j
  let K : ℝ := ((n : ℝ)+1)*b
  let H : (Fin (n+1) → V) → ℝ := fun old ↦ ∑ l, correctedScore n overlap psi means old l
  let Z : ℝ → P → ℝ := fun t p ↦ reweightingNormalizer n G overlap psi t p.1 p.2
  let Z1 : ℝ → P → ℝ := fun t p ↦ ∫ v, score n overlap psi p.2 v*Real.exp (t*score n overlap psi p.2 v) ∂G p.1
  let W : ℝ → P → ℝ := fun t p ↦ Phi p.2*Real.exp (t*H p.2)/(Z t p)^(n+1)
  let D : ℝ → P → ℝ := fun t p ↦ W t p*(H p.2-((n+1 : ℕ) : ℝ)*Z1 t p/Z t p)
  have hb0 : 0≤b := Finset.sum_nonneg (fun j _ ↦ (abs_nonneg (psi j 0)).trans (hb j 0))
  have hK0 : 0≤K := mul_nonneg (by positivity) hb0
  have hH : Measurable H := corrected_sum_measurable n hR hpsi means
  have hHb (old : Fin (n+1) → V) : |H old|≤K := corrected_sum_abs_le n overlap psi means B hb hm old
  have hS (old : Fin (n+1) → V) : Measurable (score n overlap psi old) :=
    (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
  obtain ⟨hZ,hZ1⟩ := normalizer_joint_measurable G n hR hpsi
  have hW : Measurable (fun p : ℝ×P ↦ W p.1 p.2) :=
    ((hPhi.comp measurable_snd.snd).mul
      (measurable_fst.mul (hH.comp measurable_snd.snd)).exp).div (hZ.pow_const (n+1))
  have hD : Measurable (fun p : ℝ×P ↦ D p.1 p.2) :=
    hW.mul ((hH.comp measurable_snd.snd).sub ((hZ1.const_mul _).div hZ))
  have hWAt (t : ℝ) : Measurable (W t) := hW.comp (measurable_const.prodMk measurable_id)
  have hDAt (t : ℝ) : Measurable (D t) := hD.comp (measurable_const.prodMk measurable_id)
  have hWi (t : ℝ) : Integrable (W t) mu := by
    apply Integrable.of_bound (hWAt t).aestronglyMeasurable
      (C*Real.exp (|t| *(K+((n+1 : ℕ) : ℝ)*b)))
    exact Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs,W,Z,reweightingNormalizer,b] using scalar_reweight_abs_le (G p.1) (hS p.2)
        (score_abs_le n overlap psi B hb p.2) (hHb p.2) (hp p.2) (n+1) t)
  let L : ℝ := K+b+((n+2 : ℕ) : ℝ)*b
  let Q : ℝ := C*(K+((n+1 : ℕ) : ℝ)*b)
  have hL0 : 0≤L := add_nonneg (add_nonneg hK0 hb0) (mul_nonneg (Nat.cast_nonneg _) hb0)
  have hQ0 : 0≤Q := mul_nonneg hC (add_nonneg hK0 (mul_nonneg (Nat.cast_nonneg _) hb0))
  have hDb (t : ℝ) (p : P) : |D t p|≤Q*Real.exp (|t| *L) := by
    simpa only [D,W,Z,Z1,reweightingNormalizer,K,b,H,L,Q,Nat.add_assoc] using
      scalar_derivative_abs_le (G p.1) (hS p.2) hb0
        (score_abs_le n overlap psi B hb p.2) (hHb p.2) (hp p.2) (n+1) t
  have hDi (t : ℝ) : Integrable (D t) mu := by
    exact Integrable.of_bound (hDAt t).aestronglyMeasurable (Q*Real.exp (|t| *L))
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hDb t p))
  have hdiff (t : ℝ) (p : P) : HasDerivAt (fun u ↦ W u p) (D t p) t :=
    scalar_reweight_hasDerivAt (G p.1) (hS p.2) hb0
      (score_abs_le n overlap psi B hb p.2) (H p.2) (Phi p.2) (n+1) t
  have HD : HasDerivAt (fun t ↦ ∫ p, W t p ∂mu) (∫ p, D t0 p ∂mu) t0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := W) (F' := D) (s := Metric.ball t0 1)
      (bound := fun _ ↦ Q*Real.exp ((|t0|+1)*L))
      (Metric.ball_mem_nhds t0 zero_lt_one) ?_ (hWi t0) (hDAt t0).aestronglyMeasurable
      ?_ (integrable_const _) ?_).2
    · exact Eventually.of_forall (fun t ↦ (hWAt t).aestronglyMeasurable)
    · exact Eventually.of_forall (fun p t ht ↦ by
        have ht' : |t-t0|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using ht
        have ht0 : |t|≤|t0|+1 := by have := abs_sub_abs_le_abs_sub t t0; linarith
        rw [Real.norm_eq_abs]
        exact (hDb t p).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht0 hL0)) hQ0))
    · exact Eventually.of_forall (fun p t _ ↦ hdiff t p)
  have he (t : ℝ) : (∫ p, W t p ∂mu)=reweightingExpectation n d G overlap psi means Phi t := by
    rw [Measure.integral_compProd (hWi t)]
    simp only [iid_apply]
    rfl
  have he' : (∫ p, D t0 p ∂mu)=
      ∫ w, (∫ old : Fin (n+1) → V,
        (Phi old*Real.exp (t0*(∑ l, correctedScore n overlap psi means old l))/
          (reweightingNormalizer n G overlap psi t0 w old)^(n+1))*
          ((∑ l, correctedScore n overlap psi means old l)-((n+1 : ℕ) : ℝ)*
            (∫ v, score n overlap psi old v*Real.exp (t0*score n overlap psi old v) ∂G w)/
              reweightingNormalizer n G overlap psi t0 w old)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ G w)) ∂d := by
    rw [Measure.integral_compProd (hDi t0)]
    simp only [iid_apply]
    rfl
  simpa only [he,he'] using HD

/-- The derivative adds one fresh iid replica and the finite GG insertion, while padding
the old tests by zero. This identity alone makes no assertion of invariance.
-/
theorem reweightingExpectation_hasDerivAt
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    (hm : ∀ j, |means j|≤B j) {Phi : (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C) (t0 : ℝ) :
    HasDerivAt (reweightingExpectation n d G overlap psi means Phi)
      (reweightingExpectation (n+1) d G overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0)
        (fun s ↦ Phi (initial s)*firstJetInsertion n overlap psi means s) t0) t0 := by
  let b : ℝ := ∑ j, B j
  let K : ℝ := ((n : ℝ)+1)*b
  let H : (Fin (n+1) → V) → ℝ := fun old ↦ ∑ l, correctedScore n overlap psi means old l
  let Z : Ω → (Fin (n+1) → V) → ℝ := fun w old ↦ reweightingNormalizer n G overlap psi t0 w old
  let D0 : Ω → (Fin (n+1) → V) → ℝ := fun w old ↦
    (Phi old*Real.exp (t0*H old)/(Z w old)^(n+1))*
      (H old-((n+1 : ℕ) : ℝ)*(∫ v, score n overlap psi old v*Real.exp (t0*score n overlap psi old v) ∂G w)/Z w old)
  have HD := reweightingExpectation_hasDerivAt_quotient d G n hR hpsi means B hb hm hPhi hC hp t0
  change HasDerivAt _ (∫ w, ∫ old, D0 w old ∂Measure.pi (fun _ : Fin (n+1) ↦ G w) ∂d) t0 at HD
  have heq : (∫ w, ∫ old, D0 w old ∂Measure.pi (fun _ : Fin (n+1) ↦ G w) ∂d)=
      reweightingExpectation (n+1) d G overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0)
        (fun s ↦ Phi (initial s)*firstJetInsertion n overlap psi means s) t0 := by
    unfold reweightingExpectation
    apply integral_congr_ae
    refine Eventually.of_forall (fun w ↦ ?_)
    let F : (Fin (n+2) → V) → ℝ := fun s ↦
      Phi (initial s)*firstJetInsertion n overlap psi means s*
        Real.exp (t0*(H (initial s)+score n overlap psi (initial s) (s (Fin.last (n+1)))))/
          (Z w (initial s))^(n+2)
    have hi := initial_measurable (V := V) (n+1)
    have hH : Measurable H := corrected_sum_measurable n hR hpsi means
    have hscore : Measurable (fun s : Fin (n+2) → V ↦
        score n overlap psi (initial s) (s (Fin.last (n+1)))) :=
      (score_joint_measurable n hR hpsi).comp (hi.prodMk (measurable_pi_apply _))
    have hZ : Measurable (fun s : Fin (n+2) → V ↦ Z w (initial s)) := by
      exact (normalizer_joint_measurable G n hR hpsi).1.comp
        (measurable_const.prodMk (measurable_const.prodMk hi))
    have hF : Measurable F :=
      (((hPhi.comp hi).mul (firstJetInsertion_measurable n hR hpsi means)).mul
        (((hH.comp hi).add hscore).const_mul t0).exp).div (hZ.pow_const (n+2))
    have hb0 : 0≤b := Finset.sum_nonneg (fun j _ ↦ (abs_nonneg (psi j 0)).trans (hb j 0))
    have hK0 : 0≤K := mul_nonneg (by positivity) hb0
    have hFb (s : Fin (n+2) → V) : |F s|≤
        (C*(2*((n : ℝ)+1)*b))*Real.exp (|t0| *(K+b+((n+2 : ℕ) : ℝ)*b)) := by
      have hs := score_abs_le n overlap psi B hb (initial s) (s (Fin.last (n+1)))
      have hh := corrected_sum_abs_le n overlap psi means B hb hm (initial s)
      have hHS : |H (initial s)+score n overlap psi (initial s) (s (Fin.last (n+1)))|≤K+b :=
        (abs_add_le _ _).trans (add_le_add hh hs)
      have hP : |Phi (initial s)*firstJetInsertion n overlap psi means s|≤C*(2*((n : ℝ)+1)*b) := by
        rw [abs_mul]
        exact mul_le_mul (hp _) (firstJetInsertion_abs_le n overlap psi means B hb hm s) (abs_nonneg _) hC
      have hS : Measurable (score n overlap psi (initial s)) :=
        (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
      exact scalar_reweight_abs_le (G w) hS (score_abs_le n overlap psi B hb (initial s)) hHS hP (n+2) t0
    have hsnoc := GGFiniteReplicaSnocIntegration.integral_pi_snoc (G w) n F hF hFb
    calc
      (∫ old, D0 w old ∂Measure.pi (fun _ : Fin (n+1) ↦ G w))=
          ∫ old : Fin (n+1) → V, ∫ v, F (Fin.snoc old v) ∂G w
            ∂Measure.pi (fun _ : Fin (n+1) ↦ G w) := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun old ↦ ?_)
        have hS : Measurable (score n overlap psi old) :=
          (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
        dsimp only [D0,Z,reweightingNormalizer]
        rw [scalar_derivative_eq_fresh (G w) hS (score_abs_le n overlap psi B hb old)]
        apply integral_congr_ae
        refine Eventually.of_forall (fun v ↦ ?_)
        have he : initial (Fin.snoc old v)=old := by funext j; simp only [initial,Fin.snoc_castSucc]
        simp only [F,he,firstJetInsertion,Fin.snoc_last,Nat.cast_add,Nat.cast_one]
        rfl
      _ = ∫ s, F s ∂Measure.pi (fun _ : Fin (n+2) ↦ G w) := hsnoc.symm
      _ = _ := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun s ↦ ?_)
        dsimp only
        rw [sum_correctedScore_snoc_zero,reweightingNormalizer_snoc_zero]
  rw [heq] at HD
  exact HD


end
end TensorPCA.NonRSLowerProofs.GGFiniteReweightingDerivative
