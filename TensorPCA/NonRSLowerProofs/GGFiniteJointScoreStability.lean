-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteOverlapScoreStability
public import TensorPCA.NonRSLowerProofs.GGFiniteReplicaSnocIntegration
public import TensorPCA.NonRSLowerProofs.GGFiniteReplicaWeightMoments

/-! Exact joint-disorder transports of the own-pair-law score estimates. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteJointScoreStability
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet GGFiniteOverlapScoreStability
open scoped BigOperators
noncomputable section
variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

def integrand (n : ℕ) (G : Kernel Ω V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ)
    (Phi : (Fin (n+1) → V) → ℝ) (b : ((Fin (n+1) → V)×V) → ℝ)
    (chi : ℝ → ℝ) (t : ℝ) (p : Ω×(Fin (n+1) → V)) : ℝ :=
  (Phi p.2*Real.exp (t*(∑ l, correctedScore n overlap psi means p.2 l))/
    (GGFiniteReweightingDerivative.reweightingNormalizer n G overlap psi t p.1 p.2)^(n+1))*
      chi (GGFiniteReplicaWeightMoments.tiltedWeightMean n G overlap psi b t p.1 p.2)

def observable (d : Measure Ω) (G : Kernel Ω V) (n : ℕ) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (Phi : (Fin (n+1) → V) → ℝ)
    (b : ((Fin (n+1) → V)×V) → ℝ) (chi : ℝ → ℝ) (t : ℝ) : ℝ :=
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  ∫ p, integrand n G overlap psi (fun j ↦ ∫ r, psi j r ∂rho) Phi b chi t p ∂(d ⊗ₘ iid G (n+1))

theorem integrand_measurable (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j)) (means : Fin (n+1) → ℝ)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi)
    {b : ((Fin (n+1) → V)×V) → ℝ} (hb : Measurable b) {chi : ℝ → ℝ} (hchi : Measurable chi) (t : ℝ) :
    Measurable (integrand n G overlap psi means Phi b chi t) := by
  convert (GGFiniteReweightingPadding.weight_measurable G n hR hpsi means hPhi t).mul
    (hchi.comp (GGFiniteReplicaWeightMoments.tiltedWeightMean_measurable G n hR hpsi hb t)) using 1 <;> rfl

theorem integrand_abs_le (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} {C : ℝ} (hp : ∀ old, |Phi old|≤C)
    (b : ((Fin (n+1) → V)×V) → ℝ) {chi : ℝ → ℝ} (hchi : ∀ z, |chi z|≤1)
    (t : ℝ) (p : Ω×(Fin (n+1) → V)) :
    |integrand n G overlap psi means Phi b chi t p|≤
      C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)) := by
  unfold integrand
  rw [abs_mul]
  exact ((mul_le_mul_of_nonneg_left (hchi _) (abs_nonneg _)).trans_eq (mul_one _)).trans
    (GGFiniteReweightingPadding.weight_abs_le G n hR hpsi means B hb hm hp t p.1 p.2)

theorem integrand_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) {C : ℝ} (hp : ∀ old, |Phi old|≤C)
    {b : ((Fin (n+1) → V)×V) → ℝ} (hbM : Measurable b)
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) (t : ℝ) :
    Integrable (integrand n G overlap psi means Phi b chi t) (d ⊗ₘ iid G (n+1)) := by
  exact Integrable.of_bound (integrand_measurable G n hR hpsi means hPhi hbM hchiM t).aestronglyMeasurable
    (C*Real.exp (2*((n : ℝ)+1)*|t| *(∑ j, B j)))
    (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using integrand_abs_le G n hR hpsi means B hb hm hp b hchi t p))

private theorem integrand_sub_bound (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (a a' B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j)
    (ha : ∀ j, |a j|≤B j) (ha' : ∀ j, |a' j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    {b : ((Fin (n+1) → V)×V) → ℝ} (hbM : Measurable b) (hb0 : ∀ q, 0≤b q) (hb1 : ∀ q, b q≤1)
    {chi : ℝ → ℝ} (hchi : ∀ z, |chi z|≤1) {L : ℝ} (hL : 0≤L)
    (hLip : ∀ x y, |chi x-chi y|≤L*|x-y|) (t : ℝ) (p : Ω×(Fin (n+1) → V)) :
    |integrand n G overlap psi a Phi b chi t p-integrand n G overlap phi a' Phi b chi t p|≤
      (C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j)))*
        (|(∑ l, correctedScore n overlap psi a p.2 l)-(∑ l, correctedScore n overlap phi a' p.2 l)|+
          (((n : ℝ)+1)+2*L)*(∫ z, |score n overlap psi p.2 z-score n overlap phi p.2 z| ∂G p.1)) := by
  let M := ∑ j, B j
  let k : ℝ := (n : ℝ)+1
  let S := score n overlap psi p.2
  let S' := score n overlap phi p.2
  let H := ∑ l, correctedScore n overlap psi a p.2 l
  let H' := ∑ l, correctedScore n overlap phi a' p.2 l
  let D := Real.exp (t*H)/(GGFiniteEmpiricalNormalizer.normalizer (G p.1) S t)^(n+1)
  let D' := Real.exp (t*H')/(GGFiniteEmpiricalNormalizer.normalizer (G p.1) S' t)^(n+1)
  let U := GGFiniteReplicaWeightMoments.tiltedWeightMean n G overlap psi b t p.1 p.2
  let U' := GGFiniteReplicaWeightMoments.tiltedWeightMean n G overlap phi b t p.1 p.2
  let E := ∫ z, |S z-S' z| ∂G p.1
  let K := |t| *Real.exp ((2*k+2)*|t| *M)
  have hM : 0≤M := Finset.sum_nonneg (fun j _ ↦ (abs_nonneg (psi j 0)).trans (hpb j 0))
  have hS : Measurable S := (GGFiniteReweightingDerivative.score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
  have hS' : Measurable S' := (GGFiniteReweightingDerivative.score_joint_measurable n hR hphi).comp (measurable_const.prodMk measurable_id)
  have hSb : ∀ z, |S z|≤M := score_abs_le n overlap psi B hpb p.2
  have hS'b : ∀ z, |S' z|≤M := score_abs_le n overlap phi B hfb p.2
  have hH : |H|≤((n+1 : ℕ) : ℝ)*M := by
    simpa only [Nat.cast_add,Nat.cast_one] using GGFiniteReweightingDerivative.corrected_sum_abs_le n overlap psi a B hpb ha p.2
  have hH' : |H'|≤((n+1 : ℕ) : ℝ)*M := by
    simpa only [Nat.cast_add,Nat.cast_one] using GGFiniteReweightingDerivative.corrected_sum_abs_le n overlap phi a' B hfb ha' p.2
  have hD : |D-D'|≤K*(|H-H'|+k*E) := by
    simpa only [D,D',K,k,E,Nat.cast_add,Nat.cast_one] using
      GGFiniteTiltStability.root_density_sub_le (G p.1) hS hS' hM hSb hS'b (n+1) hH hH' t
  have hD' : |D'|≤Real.exp (2*k*|t| *M) := by
    simpa only [D',H',k,M,one_mul,GGFiniteReweightingDerivative.reweightingNormalizer]
      using GGFiniteReweightingPadding.weight_abs_le G n hR hphi a' B hfb ha'
        (Phi := fun _ ↦ 1) (fun _ ↦ by norm_num : ∀ old, |(1 : ℝ)|≤1) t p.1 p.2
  have hbSlice : Measurable (fun z ↦ b (p.2,z)) := hbM.comp (measurable_const.prodMk measurable_id)
  have hU : |U-U'|≤(2*|t| *Real.exp (2*|t| *M))*E := by
    simpa only [U,U',GGFiniteReplicaWeightMoments.tiltedWeightMean,
      GGFiniteReweightingDerivative.reweightingNormalizer,integral_div] using
        GGFiniteTiltStability.normalized_mean_sub_le (G p.1) hS hS' hbSlice hSb hS'b
          (fun z ↦ hb0 _) (fun z ↦ hb1 _) t
  have hFirst : |(D-D')*chi U|≤K*(|H-H'|+k*E) := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left (hchi U) (abs_nonneg _)).trans_eq (mul_one _)).trans hD
  have hSecond : |D'*(chi U-chi U')|≤(2*L*K)*E := by
    rw [abs_mul]
    have hChi := (hLip U U').trans (mul_le_mul_of_nonneg_left hU hL)
    calc
      _ ≤ Real.exp (2*k*|t| *M)*(L*((2*|t| *Real.exp (2*|t| *M))*E)) :=
        mul_le_mul hD' hChi (abs_nonneg _) (Real.exp_nonneg _)
      _ = _ := by
        dsimp only [K]
        rw [show (2*k+2)*|t| *M=(2*k*|t| *M)+(2*|t| *M) by ring,Real.exp_add]
        ring
  have hBracket : |(D-D')*chi U+D'*(chi U-chi U')|≤K*(|H-H'|+(k+2*L)*E) :=
    (abs_add_le _ _).trans ((add_le_add hFirst hSecond).trans_eq (by ring))
  have he : integrand n G overlap psi a Phi b chi t p-integrand n G overlap phi a' Phi b chi t p=
      Phi p.2*((D-D')*chi U+D'*(chi U-chi U')) := by
    dsimp only [integrand,D,D',U,U',H,H',S,S',GGFiniteReweightingDerivative.reweightingNormalizer]
    ring
  rw [he,abs_mul]
  have HH := mul_le_mul (hp p.2) hBracket (abs_nonneg _) hC
  convert HH using 1 <;> ring

theorem joint_snd_hasLaw (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (m : ℕ) :
    HasLaw Prod.snd (law d G m) (d ⊗ₘ iid G m) where
  aemeasurable := measurable_snd.aemeasurable
  map_eq := by
    change (d ⊗ₘ iid G m).snd=law d G m
    rw [Measure.snd_compProd]
    rfl

theorem corrected_sum_joint_l1 (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j) :
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    let a := fun j ↦ ∫ r, psi j r ∂rho
    let a' := fun j ↦ ∫ r, phi j r ∂rho
    Integrable (fun p : Ω×(Fin (n+1) → V) ↦ |(∑ l, correctedScore n overlap psi a p.2 l)-
      (∑ l, correctedScore n overlap phi a' p.2 l)|) (d ⊗ₘ iid G (n+1)) ∧
      (∫ p : Ω×(Fin (n+1) → V), |(∑ l, correctedScore n overlap psi a p.2 l)-
        (∑ l, correctedScore n overlap phi a' p.2 l)| ∂(d ⊗ₘ iid G (n+1)))≤
          ((n : ℝ)+1)*(∑ j, ∫ r, |psi j r-phi j r| ∂rho) := by
  have H := corrected_sum_difference_l1 d G n hR psi phi hpsi hphi B hpb hfb
  have HL := joint_snd_hasLaw d G (n+1)
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def] using HL.integrable_comp H.1
  · exact (HL.integral_comp H.1.aestronglyMeasurable).trans_le H.2

theorem fresh_conditional_joint_l1 (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j) :
    let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
    Integrable (fun p : Ω×(Fin (n+1) → V) ↦ ∫ z,
      |score n overlap psi p.2 z-score n overlap phi p.2 z| ∂G p.1) (d ⊗ₘ iid G (n+1)) ∧
      (∫ p : Ω×(Fin (n+1) → V), (∫ z,
        |score n overlap psi p.2 z-score n overlap phi p.2 z| ∂G p.1) ∂(d ⊗ₘ iid G (n+1)))≤
          ∑ j, ∫ r, |psi j r-phi j r| ∂rho := by
  let raw : ((Fin (n+1) → V)×V) → ℝ := fun p ↦ |score n overlap psi p.1 p.2-score n overlap phi p.1 p.2|
  have hRaw : Measurable raw := by
    convert continuous_abs.measurable.comp
      ((GGFiniteReweightingDerivative.score_joint_measurable n hR hpsi).sub
        (GGFiniteReweightingDerivative.score_joint_measurable n hR hphi)) using 1 <;> rfl
  have hRb (old : Fin (n+1) → V) (z : V) : raw (old,z)≤2*(∑ j, B j) := by
    exact (abs_sub _ _).trans (by linarith [score_abs_le n overlap psi B hpb old z,score_abs_le n overlap phi B hfb old z])
  let kap : Kernel (Ω×(Fin (n+1) → V)) V := G.comap Prod.fst measurable_fst
  have hCM : Measurable (fun p : Ω×(Fin (n+1) → V) ↦ ∫ z, raw (p.2,z) ∂G p.1) := by
    simpa only [kap,Kernel.comap_apply,Function.comp_def] using
      ((hRaw.comp (measurable_fst.snd.prodMk measurable_snd)).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable
  have hCb (p : Ω×(Fin (n+1) → V)) : |∫ z, raw (p.2,z) ∂G p.1|≤2*(∑ j, B j) := by
    have H := norm_integral_le_of_norm_le_const (μ := G p.1) (f := fun z ↦ raw (p.2,z))
      (C := 2*(∑ j, B j)) (Eventually.of_forall (fun z ↦ by
        simpa only [raw,Real.norm_eq_abs,abs_abs] using hRb p.2 z))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hCI : Integrable (fun p : Ω×(Fin (n+1) → V) ↦ ∫ z, raw (p.2,z) ∂G p.1) (d ⊗ₘ iid G (n+1)) :=
    Integrable.of_bound hCM.aestronglyMeasurable (2*(∑ j, B j))
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hCb p))
  let f : Ω×(Fin (n+2) → V) → ℝ := fun p ↦ raw (initial p.2,p.2 (Fin.last (n+1)))
  have hfM : Measurable f := hRaw.comp
    (((initial_measurable _).comp measurable_snd).prodMk ((measurable_pi_apply _).comp measurable_snd))
  have hfb' (p : Ω×(Fin (n+2) → V)) : |f p|≤2*(∑ j, B j) := by
    simpa only [f,raw,abs_abs] using hRb (initial p.2) (p.2 (Fin.last (n+1)))
  have HS := GGFiniteReplicaSnocIntegration.integral_joint_iid_snoc d G n f hfM hfb'
  have hi (old : Fin (n+1) → V) (z : V) : initial (Fin.snoc old z)=old := by
    funext j
    simp only [initial,Fin.snoc_castSucc]
  dsimp only [f] at HS
  simp only [hi,Fin.snoc_last] at HS
  have HF := fresh_score_difference_l1 d G n hR psi phi hpsi hphi B hpb hfb
  have HL := joint_snd_hasLaw d G (n+2)
  refine ⟨hCI,?_⟩
  calc
    _ = ∫ p : Ω×(Fin (n+2) → V), raw (initial p.2,p.2 (Fin.last (n+1))) ∂(d ⊗ₘ iid G (n+2)) := HS.symm
    _ = ∫ s : Fin (n+2) → V, raw (initial s,s (Fin.last (n+1))) ∂law d G (n+2) := HL.integral_comp HF.1.aestronglyMeasurable
    _ ≤ _ := HF.2

theorem observable_sub_le (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    (psi phi : Fin (n+1) → ℝ → ℝ) (hpsi : ∀ j, Measurable (psi j)) (hphi : ∀ j, Measurable (phi j))
    (B : Fin (n+1) → ℝ) (hpb : ∀ j r, |psi j r|≤B j) (hfb : ∀ j r, |phi j r|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi) {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    {b : ((Fin (n+1) → V)×V) → ℝ} (hbM : Measurable b) (hb0 : ∀ q, 0≤b q) (hb1 : ∀ q, b q≤1)
    {chi : ℝ → ℝ} (hchiM : Measurable chi) (hchi : ∀ z, |chi z|≤1) {L : ℝ} (hL : 0≤L)
    (hLip : ∀ x y, |chi x-chi y|≤L*|x-y|) (t : ℝ) :
    |observable d G n overlap psi Phi b chi t-observable d G n overlap phi Phi b chi t|≤
      2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))*(((n : ℝ)+1)+L)*
        (∑ j, ∫ r, |psi j r-phi j r|
          ∂(((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2))) := by
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : V×V ↦ overlap p.1 p.2)
  haveI : IsProbabilityMeasure rho := (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).mpr inferInstance
  let a : Fin (n+1) → ℝ := fun j ↦ ∫ r, psi j r ∂rho
  let a' : Fin (n+1) → ℝ := fun j ↦ ∫ r, phi j r ∂rho
  let mu := d ⊗ₘ iid G (n+1)
  let Ip := integrand n G overlap psi a Phi b chi t
  let If := integrand n G overlap phi a' Phi b chi t
  let H : Ω×(Fin (n+1) → V) → ℝ := fun p ↦
    |(∑ l, correctedScore n overlap psi a p.2 l)-(∑ l, correctedScore n overlap phi a' p.2 l)|
  let F : Ω×(Fin (n+1) → V) → ℝ := fun p ↦ ∫ z,
    |score n overlap psi p.2 z-score n overlap phi p.2 z| ∂G p.1
  let K := C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *(∑ j, B j))
  let k : ℝ := (n : ℝ)+1
  let E := ∑ j, ∫ r, |psi j r-phi j r| ∂rho
  have ha (j) : |a j|≤B j := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := rho) (f := psi j) (C := B j)
        (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hpb j r))
  have ha' (j) : |a' j|≤B j := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := rho) (f := phi j) (C := B j)
        (Eventually.of_forall (fun r ↦ by simpa only [Real.norm_eq_abs] using hfb j r))
  have hIp : Integrable Ip mu := integrand_integrable d G n hR hpsi a B hpb ha hPhi hp hbM hchiM hchi t
  have hIf : Integrable If mu := integrand_integrable d G n hR hphi a' B hfb ha' hPhi hp hbM hchiM hchi t
  have hH := corrected_sum_joint_l1 d G n hR psi phi hpsi hphi B hpb hfb
  have hF := fresh_conditional_joint_l1 d G n hR psi phi hpsi hphi B hpb hfb
  change Integrable H mu ∧ (∫ p, H p ∂mu)≤k*E at hH
  change Integrable F mu ∧ (∫ p, F p ∂mu)≤E at hF
  have hK : 0≤K := mul_nonneg (mul_nonneg hC (abs_nonneg t)) (Real.exp_nonneg _)
  have hk : 0≤k := by dsimp only [k]; positivity
  have hkl : 0≤k+2*L := by positivity
  have hRhs : Integrable (fun p ↦ K*(H p+(k+2*L)*F p)) mu := by
    exact (hH.1.add (hF.1.const_mul _)).const_mul _
  have hPoint (p) : |Ip p-If p|≤K*(H p+(k+2*L)*F p) :=
    integrand_sub_bound G n hR psi phi hpsi hphi a a' B hpb hfb ha ha' hC hp hbM hb0 hb1 hchi hL hLip t p
  have hAbsI : Integrable (fun p ↦ |Ip p-If p|) mu := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hIp.sub hIf).norm
  have hMono := integral_mono hAbsI hRhs hPoint
  have hRI : Integrable (fun p ↦ H p+(k+2*L)*F p) mu := hH.1.add (hF.1.const_mul _)
  rw [integral_const_mul,integral_add hH.1 (hF.1.const_mul _),integral_const_mul] at hMono
  have hBound : (∫ p, |Ip p-If p| ∂mu)≤K*(k*E+(k+2*L)*E) :=
    hMono.trans (mul_le_mul_of_nonneg_left
      (add_le_add hH.2 (mul_le_mul_of_nonneg_left hF.2 hkl)) hK)
  change |(∫ p, Ip p ∂mu)-(∫ p, If p ∂mu)|≤_
  rw [← integral_sub hIp hIf]
  calc
    _ ≤ ∫ p, |Ip p-If p| ∂mu := abs_integral_le_integral_abs
    _ ≤ K*(k*E+(k+2*L)*E) := hBound
    _ = _ := by dsimp only [K,k,E,rho]; ring

end
end TensorPCA.NonRSLowerProofs.GGFiniteJointScoreStability
