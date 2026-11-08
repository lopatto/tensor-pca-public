-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteReweightingPadding
public import TensorPCA.NonRSLowerProofs.GGFiniteReweightingJets

/-! Exact fresh-replica identities for tilted partition weights. Zero tests on fresh
anchors preserve the old score and conditional means.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteReplicaWeightMoments
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel GGFiniteFirstJet GGFiniteFirstJetPadding
open GGFiniteReweightingDerivative GGFiniteReweightingPadding GGFiniteReweightingJets
open scoped BigOperators
noncomputable section
variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

def tiltedWeightMean (n : ℕ) (G : Kernel Ω V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (b : ((Fin (n+1) → V)×V) → ℝ)
    (t : ℝ) (w : Ω) (old : Fin (n+1) → V) : ℝ :=
  ∫ v, b (old,v)*Real.exp (t*score n overlap psi old v)/
    reweightingNormalizer n G overlap psi t w old ∂G w

theorem tiltedWeightMean_measurable (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    {b : ((Fin (n+1) → V)×V) → ℝ} (hb : Measurable b) (t : ℝ) :
    Measurable (fun p : Ω×(Fin (n+1) → V) ↦ tiltedWeightMean n G overlap psi b t p.1 p.2) := by
  let P := Ω×(Fin (n+1) → V)
  let kap : Kernel P V := G.comap Prod.fst measurable_fst
  have hS : Measurable (fun p : P×V ↦ score n overlap psi p.1.2 p.2) :=
    (score_joint_measurable n hR hpsi).comp (measurable_fst.snd.prodMk measurable_snd)
  have hb' : Measurable (fun p : P×V ↦ b (p.1.2,p.2)) :=
    hb.comp (measurable_fst.snd.prodMk measurable_snd)
  have hNum : Measurable (fun p : P ↦ ∫ v, b (p.2,v)*Real.exp (t*score n overlap psi p.2 v) ∂G p.1) := by
    simpa only [kap,Kernel.comap_apply,Pi.mul_apply,Function.comp_def] using
      ((hb'.mul (hS.const_mul t).exp).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable
  have hZ : Measurable (fun p : P ↦ reweightingNormalizer n G overlap psi t p.1 p.2) :=
    (normalizer_joint_measurable G n hR hpsi).1.comp (measurable_const.prodMk measurable_id)
  convert hNum.div hZ using 1
  funext p
  exact integral_div _ _

theorem tiltedWeightMean_abs_le (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {b : ((Fin (n+1) → V)×V) → ℝ} (hbM : Measurable b)
    {D : ℝ} (hbb : ∀ p, |b p|≤D) (t : ℝ) (w : Ω) (old : Fin (n+1) → V) :
    |tiltedWeightMean n G overlap psi b t w old|≤D := by
  have hS : Measurable (score n overlap psi old) :=
    (score_joint_measurable n hR hpsi).comp (measurable_const.prodMk measurable_id)
  have hbm : Measurable (fun v ↦ b (old,v)) := hbM.comp (measurable_const.prodMk measurable_id)
  have hExp : Integrable (fun v ↦ Real.exp (t*score n overlap psi old v)) (G w) := by
    apply Integrable.of_bound (hS.const_mul t).exp.aestronglyMeasurable (Real.exp (|t| *(∑ j, B j)))
    exact Eventually.of_forall (fun v ↦ by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact (GGFiniteEmpiricalNormalizer.exp_score_bounds (score_abs_le n overlap psi B hb old) t v).2)
  have hNum : Integrable (fun v ↦ b (old,v)*Real.exp (t*score n overlap psi old v)) (G w) :=
    hExp.bdd_mul hbm.aestronglyMeasurable (Eventually.of_forall (fun v ↦ by simpa only [Real.norm_eq_abs] using hbb (old,v)))
  have H : |∫ v, b (old,v)*Real.exp (t*score n overlap psi old v) ∂G w|≤
      D*reweightingNormalizer n G overlap psi t w old := by
    calc
      _ ≤ ∫ v, |b (old,v)*Real.exp (t*score n overlap psi old v)| ∂G w := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (f := fun v ↦ b (old,v)*Real.exp (t*score n overlap psi old v))
      _ ≤ ∫ v, D*Real.exp (t*score n overlap psi old v) ∂G w := by
        apply integral_mono hNum.norm (hExp.const_mul D)
        intro v
        change |b (old,v)*Real.exp (t*score n overlap psi old v)|≤D*Real.exp (t*score n overlap psi old v)
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hbb (old,v)) (Real.exp_nonneg _)
      _ = _ := integral_const_mul _ _
  have hz := reweightingNormalizer_pos G n hR hpsi B hb t w old
  rw [tiltedWeightMean,integral_div,abs_div,abs_of_pos hz]
  exact (div_le_iff₀ hz).mpr H

theorem tiltedWeightMean_nonneg (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j)
    {b : ((Fin (n+1) → V)×V) → ℝ} (hb0 : ∀ p, 0≤b p)
    (t : ℝ) (w : Ω) (old : Fin (n+1) → V) :
    0≤tiltedWeightMean n G overlap psi b t w old := by
  exact integral_nonneg (fun v ↦ div_nonneg (mul_nonneg (hb0 _) (Real.exp_nonneg _))
    (reweightingNormalizer_pos G n hR hpsi B hb t w old).le)

theorem tiltedWeightMean_zero (G : Kernel Ω V) [IsMarkovKernel G]
    (n : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (b : ((Fin (n+1) → V)×V) → ℝ) (w : Ω) (old : Fin (n+1) → V) :
    tiltedWeightMean n G overlap psi b 0 w old=∫ v, b (old,v) ∂G w := by
  simp only [tiltedWeightMean,reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,
    zero_mul,Real.exp_zero,integral_const,probReal_univ,one_smul,mul_one,div_one]

def padZero {α : Type*} [Zero α] (n : ℕ) (f : Fin (n+1) → α) :
    (m : ℕ) → Fin (n+m+1) → α
  | 0 => f
  | m+1 => Fin.snoc (padZero n f m) 0

def basePrefix (n : ℕ) : (m : ℕ) → (Fin (n+m+1) → V) → (Fin (n+1) → V)
  | 0,s => s
  | m+1,s => basePrefix n m (initial s)

def momentLift (n : ℕ) (Phi : (Fin (n+1) → V) → ℝ) :
    (m : ℕ) → (Fin m → (((Fin (n+1) → V)×V) → ℝ)) → (Fin (n+m+1) → V) → ℝ
  | 0,_b,s => Phi s
  | m+1,b,s => momentLift n Phi m (Fin.init b) (initial s)*
      b (Fin.last m) (basePrefix n m (initial s),s (Fin.last (n+m+1)))

theorem basePrefix_measurable (n m : ℕ) : Measurable (basePrefix (V := V) n m) := by
  induction m with
  | zero => exact measurable_id
  | succ m ih => exact ih.comp (initial_measurable _)

theorem padZero_tests_measurable (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ}
    (hpsi : ∀ j, Measurable (psi j)) (m : ℕ) : ∀ j, Measurable (padZero n psi m j) := by
  induction m with
  | zero => exact hpsi
  | succ m ih => exact snoc_zero_measurable ih

theorem padZero_tests_bounds (n : ℕ) {psi : Fin (n+1) → ℝ → ℝ} {B : Fin (n+1) → ℝ}
    (hb : ∀ j r, |psi j r|≤B j) (m : ℕ) : ∀ j r, |padZero n psi m j r|≤padZero n B m j := by
  induction m with
  | zero => exact hb
  | succ m ih => exact snoc_zero_bounds ih

theorem padZero_mean_bounds (n : ℕ) {means B : Fin (n+1) → ℝ}
    (hb : ∀ j, |means j|≤B j) (m : ℕ) : ∀ j, |padZero n means m j|≤padZero n B m j := by
  induction m with
  | zero => exact hb
  | succ m ih => exact snoc_zero_mean_bounds ih

theorem padZero_score (n m : ℕ) (overlap : V → V → ℝ) (psi : Fin (n+1) → ℝ → ℝ)
    (s : Fin (n+m+1) → V) (v : V) :
    score (n+m) overlap (padZero n psi m) s v=score n overlap psi (basePrefix n m s) v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change score ((n+m)+1) overlap (Fin.snoc (padZero n psi m) (fun _ ↦ 0)) s v=_
    rw [score_snoc_zero]
    exact ih (initial s)

theorem padZero_normalizer (n m : ℕ) (G : Kernel Ω V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (t : ℝ) (w : Ω) (s : Fin (n+m+1) → V) :
    reweightingNormalizer (n+m) G overlap (padZero n psi m) t w s=
      reweightingNormalizer n G overlap psi t w (basePrefix n m s) := by
  unfold reweightingNormalizer GGFiniteEmpiricalNormalizer.normalizer
  simp_rw [padZero_score]

theorem padZero_tiltedWeightMean (n m : ℕ) (G : Kernel Ω V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (b : ((Fin (n+1) → V)×V) → ℝ)
    (t : ℝ) (w : Ω) (s : Fin (n+m+1) → V) :
    tiltedWeightMean (n+m) G overlap (padZero n psi m)
      (fun p ↦ b (basePrefix n m p.1,p.2)) t w s=
        tiltedWeightMean n G overlap psi b t w (basePrefix n m s) := by
  simp only [tiltedWeightMean,padZero_score,padZero_normalizer]

theorem momentLift_measurable (n m : ℕ) {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi)
    (b : Fin m → (((Fin (n+1) → V)×V) → ℝ)) (hb : ∀ i, Measurable (b i)) :
    Measurable (momentLift n Phi m b) := by
  induction m with
  | zero => exact hPhi
  | succ m ih =>
    have HM := ih (Fin.init b) (fun i ↦ hb i.castSucc)
    exact (HM.comp (initial_measurable _)).mul ((hb (Fin.last m)).comp
      (((basePrefix_measurable n m).comp (initial_measurable _)).prodMk (measurable_pi_apply _)))

theorem momentLift_abs_le (n m : ℕ) {Phi : (Fin (n+1) → V) → ℝ} {C : ℝ}
    (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (b : Fin m → (((Fin (n+1) → V)×V) → ℝ)) (hb : ∀ i p, |b i p|≤1)
    (s : Fin (n+m+1) → V) : |momentLift n Phi m b s|≤C := by
  induction m with
  | zero => exact hp s
  | succ m ih =>
    change |momentLift n Phi m (Fin.init b) (initial s)*b (Fin.last m) _|≤C
    rw [abs_mul]
    exact (mul_le_mul (ih (Fin.init b) (fun i ↦ hb i.castSucc) (initial s)) (hb (Fin.last m) _)
      (abs_nonneg _) hC).trans_eq (mul_one C)

theorem momentLift_mul_base (n m : ℕ) (Phi f : (Fin (n+1) → V) → ℝ)
    (b : Fin m → (((Fin (n+1) → V)×V) → ℝ)) (s : Fin (n+m+1) → V) :
    momentLift n (fun old ↦ Phi old*f old) m b s=
      momentLift n Phi m b s*f (basePrefix n m s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [momentLift,basePrefix,ih]
    ring

theorem fresh_weight_identity (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi)
    {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (b : ((Fin (n+1) → V)×V) → ℝ) (hbM : Measurable b)
    {D : ℝ} (hD : 0≤D) (hbb : ∀ p, |b p|≤D) (t : ℝ) :
    reweightingExpectation (n+1) d G overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0)
      (fun s ↦ Phi (initial s)*b (initial s,s (Fin.last (n+1)))) t=
    ∫ w, (∫ old : Fin (n+1) → V,
      (Phi old*Real.exp (t*(∑ l, correctedScore n overlap psi means old l))/
        (reweightingNormalizer n G overlap psi t w old)^(n+1))*
          tiltedWeightMean n G overlap psi b t w old
      ∂Measure.pi (fun _ : Fin (n+1) ↦ G w)) ∂d := by
  let Phi' : (Fin (n+2) → V) → ℝ := fun s ↦ Phi (initial s)*b (initial s,s (Fin.last (n+1)))
  have hPM : Measurable Phi' := (hPhi.comp (initial_measurable _)).mul
    (hbM.comp ((initial_measurable _).prodMk (measurable_pi_apply _)))
  have hPb (s : Fin (n+2) → V) : |Phi' s|≤C*D := by
    dsimp only [Phi']
    rw [abs_mul]
    exact mul_le_mul (hp _) (hbb _) (abs_nonneg _) hC
  unfold reweightingExpectation
  apply integral_congr_ae
  refine Eventually.of_forall (fun w ↦ ?_)
  let F : (Fin (n+2) → V) → ℝ := fun s ↦
    Phi' s*Real.exp (t*(∑ l, correctedScore (n+1) overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0) s l))/
      (reweightingNormalizer (n+1) G overlap (Fin.snoc psi (fun _ ↦ 0)) t w s)^(n+2)
  have hFM : Measurable F := by
    convert (weight_measurable G (n+1) hR (snoc_zero_measurable hpsi) (Fin.snoc means 0) hPM t).comp
      (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hFb (s : Fin (n+2) → V) : |F s|≤
      (C*D)*Real.exp (2*((n : ℝ)+2)*|t| *(∑ j, B j)) := by
    have H := weight_abs_le G (n+1) hR (snoc_zero_measurable hpsi) (Fin.snoc means 0)
      (Fin.snoc B 0) (snoc_zero_bounds hb) (snoc_zero_mean_bounds hm) hPb t w s
    simpa only [F,sum_snoc_zero,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using H
  have hsnoc := GGFiniteReplicaSnocIntegration.integral_pi_snoc (G w) n F hFM hFb
  change (∫ s, F s ∂Measure.pi (fun _ : Fin (n+2) ↦ G w))=_
  rw [hsnoc]
  apply integral_congr_ae
  refine Eventually.of_forall (fun old ↦ ?_)
  have hz := reweightingNormalizer_pos G n hR hpsi B hb t w old
  have he : (fun v ↦ F (Fin.snoc old v))=(fun v ↦
      (Phi old*Real.exp (t*(∑ l, correctedScore n overlap psi means old l))/
        (reweightingNormalizer n G overlap psi t w old)^(n+1))*
        (b (old,v)*Real.exp (t*score n overlap psi old v)/reweightingNormalizer n G overlap psi t w old)) := by
    funext v
    have hi : initial (Fin.snoc old v)=old := by funext j; simp only [initial,Fin.snoc_castSucc]
    dsimp only [F,Phi']
    rw [sum_correctedScore_snoc_zero,reweightingNormalizer_snoc_zero]
    simp only [hi,Fin.snoc_last,mul_add,Real.exp_add]
    rw [show n+2=(n+1)+1 by omega,pow_succ]
    field_simp [hz.ne'] <;> ring
  dsimp only
  rw [he,integral_const_mul]
  rfl

private def conditionalReweighting (n : ℕ) (nu : Measure V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (means : Fin (n+1) → ℝ)
    (Phi : (Fin (n+1) → V) → ℝ) (t : ℝ) : ℝ :=
  ∫ old, Phi old*Real.exp (t*(∑ l, correctedScore n overlap psi means old l))/
    (GGFiniteEmpiricalNormalizer.normalizer nu (score n overlap psi old) t)^(n+1)
    ∂Measure.pi (fun _ : Fin (n+1) ↦ nu)

private def conditionalMean (n : ℕ) (nu : Measure V) (overlap : V → V → ℝ)
    (psi : Fin (n+1) → ℝ → ℝ) (b : ((Fin (n+1) → V)×V) → ℝ)
    (t : ℝ) (old : Fin (n+1) → V) : ℝ :=
  tiltedWeightMean n (Kernel.const Unit nu) overlap psi b t () old

private theorem conditional_fresh (nu : Measure V) [IsProbabilityMeasure nu]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi)
    {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (b : ((Fin (n+1) → V)×V) → ℝ) (hbM : Measurable b) (hbb : ∀ p, |b p|≤1) (t : ℝ) :
    conditionalReweighting (n+1) nu overlap (Fin.snoc psi (fun _ ↦ 0)) (Fin.snoc means 0)
      (fun s ↦ Phi (initial s)*b (initial s,s (Fin.last (n+1)))) t=
        conditionalReweighting n nu overlap psi means
          (fun old ↦ Phi old*conditionalMean n nu overlap psi b t old) t := by
  have H := fresh_weight_identity (Measure.dirac ()) (Kernel.const Unit nu) n hR hpsi means B hb hm
    hPhi hC hp b hbM zero_le_one hbb t
  simp only [reweightingExpectation,integral_dirac,Kernel.const_apply,reweightingNormalizer] at H
  unfold conditionalReweighting conditionalMean
  convert H using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun old ↦ by
    dsimp only [reweightingNormalizer]
    ring)

private theorem conditional_block (nu : Measure V) [IsProbabilityMeasure nu]
    (n : ℕ) {overlap : V → V → ℝ} (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    (m : ℕ) {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi)
    {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (b : Fin m → (((Fin (n+1) → V)×V) → ℝ)) (hbM : ∀ i, Measurable (b i))
    (hbb : ∀ i p, |b i p|≤1) (t : ℝ) :
    conditionalReweighting (n+m) nu overlap (padZero n psi m) (padZero n means m)
      (momentLift n Phi m b) t=
        conditionalReweighting n nu overlap psi means
          (fun old ↦ Phi old*∏ i, conditionalMean n nu overlap psi (b i) t old) t := by
  induction m generalizing Phi C with
  | zero => simp only [padZero,momentLift,Fin.prod_univ_zero,mul_one,Nat.add_zero]
  | succ m ih =>
    let bLast := b (Fin.last m)
    let f : (Fin (n+1) → V) → ℝ := conditionalMean n nu overlap psi bLast t
    have hfM : Measurable f := by
      convert (tiltedWeightMean_measurable (Kernel.const Unit nu) n hR hpsi (hbM (Fin.last m)) t).comp
        (measurable_const.prodMk measurable_id) using 1 <;> rfl
    have hfb (old : Fin (n+1) → V) : |f old|≤1 :=
      tiltedWeightMean_abs_le (Kernel.const Unit nu) n hR hpsi B hb (hbM (Fin.last m)) (hbb (Fin.last m)) t () old
    have hProdM : Measurable (fun old ↦ Phi old*f old) := by convert hPhi.mul hfM using 1
    have hProdb (old : Fin (n+1) → V) : |Phi old*f old|≤C := by
      rw [abs_mul]
      exact (mul_le_mul (hp old) (hfb old) (abs_nonneg _) hC).trans_eq (mul_one C)
    let b' : ((Fin (n+m+1) → V)×V) → ℝ := fun p ↦ bLast (basePrefix n m p.1,p.2)
    have hb'M : Measurable b' := (hbM (Fin.last m)).comp
      (((basePrefix_measurable n m).comp measurable_fst).prodMk measurable_snd)
    have hb'b (p : ((Fin (n+m+1) → V)×V)) : |b' p|≤1 := hbb (Fin.last m) _
    have hLiftM := momentLift_measurable n m hPhi (Fin.init b) (fun i ↦ hbM i.castSucc)
    have hLiftb := momentLift_abs_le n m hC hp (Fin.init b) (fun i ↦ hbb i.castSucc)
    have HF := conditional_fresh nu (n+m) hR (padZero_tests_measurable n hpsi m)
      (padZero n means m) (padZero n B m) (padZero_tests_bounds n hb m) (padZero_mean_bounds n hm m)
        hLiftM hC hLiftb b' hb'M hb'b t
    have hcm (old : Fin (n+m+1) → V) :
        conditionalMean (n+m) nu overlap (padZero n psi m) b' t old=f (basePrefix n m old) :=
      padZero_tiltedWeightMean n m (Kernel.const Unit nu) overlap psi bLast t () old
    have htest : (fun old ↦ momentLift n Phi m (Fin.init b) old*
        conditionalMean (n+m) nu overlap (padZero n psi m) b' t old)=
          momentLift n (fun old ↦ Phi old*f old) m (Fin.init b) := by
      funext old
      rw [hcm]
      exact (momentLift_mul_base n m Phi f (Fin.init b) old).symm
    rw [htest] at HF
    have HR := ih hProdM hC hProdb (Fin.init b) (fun i ↦ hbM i.castSucc) (fun i ↦ hbb i.castSucc)
    calc
      _ = conditionalReweighting (n+m) nu overlap (padZero n psi m) (padZero n means m)
          (momentLift n (fun old ↦ Phi old*f old) m (Fin.init b)) t := HF
      _ = conditionalReweighting n nu overlap psi means
          (fun old ↦ (Phi old*f old)*∏ i, conditionalMean n nu overlap psi (Fin.init b i) t old) t := HR
      _ = _ := by
        apply congrArg (fun Q ↦ conditionalReweighting n nu overlap psi means Q t)
        funext old
        rw [Fin.prod_univ_castSucc]
        dsimp only [Fin.init,f,bLast]
        ring

/-- Monomial identity under the disorder and Gibbs laws. Every fresh test uses the same
original anchors, and fresh draws are conditionally iid. The GG tests do not depend
on disorder.
-/
theorem finite_weight_identity (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n m : ℕ) {overlap : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ overlap p.1 p.2))
    {psi : Fin (n+1) → ℝ → ℝ} (hpsi : ∀ j, Measurable (psi j))
    (means B : Fin (n+1) → ℝ) (hb : ∀ j r, |psi j r|≤B j) (hm : ∀ j, |means j|≤B j)
    {Phi : (Fin (n+1) → V) → ℝ} (hPhi : Measurable Phi)
    {C : ℝ} (hC : 0≤C) (hp : ∀ old, |Phi old|≤C)
    (b : Fin m → (((Fin (n+1) → V)×V) → ℝ)) (hbM : ∀ i, Measurable (b i))
    (hbb : ∀ i p, |b i p|≤1) (t : ℝ) :
    reweightingExpectation (n+m) d G overlap (padZero n psi m) (padZero n means m)
      (momentLift n Phi m b) t=
    ∫ w, (∫ old : Fin (n+1) → V,
      (Phi old*Real.exp (t*(∑ l, correctedScore n overlap psi means old l))/
        (reweightingNormalizer n G overlap psi t w old)^(n+1))*
          (∏ i, tiltedWeightMean n G overlap psi (b i) t w old)
      ∂Measure.pi (fun _ : Fin (n+1) ↦ G w)) ∂d := by
  unfold reweightingExpectation
  apply integral_congr_ae
  refine Eventually.of_forall (fun w ↦ ?_)
  have H := conditional_block (G w) n hR hpsi means B hb hm m hPhi hC hp b hbM hbb t
  change conditionalReweighting (n+m) (G w) overlap (padZero n psi m) (padZero n means m)
    (momentLift n Phi m b) t=_
  rw [H]
  unfold conditionalReweighting
  apply integral_congr_ae
  exact Eventually.of_forall (fun old ↦ by
    dsimp only [conditionalMean,tiltedWeightMean,reweightingNormalizer,Kernel.const_apply]
    ring)

end
end TensorPCA.NonRSLowerProofs.GGFiniteReplicaWeightMoments
