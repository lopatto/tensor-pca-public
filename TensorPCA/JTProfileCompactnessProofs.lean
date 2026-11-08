-- SPDX-License-Identifier: Apache-2.0
-- Narrow generic Arzela-Ascoli/countable-exhaustion port from
-- https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/SourceLiteratureGroundStateExtraction.lean
-- No thermal minimizer/profile hypothesis is imported.
module
public import TensorPCA.JTProfileBoundsProofs
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences

@[expose] public section
namespace TensorPCA.JTProfileCompactnessProofs
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem local_lipschitz_subsequence
    (f : ℕ → ℝ → ℝ) (r : ℕ → ℝ) (C : ℝ) (K : ℕ → ℝ≥0)
    (hbound : ∀ n m t, t ∈ Icc (0 : ℝ) (r m) → f n t ∈ Icc 0 C)
    (hlip : ∀ n m, LipschitzOnWith (K m) (f n) (Icc (0 : ℝ) (r m)))
    (hcover : ∀ t ∈ Ico (0 : ℝ) 1, ∃ m, t ∈ Icc (0 : ℝ) (r m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto (fun n => f (φ n) t) atTop (𝓝 l) := by
  let B (n m : ℕ) : Icc (0 : ℝ) (r m) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t => f n t, (hlip n m).to_restrict.continuous⟩
  let S (m : ℕ) : Set (Icc (0 : ℝ) (r m) →ᵇ ℝ) :=
    closure (range (fun n => B n m))
  have hS (m : ℕ) : IsCompact (S m) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) C) isCompact_Icc
    · rintro g t ⟨n, rfl⟩
      exact hbound n m t t.property
    · apply Metric.equicontinuous_of_continuity_modulus (fun d => (K m : ℝ) * d)
      · simpa only [mul_zero] using (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun d : ℝ => (K m : ℝ) * d) (𝓝 0) (𝓝 ((K m : ℝ) * 0)))
      · rintro x y ⟨g, hg⟩
        obtain ⟨n, rfl⟩ := hg
        exact ((hlip n m).to_restrict).dist_le_mul x y
  let (m : ℕ) : CompactSpace (S m) := isCompact_iff_compactSpace.mp (hS m)
  let F (n : ℕ) : ∀ m, S m := fun m => ⟨B n m, subset_closure ⟨n, rfl⟩⟩
  obtain ⟨G, φ, hφ, hG⟩ := CompactSpace.tendsto_subseq F
  refine ⟨φ, hφ, ?_⟩
  intro t ht
  obtain ⟨m, hm⟩ := hcover t ht
  let z : Icc (0 : ℝ) (r m) := ⟨t, hm⟩
  refine ⟨(G m).val z, ?_⟩
  have hcoord := ((continuous_apply m).tendsto G).comp hG
  have heval := (((BoundedContinuousFunction.lipschitz_eval_const z).continuous.comp
    continuous_subtype_val).tendsto (G m)).comp hcoord
  exact heval

def exhaustion (m : ℕ) : ℝ := 1 - ((m : ℝ) + 2)⁻¹

theorem exhaustion_lt_one (m : ℕ) : exhaustion m < 1 := by
  dsimp [exhaustion]
  have h : 0 < (m : ℝ) + 2 := by positivity
  linarith [inv_pos.mpr h]

theorem exhaustion_cover {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ∃ m, t ∈ Icc (0 : ℝ) (exhaustion m) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((1-t)⁻¹)
  refine ⟨m, ht.1, ?_⟩
  have hd : 0 < (m : ℝ) + 2 := by positivity
  have hi : ((m : ℝ) + 2)⁻¹ ≤ 1-t := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    have hprod : (1-t) * (1-t)⁻¹ = 1 := mul_inv_cancel₀ (sub_pos.mpr ht.2).ne'
    nlinarith [mul_lt_mul_of_pos_left hm (sub_pos.mpr ht.2)]
  dsimp [exhaustion]
  linarith

theorem exists_profile_pointwise_subsequence (p : ℕ → ℝ → ℝ)
    (hp : ∀ n, Scalar.AdmissibleProfile (p n)) {M : ℝ} (hM : ∀ n, p n 0 ≤ M) :
    ∃ f : ℝ → ℝ, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ t ∈ Ico (0 : ℝ) 1, Tendsto (fun n => p (phi n) t) atTop (𝓝 (f t)) := by
  have hM0 : 0 ≤ M := ((hp 0).2.2.2 0 (by norm_num)).le.trans (hM 0)
  let K (m : ℕ) : ℝ≥0 := ⟨M/(1-exhaustion m),div_nonneg hM0 (sub_pos.mpr (exhaustion_lt_one m)).le⟩
  obtain ⟨phi,hphi,hlim⟩ := local_lipschitz_subsequence p exhaustion M K
    (fun n m t ht => by
      have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.trans (exhaustion_lt_one m).le⟩
      exact ⟨((hp n).2.2.2 t ht1).le,
        ((hp n).2.1 (by norm_num) ht1 ht.1).trans (hM n)⟩)
    (fun n m => JTProfileBoundsProofs.profile_local_lipschitz (hp n) (hM n) (exhaustion_lt_one m))
    (fun _ ht => exhaustion_cover ht)
  classical
  let f : ℝ → ℝ := fun t => if ht : t ∈ Ico (0 : ℝ) 1 then Classical.choose (hlim t ht) else 0
  refine ⟨f,phi,hphi,?_⟩
  intro t ht
  simpa only [f,dite_eq_left ht] using Classical.choose_spec (hlim t ht)

theorem profile_limit_local_lipschitz (p : ℕ → ℝ → ℝ)
    (hp : ∀ n, Scalar.AdmissibleProfile (p n)) {M : ℝ} (hM : ∀ n, p n 0 ≤ M)
    (f : ℝ → ℝ) (phi : ℕ → ℕ)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1, Tendsto (fun n => p (phi n) t) atTop (𝓝 (f t)))
    {r : ℝ} (hr : r < 1) :
    LipschitzOnWith ⟨M/(1-r),div_nonneg
      (((hp 0).2.2.2 0 (by norm_num)).le.trans (hM 0)) (sub_pos.mpr hr).le⟩ f (Icc (0 : ℝ) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  exact le_of_tendsto' ((hlim s ⟨hs.1,hs.2.trans_lt hr⟩).dist
    (hlim t ⟨ht.1,ht.2.trans_lt hr⟩))
    (fun n => (JTProfileBoundsProofs.profile_local_lipschitz (hp (phi n)) (hM (phi n)) hr).dist_le_mul s hs t ht)

theorem profile_limit_properties (p : ℕ → ℝ → ℝ)
    (hp : ∀ n, Scalar.AdmissibleProfile (p n)) {M eps : ℝ} (hM : ∀ n, p n 0 ≤ M)
    (hfloor : ∀ n t, t ∈ Icc (0 : ℝ) 1 → eps ≤ p n t)
    (f : ℝ → ℝ) (phi : ℕ → ℕ)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1, Tendsto (fun n => p (phi n) t) atTop (𝓝 (f t))) :
    (∀ t ∈ Ico (0 : ℝ) 1, f t ∈ Icc eps M) ∧
      AntitoneOn f (Ico (0 : ℝ) 1) ∧ ConcaveOn ℝ (Ico (0 : ℝ) 1) f ∧
        ContinuousOn f (Ico (0 : ℝ) 1) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim t ht) (fun n => hfloor (phi n) t ht1),
      le_of_tendsto' (hlim t ht) (fun n => ((hp (phi n)).2.1 (by norm_num) ht1 ht.1).trans (hM (phi n)))⟩
  · intro s hs t ht hst
    exact le_of_tendsto_of_tendsto' (hlim t ht) (hlim s hs)
      (fun n => (hp (phi n)).2.1 ⟨hs.1,hs.2.le⟩ ⟨ht.1,ht.2.le⟩ hst)
  · refine ⟨convex_Ico 0 1,?_⟩
    intro s hs t ht a b ha hb hab
    have hx : a • s+b • t ∈ Ico (0 : ℝ) 1 := (convex_Ico 0 1) hs ht ha hb hab
    apply le_of_tendsto_of_tendsto'
      (((hlim s hs).const_mul a).add ((hlim t ht).const_mul b)) (hlim _ hx)
    intro n
    exact (hp (phi n)).2.2.1.2 ⟨hs.1,hs.2.le⟩ ⟨ht.1,ht.2.le⟩ ha hb hab
  · intro t ht
    let r : ℝ := (t+1)/2
    have hr : r < 1 := by dsimp [r]; linarith [ht.2]
    have htr : t < r := by dsimp [r]; linarith [ht.2]
    have hc := (profile_limit_local_lipschitz p hp hM f phi hlim hr).continuousOn t ⟨ht.1,htr.le⟩
    apply hc.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds htr)] with s hs hsr
    exact ⟨hs.1,hsr.le⟩

theorem exhaustion_nonneg (n : ℕ) : 0 ≤ exhaustion n := by
  have hden : (1 : ℝ) ≤ (n : ℝ)+2 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  dsimp [exhaustion]
  rw [one_div] at hi
  norm_num at hi
  linarith

theorem exhaustion_tendsto : Tendsto exhaustion atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi : Tendsto (fun n : ℕ => ((n : ℝ)+2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hd
  change Tendsto (fun n : ℕ => 1-((n : ℝ)+2)⁻¹) atTop (𝓝 1)
  simpa only [sub_zero] using tendsto_const_nhds.sub hi

def profileLeftLimit (f : ℝ → ℝ) : ℝ := sInf (f '' Ico (0 : ℝ) 1)

def completeProfile (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 1 then f (max 0 t) else profileLeftLimit f

theorem exists_profile_completion (f : ℝ → ℝ) {eps M : ℝ} (heps : 0 < eps)
    (hbounds : ∀ t ∈ Ico (0 : ℝ) 1, f t ∈ Icc eps M)
    (hanti : AntitoneOn f (Ico (0 : ℝ) 1)) (hconc : ConcaveOn ℝ (Ico (0 : ℝ) 1) f)
    (hcont : ContinuousOn f (Ico (0 : ℝ) 1)) :
    Scalar.AdmissibleProfile (completeProfile f) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, completeProfile f t = f t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ completeProfile f t) ∧ completeProfile f 0 ≤ M := by
  let F := fun t : ℝ => f (max 0 t)
  have hmaxmem {t : ℝ} (ht : t < 1) : max 0 t ∈ Ico (0 : ℝ) 1 :=
    ⟨le_max_left _ _,max_lt (by norm_num) ht⟩
  have hne : (f '' Ico (0 : ℝ) 1).Nonempty := ⟨f 0,0,by norm_num,rfl⟩
  have hbb : BddBelow (f '' Ico (0 : ℝ) 1) := by
    refine ⟨eps,?_⟩
    rintro y ⟨t,ht,rfl⟩
    exact (hbounds t ht).1
  have hcLower : eps ≤ profileLeftLimit f := by
    apply le_csInf hne
    rintro y ⟨t,ht,rfl⟩
    exact (hbounds t ht).1
  have hcLe (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : profileLeftLimit f ≤ f t :=
    csInf_le hbb (mem_image_of_mem f ht)
  have hFAnti : AntitoneOn F (Iio (1 : ℝ)) := by
    intro s hs t ht hst
    exact hanti (hmaxmem hs) (hmaxmem ht) (max_le_max le_rfl hst)
  have hFcont : ContinuousOn F (Iio (1 : ℝ)) := by
    exact hcont.comp (continuous_const.max continuous_id).continuousOn (fun t ht => hmaxmem ht)
  have hFimage : F '' Iio (1 : ℝ) = f '' Ico (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨max 0 t,hmaxmem ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      refine ⟨t,ht.2,?_⟩
      dsimp [F]
      rw [max_eq_right ht.1]
  have hFbb : BddBelow (F '' Iio (1 : ℝ)) := hFimage.symm ▸ hbb
  have hFlim : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (profileLeftLimit f)) := by
    simpa only [hFimage,profileLeftLimit] using hFAnti.tendsto_nhdsLT hFbb
  have heq (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : completeProfile f t = f t := by
    simp only [completeProfile,ite_eq_left ht.2,max_eq_right ht.1]
  have heqF (t : ℝ) (ht : t < 1) : completeProfile f t = F t := by
    simp only [completeProfile,ite_eq_left ht,F]
  have heq1 : completeProfile f 1 = profileLeftLimit f := by
    simp only [completeProfile,lt_self_iff_false,ite_false]
  have hpc : ContinuousOn (completeProfile f) (Icc (0 : ℝ) 1) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htlt | rfl
    · apply ContinuousAt.continuousWithinAt
      apply ((hFcont t htlt).continuousAt (Iio_mem_nhds htlt)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds htlt] with s hs
      exact heqF s hs
    · have hleft : ContinuousWithinAt (completeProfile f) (Iio (1 : ℝ)) 1 := by
        change Tendsto (completeProfile f) (𝓝[<] (1 : ℝ)) (𝓝 (completeProfile f 1))
        rw [heq1]
        apply hFlim.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (heqF s hs).symm
      have hic : ContinuousWithinAt (completeProfile f) (Iic (1 : ℝ)) 1 :=
        continuousWithinAt_Iio_iff_Iic.mp hleft
      exact hic.mono (fun s hs => hs.2)
  have hfloor (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : eps ≤ completeProfile f t := by
    rcases lt_or_eq_of_le ht.2 with htlt | rfl
    · rw [heq t ⟨ht.1,htlt⟩]
      exact (hbounds t ⟨ht.1,htlt⟩).1
    · rw [heq1]
      exact hcLower
  have hpanti : AntitoneOn (completeProfile f) (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    rcases lt_or_eq_of_le ht.2 with htlt | rfl
    · have hslt : s < 1 := hst.trans_lt htlt
      rw [heq s ⟨hs.1,hslt⟩,heq t ⟨ht.1,htlt⟩]
      exact hanti ⟨hs.1,hslt⟩ ⟨ht.1,htlt⟩ hst
    · rcases lt_or_eq_of_le hs.2 with hslt | rfl
      · rw [heq1,heq s ⟨hs.1,hslt⟩]
        exact hcLe s ⟨hs.1,hslt⟩
      · exact le_rfl
  have hshrink (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) :
      exhaustion n*t ∈ Ico (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (exhaustion_nonneg n) ht.1,?_⟩
    exact (mul_le_mul_of_nonneg_left ht.2 (exhaustion_nonneg n)).trans_lt
      (by simpa only [mul_one] using exhaustion_lt_one n)
  have hlim (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => completeProfile f (exhaustion n*t)) atTop (𝓝 (completeProfile f t)) := by
    have hx : Tendsto (fun n => exhaustion n*t) atTop (𝓝 t) := by
      simpa only [one_mul] using exhaustion_tendsto.mul_const t
    have hxwithin : Tendsto (fun n => exhaustion n*t) atTop (𝓝[Icc (0 : ℝ) 1] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hx,Eventually.of_forall (fun n =>
        ⟨(hshrink t ht n).1,(hshrink t ht n).2.le⟩)⟩
    exact (show Tendsto (completeProfile f) (𝓝[Icc (0 : ℝ) 1] t)
      (𝓝 (completeProfile f t)) from hpc t ht).comp hxwithin
  have hpconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (completeProfile f) := by
    refine ⟨convex_Icc 0 1,?_⟩
    intro s hs t ht a b ha hb hab
    have hcombo : a*s+b*t ∈ Icc (0 : ℝ) 1 := (convex_Icc 0 1) hs ht ha hb hab
    apply le_of_tendsto_of_tendsto'
      (((hlim s hs).const_mul a).add ((hlim t ht).const_mul b)) (hlim _ hcombo)
    intro n
    have hsN := hshrink s hs n
    have htN := hshrink t ht n
    have hNcombo : a*(exhaustion n*s)+b*(exhaustion n*t) ∈ Ico (0 : ℝ) 1 :=
      (convex_Ico 0 1) hsN htN ha hb hab
    have H := hconc.2 hsN htN ha hb hab
    simp only [smul_eq_mul] at H
    rw [← heq _ hsN,← heq _ htN,← heq _ hNcombo] at H
    rw [show a*(exhaustion n*s)+b*(exhaustion n*t) = exhaustion n*(a*s+b*t) by ring] at H
    exact H
  refine ⟨⟨hpc,hpanti,hpconc,fun t ht => heps.trans_le (hfloor t ht)⟩,heq,hfloor,?_⟩
  rw [heq 0 (by norm_num)]
  exact (hbounds 0 (by norm_num)).2


end
end TensorPCA.JTProfileCompactnessProofs

