-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTProfileCompactnessProofs

/-! Positive-floor compactness applies to the original zero-temperature
functional. The endpoint completion changes no integral: the extracted sequence
converges at every point below one, hence almost everywhere. -/
@[expose] public section
namespace TensorPCA.JTFloorAttainmentProofs
open Set Filter MeasureTheory
open scoped Topology
open JTProfileBoundsProofs JTProfileCompactnessProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem parisiFunctional_tendsto_of_floor {xi : ℝ → ℝ}
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (p : ℕ → ℝ → ℝ) (hp : ∀ n, Scalar.AdmissibleProfile (p n))
    {eps M : ℝ} (heps : 0 < eps) (hM : ∀ n, p n 0 ≤ M)
    (hfloor : ∀ n t, t ∈ Icc (0 : ℝ) 1 → eps ≤ p n t)
    {q : ℝ → ℝ} (hq : Scalar.AdmissibleProfile q)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1, Tendsto (fun n => p n t) atTop (𝓝 (q t))) :
    Tendsto (fun n => Scalar.parisiFunctional xi h (p n)) atTop
      (𝓝 (Scalar.parisiFunctional xi h q)) := by
  obtain ⟨W,hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hxi
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by norm_num))
  have hM0 : 0 ≤ M := ((hp 0).2.2.2 0 (by norm_num)).le.trans (hM 0)
  let F : ℕ → ℝ → ℝ := fun n t => deriv (deriv xi) t*p n t+1/p n t
  let G : ℝ → ℝ := fun t => deriv (deriv xi) t*q t+1/q t
  have hFint (n : ℕ) : IntervalIntegrable (F n) volume (0 : ℝ) 1 := by
    exact ((hxi.mul (hp n).1).add
      (continuousOn_const.div (hp n).1 (fun t ht => ((hp n).2.2.2 t ht).ne'))).intervalIntegrable_of_Icc zero_le_one
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      ‖F n t‖ ≤ W*M+1/eps := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2⟩
    have hpt := (hp n).2.2.2 t ht1
    have hptM : p n t ≤ M := ((hp n).2.1 (by norm_num) ht1 ht.1.le).trans (hM n)
    have hinv : 1/p n t ≤ 1/eps := one_div_le_one_div_of_le heps (hfloor n t ht1)
    calc
      ‖F n t‖ ≤ ‖deriv (deriv xi) t*p n t‖+‖1/p n t‖ := norm_add_le _ _
      _ = ‖deriv (deriv xi) t‖*p n t+1/p n t := by
        rw [norm_mul,Real.norm_of_nonneg hpt.le,Real.norm_of_nonneg (one_div_pos.mpr hpt).le]
      _ ≤ W*M+1/eps := add_le_add
        (mul_le_mul (hW t ht1) hptM hpt.le hW0) hinv
  have hAE : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun n => F n t) atTop (𝓝 (G t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (show ∀ᵐ t : ℝ ∂volume, t ≠ 1 from by simp [ae_iff]))] with t ht hne
    have ht0 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
    exact ((hlim t ht0).const_mul _).add
      (tendsto_const_nhds.div (hlim t ht0) (hq.2.2.2 t ⟨ht.1.le,ht.2⟩).ne')
  have Hint := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ => W*M+1/eps)
    (fun n => ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hFint n)).aestronglyMeasurable)
    (integrable_const _) hbound hAE
  have Hint' : Tendsto (fun n => ∫ t in (0 : ℝ)..1, F n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, G t)) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using Hint
  exact Hint'.add ((hlim 0 (by norm_num)).const_mul (h^2+deriv xi 0))

theorem exists_floor_minimizer {xi : ℝ → ℝ}
    (hxi : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1)) (h : ℝ)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ deriv (deriv xi) t)
    (hpos : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv xi) t)
    (hA : 0 ≤ h^2+deriv xi 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ q : ℝ → ℝ, Scalar.AdmissibleProfile q ∧
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ q t) ∧
        ∀ p : ℝ → ℝ, Scalar.AdmissibleProfile p →
          (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t) →
            Scalar.parisiFunctional xi h q ≤ Scalar.parisiFunctional xi h p := by
  classical
  let S : Set ℝ := {v | ∃ p : ℝ → ℝ, Scalar.AdmissibleProfile p ∧
    (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t) ∧ Scalar.parisiFunctional xi h p = v}
  have hne : S.Nonempty := ⟨Scalar.parisiFunctional xi h (fun _ => eps),
    (fun _ => eps),Scalar.admissibleProfile_const heps,(fun _ _ => le_rfl),rfl⟩
  have hκ : 0 < coercivityConstant xi := coercivityConstant_pos hxi hw hpos
  have hbb : BddBelow S := by
    refine ⟨0,?_⟩
    rintro v ⟨p,hp,_,rfl⟩
    exact (mul_nonneg (hp.2.2.2 0 (by norm_num)).le hκ.le).trans
      (functional_coercive hp hxi h hw hA)
  obtain ⟨u,huanti,hulim,hu⟩ := exists_seq_tendsto_sInf hne hbb
  choose p hp hfloor hcost using hu
  let M := u 0/coercivityConstant xi
  have hM (n : ℕ) : p n 0 ≤ M := by
    apply (profile_initial_le_functional (hp n) hxi h hw hpos hA).trans
    rw [hcost]
    exact div_le_div_of_nonneg_right (huanti (Nat.zero_le n)) hκ.le
  obtain ⟨f,phi,hphi,hlim⟩ := exists_profile_pointwise_subsequence p hp hM
  obtain ⟨hfbound,hfanti,hfconc,hfcont⟩ := profile_limit_properties p hp hM hfloor f phi hlim
  obtain ⟨hq,heq,hqfloor,hqM⟩ := exists_profile_completion f heps hfbound hfanti hfconc hfcont
  let q := completeProfile f
  have hqlim (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      Tendsto (fun n => p (phi n) t) atTop (𝓝 (q t)) := by
    simpa only [q,heq t ht] using hlim t ht
  have HP := parisiFunctional_tendsto_of_floor hxi h (fun n => p (phi n))
    (fun n => hp (phi n)) heps (fun n => hM (phi n))
    (fun n => hfloor (phi n)) hq hqlim
  have Hu : Tendsto (fun n => Scalar.parisiFunctional xi h (p (phi n))) atTop (𝓝 (sInf S)) := by
    simpa only [hcost,Function.comp_def] using hulim.comp hphi.tendsto_atTop
  have Hvalue : Scalar.parisiFunctional xi h q = sInf S := tendsto_nhds_unique HP Hu
  refine ⟨q,hq,hqfloor,?_⟩
  intro r hr hrfloor
  rw [Hvalue]
  exact csInf_le hbb ⟨r,hr,hrfloor,rfl⟩

theorem exists_xiSlice_floor_minimizer (k : ℕ) (hk : 2 ≤ k) {m : ℝ}
    (hm : |m| < 1) (h : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ q : ℝ → ℝ, Scalar.AdmissibleProfile q ∧
      (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ q t) ∧
        ∀ p : ℝ → ℝ, Scalar.AdmissibleProfile p →
          (∀ t ∈ Icc (0 : ℝ) 1, eps ≤ p t) →
            Scalar.parisiFunctional (Scalar.xiSlice k m) h q ≤
              Scalar.parisiFunctional (Scalar.xiSlice k m) h p := by
  apply exists_floor_minimizer (xiSlice_secondDeriv_continuous k hk m).continuousOn h
    (fun t ht => xiSlice_secondDeriv_nonneg k hk hm ht) ?_
    (xiSlice_boundary_nonneg k hm h) heps
  exact ⟨1/2,by norm_num,xiSlice_secondDeriv_pos k hk hm (by norm_num)⟩


end
end TensorPCA.JTFloorAttainmentProofs
