-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledScalarProofs

/-! Compact uniformity for improving coupled scalar trials. -/
@[expose] public section
namespace TensorPCA.CoupledMacroscopicProofs
open Set Filter CoupledScalarProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def trialParams (lam m L u : ℝ) : Fin 4 → ℝ :=
  fun j => if j = 0 then lam else if j = 1 then m else if j = 2 then L else u

theorem trialParams_apply (lam m L u : ℝ) :
    trialParams lam m L u 0 = lam ∧ trialParams lam m L u 1 = m ∧
      trialParams lam m L u 2 = L ∧ trialParams lam m L u 3 = u := by
  simp [trialParams]

theorem continuous_trialParams (m L : ℝ) :
    Continuous (fun z : ℝ×ℝ => trialParams z.1 m L z.2) := by
  apply continuous_pi
  intro j
  by_cases h0 : j = 0
  · simp only [trialParams, ite_eq_left h0]
    exact continuous_fst
  · by_cases h1 : j = 1
    · simp only [trialParams, ite_eq_right h0, ite_eq_left h1]
      exact continuous_const
    · by_cases h2 : j = 2
      · simp only [trialParams, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
        exact continuous_const
      · simp only [trialParams, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
        exact continuous_snd

theorem continuous_margin (k : ℕ) (m L : ℝ) :
    Continuous (fun z : ℝ×ℝ => 1+(1-m)*Coupled.xiPrime k z.1 z.2-L) := by
  unfold Coupled.xiPrime
  fun_prop

theorem continuousAt_trial (k : ℕ) {lam m L u : ℝ}
    (hu : 0 ≤ u) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hmargin : 0 < 1+(1-m)*Coupled.xiPrime k lam u-L) :
    ContinuousAt (fun z : ℝ×ℝ => Coupled.trial k z.1 m L z.2) (lam,u) := by
  let a := Coupled.xiPrime k lam u
  have ha : 0 ≤ a := by unfold a Coupled.xiPrime; positivity
  have hA : 0 < 1+a-L := by change 0 < 1+(1-m)*a-L at hmargin; nlinarith
  have hB : 0 < 1+a+L := by linarith
  have hcA : Continuous (fun z : ℝ×ℝ => 1+Coupled.xiPrime k z.1 z.2-L) := by unfold Coupled.xiPrime; fun_prop
  have hcB : Continuous (fun z : ℝ×ℝ => 1+Coupled.xiPrime k z.1 z.2+L) := by unfold Coupled.xiPrime; fun_prop
  have hcD := continuous_margin k m L
  have hcT : Continuous (fun z : ℝ×ℝ => Coupled.theta k z.1 z.2) := by unfold Coupled.theta; fun_prop
  have hAat : ContinuousAt (fun z : ℝ×ℝ => 1+Coupled.xiPrime k z.1 z.2-L) (lam,u) := hcA.continuousAt
  have hBat : ContinuousAt (fun z : ℝ×ℝ => 1+Coupled.xiPrime k z.1 z.2+L) (lam,u) := hcB.continuousAt
  have hDat : ContinuousAt (fun z : ℝ×ℝ => 1+(1-m)*Coupled.xiPrime k z.1 z.2-L) (lam,u) := hcD.continuousAt
  have hratio : ContinuousAt (fun z : ℝ×ℝ => (1+Coupled.xiPrime k z.1 z.2-L)/
      (1+(1-m)*Coupled.xiPrime k z.1 z.2-L)) (lam,u) := hAat.div hDat hmargin.ne'
  have hlog : ContinuousAt (fun z : ℝ×ℝ => Real.log ((1+Coupled.xiPrime k z.1 z.2-L)/
      (1+(1-m)*Coupled.xiPrime k z.1 z.2-L))) (lam,u) := hratio.log (div_pos hA hmargin).ne'
  have hlogA : ContinuousAt (fun z : ℝ×ℝ => Real.log (1+Coupled.xiPrime k z.1 z.2-L)) (lam,u) := hAat.log hA.ne'
  have hlogB : ContinuousAt (fun z : ℝ×ℝ => Real.log (1+Coupled.xiPrime k z.1 z.2+L)) (lam,u) := hBat.log hB.ne'
  have hresult := ((((continuous_fst.pow 2).continuousAt.add (hcT.continuousAt.const_mul (1-m))).sub
    (continuous_snd.continuousAt.const_mul L)).add (hlog.const_mul (1/m))).sub
      ((hlogB.add hlogA).const_mul (1/2 : ℝ))
  convert hresult using 1
  funext z
  rfl

/-- A compact family of admissible trials has one positive improvement and
one positive margin, uniformly on the macroscopic parameter rectangle. -/
theorem compact_improving_trials (k : ℕ) (hk : 3 ≤ k) {barLam eps : ℝ}
    (hbar : 0 ≤ barLam) (hsub : barLam < Scalar.lambdaC k) (heps : eps ∈ Ioc (0 : ℝ) 1) :
    ∃ gamma rho : ℝ, ∃ K : Set (Fin 4 → ℝ), 0 < gamma ∧ 0 < rho ∧ IsCompact K ∧
      (∀ p ∈ K, Coupled.Admissible k barLam p ∧
        rho ≤ 1+(1-p 1)*Coupled.xiPrime k (p 0) (p 3)-p 2) ∧
      ∀ lam ∈ Icc (0 : ℝ) barLam, ∀ u ∈ Icc eps 1,
        ∃ p ∈ K, p 0 = lam ∧ p 3 = u ∧
          Coupled.trial k (p 0) (p 1) (p 2) (p 3) ≤ lam^2-gamma := by
  classical
  let S : Set (ℝ×ℝ) := (Icc (0 : ℝ) barLam) ×ˢ (Icc eps 1)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hex : ∀ x : S, ∃ m L : ℝ, m ∈ Icc (1 : ℝ) 2 ∧ L ∈ Icc (0 : ℝ) 1 ∧
      0 < 1+(1-m)*Coupled.xiPrime k x.1.1 x.1.2-L ∧
        Coupled.trial k x.1.1 m L x.1.2 < x.1.1^2 := by
    intro x
    exact exists_improving_trial k hk x.2.1.1 (x.2.1.2.trans_lt hsub)
      ⟨heps.1.trans_le x.2.2.1, x.2.2.2⟩
  choose m L hm hL hr hg using hex
  let D : S → (ℝ×ℝ) → ℝ := fun x z => 1+(1-m x)*Coupled.xiPrime k z.1 z.2-L x
  let G : S → (ℝ×ℝ) → ℝ := fun x z => z.1^2-Coupled.trial k z.1 (m x) (L x) z.2
  let rhoAt : S → ℝ := fun x => D x x.1
  let gapAt : S → ℝ := fun x => G x x.1
  have hrho (x : S) : 0 < rhoAt x := hr x
  have hgap (x : S) : 0 < gapAt x := sub_pos.mpr (hg x)
  have hDcont (x : S) : Continuous (D x) := continuous_margin k (m x) (L x)
  have hGcont (x : S) : ContinuousAt (G x) x.1 := by
    have hfst : ContinuousAt (fun z : ℝ×ℝ => z.1^2) x.1 := (continuous_fst.pow 2).continuousAt
    have htrial := continuousAt_trial k ((heps.1.trans_le x.2.2.1).le) (hm x).1 (hL x).1 (hr x)
    exact hfst.sub htrial
  let U : S → Set (ℝ×ℝ) := fun x => interior {z | rhoAt x/2 < D x z ∧ gapAt x/2 < G x z}
  have hUx (x : S) : x.1 ∈ U x := by
    apply mem_interior_iff_mem_nhds.mpr
    have hnd : Ioi (rhoAt x/2) ∈ 𝓝 (D x x.1) := Ioi_mem_nhds (by change rhoAt x/2 < rhoAt x; linarith [hrho x])
    have hng : Ioi (gapAt x/2) ∈ 𝓝 (G x x.1) := Ioi_mem_nhds (by change gapAt x/2 < gapAt x; linarith [hgap x])
    exact Filter.inter_mem ((hDcont x).continuousAt.eventually hnd) ((hGcont x).eventually hng)
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U (fun _ => isOpen_interior)
    (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩, hUx ⟨z,hz⟩⟩)
  have htne : t.Nonempty := by
    have hz : ((0 : ℝ),eps) ∈ S := ⟨⟨le_rfl,hbar⟩,⟨le_rfl,heps.2⟩⟩
    obtain ⟨x,hxt,_⟩ := mem_iUnion₂.mp (ht hz)
    exact ⟨x,hxt⟩
  let rho : ℝ := t.inf' htne (fun x => rhoAt x/2)
  let gamma : ℝ := t.inf' htne (fun x => gapAt x/2)
  have hrhopos : 0 < rho := (Finset.lt_inf'_iff htne).mpr (fun x _ => half_pos (hrho x))
  have hgammapos : 0 < gamma := (Finset.lt_inf'_iff htne).mpr (fun x _ => half_pos (hgap x))
  have hrhole (x : S) (hx : x ∈ t) : rho ≤ rhoAt x/2 := Finset.inf'_le (f := fun x => rhoAt x/2) hx
  have hgammale (x : S) (hx : x ∈ t) : gamma ≤ gapAt x/2 := Finset.inf'_le (f := fun x => gapAt x/2) hx
  let V : S → Set (ℝ×ℝ) := fun x => S ∩ {z | rho ≤ D x z}
  let Kx : S → Set (Fin 4 → ℝ) := fun x => (fun z : ℝ×ℝ => trialParams z.1 (m x) (L x) z.2) '' V x
  let K : Set (Fin 4 → ℝ) := ⋃ x ∈ t, Kx x
  have hKx (x : S) : IsCompact (Kx x) :=
    (hS.inter_right (isClosed_le continuous_const (hDcont x))).image (continuous_trialParams (m x) (L x))
  have hK : IsCompact K := t.isCompact_biUnion (fun x _ => hKx x)
  have hKspec (p : Fin 4 → ℝ) (hp : p ∈ K) : Coupled.Admissible k barLam p ∧
      rho ≤ 1+(1-p 1)*Coupled.xiPrime k (p 0) (p 3)-p 2 := by
    obtain ⟨x,hxt,hpx⟩ := mem_iUnion₂.mp hp
    obtain ⟨z,hz,rfl⟩ := hpx
    obtain ⟨hp0,hp1,hp2,hp3⟩ := trialParams_apply z.1 (m x) (L x) z.2
    simp only [Coupled.Admissible,hp0,hp1,hp2,hp3]
    exact ⟨⟨hz.1.1,hm x,hL x,⟨heps.1.le.trans hz.1.2.1,hz.1.2.2⟩,
      hrhopos.trans_le hz.2⟩,hz.2⟩
  refine ⟨gamma,rho,K,hgammapos,hrhopos,hK,hKspec,?_⟩
  intro lam hlam u hu
  have hz : (lam,u) ∈ S := ⟨hlam,hu⟩
  obtain ⟨x,hxt,hU⟩ := mem_iUnion₂.mp (ht hz)
  have hineq : rhoAt x/2 < D x (lam,u) ∧ gapAt x/2 < G x (lam,u) :=
    (interior_subset : interior {z : ℝ×ℝ | rhoAt x/2 < D x z ∧ gapAt x/2 < G x z} ⊆
      {z : ℝ×ℝ | rhoAt x/2 < D x z ∧ gapAt x/2 < G x z}) hU
  have hV : (lam,u) ∈ V x := ⟨hz,(hrhole x hxt).trans hineq.1.le⟩
  refine ⟨trialParams lam (m x) (L x) u,mem_iUnion₂.mpr ⟨x,hxt,⟨(lam,u),hV,rfl⟩⟩,?_,?_,?_⟩
  · exact (trialParams_apply lam (m x) (L x) u).1
  · exact (trialParams_apply lam (m x) (L x) u).2.2.2
  · obtain ⟨hp0,hp1,hp2,hp3⟩ := trialParams_apply lam (m x) (L x) u
    rw [hp0,hp1,hp2,hp3]
    have hh := hgammale x hxt
    have hhgap := hineq.2
    change gapAt x/2 < lam^2-Coupled.trial k lam (m x) (L x) u at hhgap
    linarith

/-- Lemma 4.3 from the uniform coupled trial bound, supplied as an explicit
matrix/interpolation hypothesis. -/
theorem macroscopic_gap_of_trialBound (htrial : Coupled.CoupledTrialBound)
    (k : ℕ) (hk : 4 ≤ k) (heven : Even k) {barLam eps : ℝ}
    (hbar : 0 ≤ barLam) (hsub : barLam < Scalar.lambdaC k) (heps : eps ∈ Ioc (0 : ℝ) 1) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ lam ∈ Icc (0 : ℝ) barLam, ∀ u ∈ Icc eps 1, ∀ N : ℕ, 1 ≤ N →
        Coupled.expectedCoupledFreeEnergy N k lam u (1/(N : ℝ)) ≤
          ((lam^2-gamma+C*Real.log ((N : ℝ)+1)/(N : ℝ) : ℝ) : EReal) := by
  obtain ⟨gamma,rho,K,hgamma,hrho,hK,hKspec,hcover⟩ :=
    compact_improving_trials k (by omega) hbar hsub heps
  have hKad : K ⊆ {p | Coupled.Admissible k barLam p} := fun p hp => (hKspec p hp).1
  obtain ⟨C,hC,hbound⟩ := htrial k (by omega) heven barLam hbar K hK hKad
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C' : ℝ := C*(1+1/Real.log 2)
  have hC' : 0 < C' := mul_pos hC (by positivity)
  refine ⟨gamma,C',hgamma,hC',?_⟩
  intro lam hlam u hu N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : Real.log 2 ≤ Real.log ((N : ℝ)+1) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
  have hratio : 1 ≤ Real.log ((N : ℝ)+1)/Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa only [one_mul] using hlogN)
  have hrem : C/(N : ℝ)+C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤
      C'*Real.log ((N : ℝ)+1)/(N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hratio (div_pos hC hNpos).le
    calc
      _ ≤ (C/(N : ℝ))*(Real.log ((N : ℝ)+1)/Real.log 2)+
          C*Real.log ((N : ℝ)+1)/(N : ℝ) := by
        simpa only [mul_one] using add_le_add hh (le_rfl :
          C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤ C*Real.log ((N : ℝ)+1)/(N : ℝ))
      _ = _ := by unfold C'; ring
  obtain ⟨p,hp,hp0,hp3,hgap⟩ := hcover lam hlam u hu
  have hh := hbound p hp N hN (1/(N : ℝ)) (one_div_pos.mpr hNpos)
  rw [hp0,hp3] at hh hgap
  apply hh.trans
  have hreal : Coupled.trial k lam (p 1) (p 2) u+C*(1/(N : ℝ))+
      C*Real.log ((N : ℝ)+1)/(N : ℝ) ≤ lam^2-gamma+C'*Real.log ((N : ℝ)+1)/(N : ℝ) := by
    have hmul : C*(1/(N : ℝ)) = C/(N : ℝ) := by ring
    rw [hmul]
    linarith
  exact_mod_cast hreal

end
end TensorPCA.CoupledMacroscopicProofs
