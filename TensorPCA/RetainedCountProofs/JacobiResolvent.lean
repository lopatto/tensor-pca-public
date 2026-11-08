-- SPDX-License-Identifier: Apache-2.0
/- Attributed finite Jacobi resolvent source proof from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/PathSpectra.lean (upstream
   openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). We retain only
   the genuine Hermite/Riccati equation and its elementary outside-resolvent
   consequence. A coarse fixed-pole bound suffices for weak convergence;
   no spectral-edge estimate or empirical-limit assumption is imported.
   See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.JacobiSupport
public import TensorPCA.RetainedCountProofs.SemicirclePotentialIntegralProofs
@[expose] public section
noncomputable section
open Matrix Polynomial Filter Set
open scoped BigOperators Topology
namespace TensorPCA.RetainedCountProofs.JacobiMatrix
open SemicirclePotential.OutsideFormula
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def empiricalResolvent {ι : Type*} [Fintype ι] (e : ι → ℝ) (s : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (s + e i)⁻¹

def empiricalResolventSquare {ι : Type*} [Fintype ι] (e : ι → ℝ) (s : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (s + e i)⁻¹ ^ 2


section
variable {ι : Type*} [Fintype ι] [Nonempty ι] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)

include he

lemma empiricalResolvent_pos {s : ℝ} (hs : 0 < s) : 0 < empiricalResolvent e s := by
  unfold empiricalResolvent
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  exact Finset.sum_pos (fun i _ => inv_pos.mpr (add_pos_of_pos_of_nonneg hs (he i))) Finset.univ_nonempty

lemma empiricalResolventSquare_pos {s : ℝ} (hs : 0 < s) : 0 < empiricalResolventSquare e s := by
  unfold empiricalResolventSquare
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr
    (add_pos_of_pos_of_nonneg hs (he i)))) Finset.univ_nonempty

lemma empiricalResolvent_le_inv {s : ℝ} (hs : 0 < s) : empiricalResolvent e s ≤ s⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, s⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      apply Finset.sum_le_sum
      intro i _
      exact (inv_le_inv₀ (add_pos_of_pos_of_nonneg hs (he i)) hs).mpr (le_add_of_nonneg_right (he i))
    _ = s⁻¹ := by simp [hn.ne']

omit [Nonempty ι] in
lemma empiricalResolvent_continuousOn : ContinuousOn (empiricalResolvent e) (Set.Ioi 0) := by
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.inv₀ (continuousOn_id.add continuousOn_const)
  intro s hs
  exact ne_of_gt (add_pos_of_pos_of_nonneg hs (he i))

omit [Nonempty ι] in
lemma empiricalResolvent_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (empiricalResolvent e) (-empiricalResolventSquare e s) s := by
  have h (i : ι) : HasDerivAt (fun u : ℝ => (u + e i)⁻¹) (-(s + e i)⁻¹ ^ 2) s := by
    convert! ((hasDerivAt_id s).add_const (e i)).inv (ne_of_gt
      (add_pos_of_pos_of_nonneg hs (he i))) using 1
    simp only [neg_div, one_div, inv_pow, id_eq]
  convert! (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).const_mul
    (Fintype.card ι : ℝ)⁻¹ using 1
  simp only [empiricalResolventSquare, Finset.sum_neg_distrib, mul_neg]

lemma empiricalResolvent_lt_midpoint
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) : empiricalResolvent e s < (2 + s) / 2 := by
  by_contra hbad
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  let f : ℝ → ℝ := fun u => (2 + u) / 2 - empiricalResolvent e u
  have hfs : f s ≤ 0 := by dsimp [f]; linarith
  have hft : 0 ≤ f (s + 2) := by
    have hb := empiricalResolvent_le_inv e he (show 0 < s + 2 by linarith)
    have hinv : (s + 2)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
    dsimp [f]
    linarith
  have hc : ContinuousOn f (Set.Icc s (s + 2)) := by
    apply ContinuousOn.sub
    · exact (continuous_const.add continuous_id).continuousOn.div_const 2
    · exact (empiricalResolvent_continuousOn e he).mono (fun u hu => lt_of_lt_of_le hs hu.1)
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc (show s ≤ s + 2 by linarith) hc ⟨hfs, hft⟩
  have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
  have hid := hR u hu0
  have ht : 0 < empiricalResolventSquare e u / Fintype.card ι :=
    div_pos (empiricalResolventSquare_pos e he hu0) hn
  dsimp [f] at hzero
  nlinarith

lemma empiricalResolvent_lt_semicircle
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) : empiricalResolvent e s < semicircleResolvent s := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hmid := empiricalResolvent_lt_midpoint e he hR hs
  have hid := hR s hs
  have ht : 0 < empiricalResolventSquare e s / Fintype.card ι :=
    div_pos (empiricalResolventSquare_pos e he hs) hn
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  have hpos := Real.sqrt_nonneg (s * (4 + s))
  unfold semicircleResolvent
  nlinarith

lemma empiricalResolvent_root_difference
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ semicircleResolvent s - empiricalResolvent e s ∧
      semicircleResolvent s - empiricalResolvent e s ≤
        empiricalResolventSquare e s /
          ((Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s))) := by
  have hd := (empiricalResolvent_lt_semicircle e he hR hs).le
  refine ⟨sub_nonneg.mpr hd, ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpos : 0 < Real.sqrt (s * (4 + s)) := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  have hid := hR s hs
  apply (le_div_iff₀ (mul_pos hn hpos)).mpr
  have hid' := (eq_div_iff hn.ne').mp hid
  unfold semicircleResolvent at *
  nlinarith [sq_nonneg ((2 + s - Real.sqrt (s * (4 + s))) / 2 - empiricalResolvent e s)]


end

noncomputable def jacobiGaps (n : ℕ) (i : Fin n) : ℝ :=
  2 - (jacobi_hermitian (n : ℝ)⁻¹ n).eigenvalues i

lemma jacobiGaps_nonneg (n : ℕ) (i : Fin n) : 0 ≤ jacobiGaps n i := by
  have := (abs_le.mp (jacobi_eigenvalue_bound n i)).2
  exact sub_nonneg.mpr this

lemma hermitian_charpoly_derivative_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {z : ℝ} (hz : A.charpoly.eval z ≠ 0) :
    A.charpoly.derivative.eval z / A.charpoly.eval z = ∑ i, (z - hA.eigenvalues i)⁻¹ := by
  rw [hA.splits_charpoly.eval_derivative_div_eval_of_ne_zero hz,
    hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp [one_div]

lemma jacobi_charpoly_nonzero {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (jacobi (n : ℝ)⁻¹ n).charpoly.eval (2 + s) ≠ 0 := by
  rw [(jacobi_hermitian (n : ℝ)⁻¹ n).charpoly_eq, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [eval_sub, eval_X, eval_C, RCLike.ofReal_real_eq_id, id_eq]
  have := jacobiGaps_nonneg n i
  dsimp [jacobiGaps] at this
  linarith

lemma jacobi_logarithmic_ratio {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (jacobi (n : ℝ)⁻¹ n).charpoly.derivative.eval (2 + s) /
      (jacobi (n : ℝ)⁻¹ n).charpoly.eval (2 + s) =
        (n : ℝ) * empiricalResolvent (jacobiGaps n) s := by
  by_cases hn : n = 0
  · subst n
    simp [empiricalResolvent]
  · rw [hermitian_charpoly_derivative_ratio _ (jacobi_hermitian (n : ℝ)⁻¹ n)
      (jacobi_charpoly_nonzero hs)]
    simp only [empiricalResolvent, Fintype.card_fin, ← mul_assoc,
      mul_inv_cancel₀ (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn), one_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [jacobiGaps]
    ring

lemma jacobi_riccati {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    (empiricalResolvent (jacobiGaps n) s) ^ 2 -
      (2 + s) * empiricalResolvent (jacobiGaps n) s + 1 =
        empiricalResolventSquare (jacobiGaps n) s / n := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let p := (jacobi (n : ℝ)⁻¹ n).charpoly
  have hp : p.eval (2 + s) ≠ 0 := jacobi_charpoly_nonzero hs
  have hpd : HasDerivAt (fun u : ℝ => p.eval (2 + u)) (p.derivative.eval (2 + s)) s := by
    convert! (p.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    simp only [mul_one]
  have hpdd : HasDerivAt (fun u : ℝ => p.derivative.eval (2 + u))
      (p.derivative.derivative.eval (2 + s)) s := by
    convert! (p.derivative.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    simp only [mul_one]
  have hratio : HasDerivAt (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u)))
      ((n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2)) s := by
    convert! (hpdd.div hpd hp).const_mul (n : ℝ)⁻¹ using 1
  have hlocal : (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u))) =ᶠ[𝓝 s]
        empiricalResolvent (jacobiGaps n) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [jacobi_logarithmic_ratio hu, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
  have hder := (hratio.congr_of_eventuallyEq hlocal.symm).unique
    (empiricalResolvent_hasDerivAt (jacobiGaps n) (jacobiGaps_nonneg n) hs)
  have hode := congrArg (Polynomial.eval (2 + s)) (scaledHermite_differential (n : ℝ)⁻¹ n)
  rw [← jacobi_charpoly (inv_nonneg.mpr hnR.le) n] at hode
  rw [eval_zero] at hode
  change (C (n : ℝ)⁻¹ * p.derivative.derivative - X * p.derivative + C (n : ℝ) * p).eval (2 + s) = 0 at hode
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X] at hode
  have hv := jacobi_logarithmic_ratio (n := n) hs
  change p.derivative.eval (2 + s) / p.eval (2 + s) =
    (n : ℝ) * empiricalResolvent (jacobiGaps n) s at hv
  change (n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2) =
      -empiricalResolventSquare (jacobiGaps n) s at hder
  field_simp [hnR.ne', hp] at hode hv hder ⊢
  rw [hv] at hode hder
  have hh : (n : ℝ) * p.eval (2 + s) ^ 2 *
      ((n : ℝ) * (empiricalResolvent (jacobiGaps n) s *
        (empiricalResolvent (jacobiGaps n) s - (2 + s)) + 1) -
        empiricalResolventSquare (jacobiGaps n) s) = 0 := by
    linear_combination p.eval (2 + s) * hode - hder
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero hnR.ne' (pow_ne_zero 2 hp)))


/-- A fixed outside pole needs only the elementary reciprocal-square bound. -/
lemma empiricalResolventSquare_le_inv_sq {ι : Type*} [Fintype ι] [Nonempty ι]
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) {s : ℝ} (hs : 0 < s) :
    empiricalResolventSquare e s ≤ s⁻¹ ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  unfold empiricalResolventSquare
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, s⁻¹ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      apply Finset.sum_le_sum
      intro i _
      apply pow_le_pow_left₀ (inv_nonneg.mpr (add_nonneg hs.le (he i)))
      exact (inv_le_inv₀ (add_pos_of_pos_of_nonneg hs (he i)) hs).mpr
        (le_add_of_nonneg_right (he i))
    _ = _ := by simp [hn.ne']

/-- The actual finite Jacobi transform approaches the semicircle transform
at each fixed outside pole, with an explicit elementary error. -/
lemma jacobi_resolvent_error {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    0 ≤ semicircleResolvent s - empiricalResolvent (jacobiGaps n) s ∧
    semicircleResolvent s - empiricalResolvent (jacobiGaps n) s ≤
      s⁻¹ ^ 2 / ((n : ℝ) * Real.sqrt (s * (4 + s))) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hR : ∀ u : ℝ, 0 < u →
      (empiricalResolvent (jacobiGaps n) u) ^ 2 -
        (2 + u) * empiricalResolvent (jacobiGaps n) u + 1 =
          empiricalResolventSquare (jacobiGaps n) u / Fintype.card (Fin n) := by
    intro u hu
    simpa using jacobi_riccati hn hu
  have hd := empiricalResolvent_root_difference (jacobiGaps n) (jacobiGaps_nonneg n) hR hs
  simp only [Fintype.card_fin] at hd
  refine ⟨hd.1, hd.2.trans ?_⟩
  apply div_le_div_of_nonneg_right
  · exact empiricalResolventSquare_le_inv_sq _ (jacobiGaps_nonneg n) hs
  · positivity

/-- Genuine deterministic Jacobi resolvent convergence, with no spectral
asymptotic supplied as a premise. -/
theorem jacobi_resolvent_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => empiricalResolvent (jacobiGaps (n+1)) s) atTop
      (𝓝 (semicircleResolvent s)) := by
  have hdisc : 0 < Real.sqrt (s * (4 + s)) :=
    Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have ht : Tendsto (fun n : ℕ => s⁻¹ ^ 2 /
      ((n+1 : ℝ)*Real.sqrt (s*(4+s)))) atTop (𝓝 0) :=
    (hn.atTop_mul_const hdisc).const_div_atTop _
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with n he
  have hd := jacobi_resolvent_error (Nat.succ_pos n) hs
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hd.1]
  simp only [Nat.cast_succ] at hd
  exact hd.2.trans_lt he

end TensorPCA.RetainedCountProofs.JacobiMatrix
