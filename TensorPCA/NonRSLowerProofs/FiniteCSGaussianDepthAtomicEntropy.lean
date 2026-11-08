-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthAtomicLaw

/-! Ordinary integrated-CDF entropy for the arbitrary finite atomic law, with its
initial interval and terminal mass-one boundary retained.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthAtomicEntropy
open MeasureTheory ProbabilityTheory Set
open FiniteCS RetainedCountProofs.CrisantiSommers
open FiniteCSGaussianDepthPrecision FiniteCSGaussianPushforwardAlgebra FiniteCSGaussianDepthAtomicLaw
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem atomWeight_prefix {d : ℕ} (x : Fin d→ℝ) (i : Fin d) :
    prefixSum (atomWeight x) ((i : ℕ)+1)=x i := by
  have H := prefix_differences (d := d+1) (cumulativeHeight x) ((i : ℕ)+1) (by omega)
  have hneg : prefixSum (atomWeight x) ((i : ℕ)+1)=
      -prefixSum (fun j : Fin (d+1) => cumulativeHeight x j-cumulativeHeight x ((j : ℕ)+1)) ((i : ℕ)+1) := by
    unfold prefixSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [atomWeight,neg_sub,neg_zero]
  rw [hneg,H,cumulativeHeight_zero,cumulativeHeight_succ]
  ring

private theorem prefix_mul_const {d : ℕ} (f : Fin d→ℝ) (i : ℕ) (c : ℝ) :
    prefixSum (fun j => f j*c) i=prefixSum f i*c := by
  unfold prefixSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [zero_mul]

theorem xHat_atomicLaw_affine {d : ℕ} {x : Fin d→ℝ} {r : Fin (d+1)→ℝ}
    (hx : ∀j,0≤ x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hrm : Monotone r)
    (i : Fin d) {t : ℝ} (ht : t∈Icc (r i.castSucc) (r i.succ)) :
    xHat (atomicLaw x r) t=xHat (atomicLaw x r) (r i.succ)+x i*(r i.succ-t) := by
  have hhat (s : ℝ) : xHat (atomicLaw x r) s=
      ∑j : Fin (d+1),atomWeight x j*(1-max s (r j)) := by
    unfold xHat
    rw [integral_atomicLaw r hx hx1 hxm]
  have H : xHat (atomicLaw x r) t-xHat (atomicLaw x r) (r i.succ)=x i*(r i.succ-t) := by
    rw [hhat,hhat,← Finset.sum_sub_distrib]
    calc
      _=prefixSum (fun j : Fin (d+1) => atomWeight x j*(r i.succ-t)) ((i : ℕ)+1) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : (j : ℕ)< (i : ℕ)+1
        · have hrj : r j≤ t := (hrm (show j≤ i.castSucc by change (j : ℕ)≤ i; omega)).trans ht.1
          simp only [hji,ite_true,max_eq_left hrj,max_eq_left (hrj.trans ht.2)]
          ring
        · have hrj : r i.succ≤ r j := hrm (show i.succ≤ j by change (i : ℕ)+1≤ j; omega)
          simp only [hji,ite_false,max_eq_right hrj,max_eq_right (ht.2.trans hrj)]
          ring
      _=prefixSum (atomWeight x) ((i : ℕ)+1)*(r i.succ-t) := prefix_mul_const _ _ _
      _=x i*(r i.succ-t) := by rw [atomWeight_prefix]
  linarith only [H]

theorem xHat_atomicLaw_at_node {d : ℕ} {x : Fin d→ℝ} {r : Fin (d+1)→ℝ}
    (hx : ∀j,0≤ x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hrm : Monotone r) (i : Fin (d+1)) :
    xHat (atomicLaw x r) (r i)=1-r (Fin.last d)+
      tail (fun j : Fin d => x j*(r j.succ-r j.castSucc)) i := by
  rw [xHat_atomicLaw r hx hx1 hxm,max_eq_right (hrm (Fin.le_last i))]
  congr 1
  unfold tail
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : (i : ℕ)≤(j : ℕ)
  · have h0 : r i≤ r j.castSucc := hrm (show i≤ j.castSucc from hij)
    have h1 : r i≤ r j.succ := hrm (show i≤ j.succ by change (i : ℕ)≤(j : ℕ)+1; omega)
    simp only [hij,ite_true,max_eq_right h0,max_eq_right h1]
  · have h0 : r j.castSucc≤ r i := hrm (show j.castSucc≤ i by change (j : ℕ)≤(i : ℕ); omega)
    have h1 : r j.succ≤ r i := hrm (show j.succ≤ i by change (j : ℕ)+1≤(i : ℕ); omega)
    simp only [hij,ite_false,max_eq_left h0,max_eq_left h1,sub_self,mul_zero]

theorem integral_inverse_xHat_atomicLaw {d : ℕ} {x : Fin d→ℝ} {r D : Fin (d+1)→ℝ}
    (hx : ∀j,0< x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hr0 : 0≤ r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1)
    (hD : ∀i,0< D i) (hhat : ∀i,xHat (atomicLaw x r) (r i)=1/D i) :
    (∫t in (0 : ℝ)..r (Fin.last d),(xHat (atomicLaw x r) t)⁻¹)=
      r 0*D 0+∑j : Fin d,Real.log (D j.succ/D j.castSucc)/x j := by
  letI := atomicLaw_probability r (fun j => (hx j).le) hx1 hxm
  have hcut := atomicLaw_hasCutoff x hr0 hrm hr1
  have hhead : (∫t in (0 : ℝ)..r 0,(xHat (atomicLaw x r) t)⁻¹)=r 0*D 0 := by
    calc
      _=∫t in (0 : ℝ)..r 0,(1/D 0 : ℝ)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr0] at ht
        have H := xHat_atomicLaw_head (fun j => (hx j).le) hx1 hxm hrm ht.2
        have H0 := xHat_atomicLaw_head (fun j => (hx j).le) hx1 hxm hrm (t := r 0) le_rfl
        rw [hhat 0] at H0
        dsimp only
        congr 1
        linarith only [H,H0]
      _=_ := by simp
  have hsegment (j : Fin d) :
      (∫t in r j.castSucc..r j.succ,(xHat (atomicLaw x r) t)⁻¹)=Real.log (D j.succ/D j.castSucc)/x j := by
    have hab : r j.castSucc≤ r j.succ := hrm (by change (j : ℕ)≤(j : ℕ)+1; omega)
    have hleft := xHat_atomicLaw_affine (fun l => (hx l).le) hx1 hxm hrm j ⟨le_rfl,hab⟩
    rw [hhat j.castSucc,hhat j.succ] at hleft
    calc
      _=∫t in r j.castSucc..r j.succ,(1/D j.succ+x j*(r j.succ-t))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        dsimp only
        rw [xHat_atomicLaw_affine (fun l => (hx l).le) hx1 hxm hrm j ht,hhat j.succ]
      _=_ := by
        rw [integral_inverse_affine_segment hab (one_div_pos.mpr (hD j.succ)) (hx j),← hleft]
        congr 2
        field_simp
  have hI (j : Fin d) : IntervalIntegrable (fun t => (xHat (atomicLaw x r) t)⁻¹) volume (r j.castSucc) (r j.succ) :=
    inverse_xHat_intervalIntegrable _ hcut ((hrm (Fin.le_last _)).trans_lt hr1) ((hrm (Fin.le_last _)).trans_lt hr1)
  let a : ℕ→ℝ := fun i => r ⟨min i d,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have ha0 : a 0=r 0 := by dsimp only [a]; apply congrArg r; apply Fin.ext; simp
  have had : a d=r (Fin.last d) := by dsimp only [a]; apply congrArg r; apply Fin.ext; simp
  have haj (j : Fin d) : a j=r j.castSucc := by dsimp only [a]; apply congrArg r; apply Fin.ext; exact Nat.min_eq_left j.isLt.le
  have haj1 (j : Fin d) : a ((j : ℕ)+1)=r j.succ := by
    dsimp only [a]
    apply congrArg r
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  have hchain := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := d)
    (f := fun t => (xHat (atomicLaw x r) t)⁻¹) (μ := volume) (fun j hj => by
      rw [show a j=r (⟨j,hj⟩ : Fin d).castSucc from haj ⟨j,hj⟩,
        show a (j+1)=r (⟨j,hj⟩ : Fin d).succ from haj1 ⟨j,hj⟩]
      exact hI ⟨j,hj⟩)
  have hsum : (∑j : Fin d,Real.log (D j.succ/D j.castSucc)/x j)=
      ∫t in r 0..r (Fin.last d),(xHat (atomicLaw x r) t)⁻¹ := by
    calc
      _=∑j : Fin d,∫t in r j.castSucc..r j.succ,(xHat (atomicLaw x r) t)⁻¹ :=
        Finset.sum_congr rfl (fun j _ => (hsegment j).symm)
      _=∑j : Fin d,∫t in a j..a ((j : ℕ)+1),(xHat (atomicLaw x r) t)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [haj,haj1]
      _=∑j∈Finset.range d,∫t in a j..a (j+1),(xHat (atomicLaw x r) t)⁻¹ := Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫t in a j..a (j+1),(xHat (atomicLaw x r) t)⁻¹) d
      _=_ := by rw [hchain,ha0,had]
  have h00 := inverse_xHat_intervalIntegrable (atomicLaw x r) hcut
    (a := 0) (b := r 0) (by norm_num) ((hrm (Fin.zero_le _)).trans_lt hr1)
  have h01 := inverse_xHat_intervalIntegrable (atomicLaw x r) hcut
    (a := r 0) (b := r (Fin.last d)) ((hrm (Fin.zero_le _)).trans_lt hr1) hr1
  rw [← intervalIntegral.integral_add_adjacent_intervals h00 h01,hhead,hsum]

theorem functional_atomicLaw_eval {d : ℕ} {x : Fin d→ℝ} {r D : Fin (d+1)→ℝ}
    (hx : ∀j,0< x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hr0 : 0≤ r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1)
    (hD : ∀i,0< D i) (hhat : ∀i,xHat (atomicLaw x r) (r i)=1/D i) (beta : ℝ) (xi : ℝ→ℝ) :
    2*functional beta xi (atomicLaw x r) (r (Fin.last d))=
      beta^2*(xi 1-∑i : Fin (d+1),atomWeight x i*xi (r i))+
      r 0*D 0+(∑j : Fin d,Real.log (D j.succ/D j.castSucc)/x j)-Real.log (D (Fin.last d)) := by
  have hm (i : Fin (d+1)) : max (r (Fin.last d)) (r i)=r (Fin.last d) := max_eq_left (hrm (Fin.le_last i))
  have H := xHat_atomicLaw r (fun j => (hx j).le) hx1 hxm (r (Fin.last d))
  simp_rw [hm] at H
  simp only [sub_self,mul_zero,Finset.sum_const_zero,add_zero] at H
  have hterm : 1-r (Fin.last d)=1/D (Fin.last d) := H.symm.trans (hhat _)
  unfold functional
  rw [integral_atomicLaw r (fun j => (hx j).le) hx1 hxm,
    integral_inverse_xHat_atomicLaw hx hx1 hxm hr0 hrm hr1 hD hhat,
    hterm,Real.log_div one_ne_zero (hD _).ne',Real.log_one]
  ring

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthAtomicEntropy
