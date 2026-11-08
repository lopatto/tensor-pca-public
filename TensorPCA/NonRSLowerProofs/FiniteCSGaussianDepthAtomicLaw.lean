-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecision
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianPushforwardAlgebra

/-! Arbitrary finite atomic CS laws. Cumulative heights include the zero initial and
mass-one terminal boundaries; the atom weights are their differences. No hierarchy
or zero-height cofinality is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthAtomicLaw
open MeasureTheory ProbabilityTheory Set
open FiniteCS RetainedCountProofs.CrisantiSommers
open FiniteCSGaussianDepthPrecision FiniteCSGaussianPushforwardAlgebra
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extend the interior cumulative heights by their boundary values.
-/
def cumulativeHeight {d : ℕ} (x : Fin d→ℝ) (i : ℕ) : ℝ :=
  if hi : i=0 then 0 else if hid : i≤d then x ⟨i-1,by omega⟩ else 1

theorem cumulativeHeight_zero {d : ℕ} (x : Fin d→ℝ) : cumulativeHeight x 0=0 := by simp [cumulativeHeight]
theorem cumulativeHeight_end {d : ℕ} (x : Fin d→ℝ) : cumulativeHeight x (d+1)=1 := by simp [cumulativeHeight]
theorem cumulativeHeight_succ {d : ℕ} (x : Fin d→ℝ) (j : Fin d) :
    cumulativeHeight x ((j : ℕ)+1)=x j := by
  simp only [cumulativeHeight,show ¬(j : ℕ)+1=0 by omega,show (j : ℕ)+1≤d by omega,dite_false,dite_true]
  congr 1

theorem cumulativeHeight_bounds {d : ℕ} {x : Fin d→ℝ} (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (i : ℕ) :
    0≤cumulativeHeight x i ∧ cumulativeHeight x i≤1 := by
  unfold cumulativeHeight
  split_ifs with hi hid
  · norm_num
  · exact ⟨hx _,hx1 _⟩
  · norm_num

theorem cumulativeHeight_monotone {d : ℕ} {x : Fin d→ℝ}
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) : Monotone (cumulativeHeight x) := by
  intro i l hil
  by_cases hi : i=0
  · rw [hi,cumulativeHeight_zero]
    exact (cumulativeHeight_bounds hx hx1 l).1
  · by_cases hl : l≤d
    · have hilD : i≤d := hil.trans hl
      have hl0 : l≠0 := by omega
      simp only [cumulativeHeight,hi,hl0,hilD,hl,dite_false,dite_true]
      apply hxm
      exact Nat.sub_le_sub_right hil 1
    · simpa only [cumulativeHeight,show l≠0 by omega,hl,dite_false] using (cumulativeHeight_bounds hx hx1 i).2

/-- Probability weights, including both boundary atoms.
-/
def atomWeight {d : ℕ} (x : Fin d→ℝ) (i : Fin (d+1)) : ℝ :=
  cumulativeHeight x ((i : ℕ)+1)-cumulativeHeight x i

theorem atomWeight_nonneg {d : ℕ} {x : Fin d→ℝ}
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (i : Fin (d+1)) : 0≤atomWeight x i :=
  sub_nonneg.mpr (cumulativeHeight_monotone hx hx1 hxm (Nat.le_succ i))

theorem atomWeight_sum {d : ℕ} (x : Fin d→ℝ) : (∑i : Fin (d+1),atomWeight x i)=1 := by
  have H := prefix_differences (d := d+1) (cumulativeHeight x) (d+1) le_rfl
  rw [prefix_end,cumulativeHeight_zero,cumulativeHeight_end] at H
  calc
    _= -(∑i : Fin (d+1),(cumulativeHeight x i-cumulativeHeight x ((i : ℕ)+1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold atomWeight
      ring
    _=1 := by rw [H]; norm_num

/-- The literal finite sum of weighted Dirac measures on the real line. -/
def atomicLaw {d : ℕ} (x : Fin d→ℝ) (r : Fin (d+1)→ℝ) : Measure ℝ :=
  ∑i : Fin (d+1),ENNReal.ofReal (atomWeight x i) •Measure.dirac (r i)

theorem atomicLaw_probability {d : ℕ} {x : Fin d→ℝ} (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) : IsProbabilityMeasure (atomicLaw x r) := by
  constructor
  simp only [atomicLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => atomWeight_nonneg hx hx1 hxm i),atomWeight_sum,ENNReal.ofReal_one]

theorem integral_atomicLaw {d : ℕ} {x : Fin d→ℝ} (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (f : ℝ→ℝ) :
    (∫a,f a∂atomicLaw x r)=∑i : Fin (d+1),atomWeight x i*f (r i) := by
  have hI (i : Fin (d+1)) : Integrable f (ENNReal.ofReal (atomWeight x i) •Measure.dirac (r i)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [atomicLaw,integral_finsetSum_measure (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_dirac,smul_eq_mul,ENNReal.toReal_ofReal (atomWeight_nonneg hx hx1 hxm i)]

theorem atomicLaw_hasCutoff {d : ℕ} (x : Fin d→ℝ) {r : Fin (d+1)→ℝ}
    (hr0 : 0≤r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1) : HasCutoff (atomicLaw x r) (r (Fin.last d)) := by
  refine ⟨hr0.trans (hrm (Fin.zero_le _)),hr1,?_⟩
  rw [atomicLaw,ae_finsetSum_measure_iff]
  intro i _
  apply Measure.ae_smul_measure
  simp only [ae_dirac_eq]
  exact ⟨hr0.trans (hrm (Fin.zero_le i)),hrm (Fin.le_last i)⟩

theorem weighted_sum_by_parts {d : ℕ} (x : Fin d→ℝ) (r : Fin (d+1)→ℝ) (f : ℝ→ℝ) :
    (∑i : Fin (d+1),atomWeight x i*f (r i))=
      f (r (Fin.last d))-
        ∑j : Fin d,x j*(f (r j.succ)-f (r j.castSucc)) := by
  unfold atomWeight
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,Fin.sum_univ_castSucc,Fin.sum_univ_succ]
  simp only [Fin.val_castSucc,Fin.val_last,Fin.val_zero,Fin.val_succ,
    cumulativeHeight_zero,cumulativeHeight_end,cumulativeHeight_succ,one_mul,zero_mul,zero_add]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

theorem xHat_atomicLaw {d : ℕ} {x : Fin d→ℝ} (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (t : ℝ) :
    xHat (atomicLaw x r) t=1-max t (r (Fin.last d))+
      ∑j : Fin d,x j*(max t (r j.succ)-max t (r j.castSucc)) := by
  unfold xHat
  rw [integral_atomicLaw r hx hx1 hxm,weighted_sum_by_parts]
  have H : (∑j : Fin d,x j*((1-max t (r j.succ))-(1-max t (r j.castSucc))))=
      -(∑j : Fin d,x j*(max t (r j.succ)-max t (r j.castSucc))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [H]
  ring

theorem xHat_atomicLaw_head {d : ℕ} {x : Fin d→ℝ} {r : Fin (d+1)→ℝ}
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hrm : Monotone r)
    {t : ℝ} (ht : t≤r 0) :
    xHat (atomicLaw x r) t=1-r (Fin.last d)+∑j : Fin d,x j*(r j.succ-r j.castSucc) := by
  have hm (i : Fin (d+1)) : max t (r i)=r i := max_eq_right (ht.trans (hrm (Fin.zero_le i)))
  rw [xHat_atomicLaw r hx hx1 hxm]
  simp_rw [hm]

def atomicTrial {d : ℕ} (x : Fin d→ℝ) (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hr0 : 0≤r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1) : Trial :=
  letI := atomicLaw_probability r hx hx1 hxm
  cutoffTrial (atomicLaw x r) (atomicLaw_hasCutoff x hr0 hrm hr1)

theorem realLaw_atomicTrial {d : ℕ} (x : Fin d→ℝ) (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hr0 : 0≤r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1) :
    realLaw (atomicTrial x r hx hx1 hxm hr0 hrm hr1)=atomicLaw x r := by
  letI := atomicLaw_probability r hx hx1 hxm
  exact realLaw_cutoffTrial _ _

theorem profile_atomicTrial {d : ℕ} (beta : ℝ) (x : Fin d→ℝ) (r : Fin (d+1)→ℝ)
    (hx : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x)
    (hr0 : 0≤r 0) (hrm : Monotone r) (hr1 : r (Fin.last d)<1) (t : ℝ) :
    profile beta (atomicTrial x r hx hx1 hxm hr0 hrm hr1) t=
      beta*(1-max t (r (Fin.last d))+∑j : Fin d,x j*(max t (r j.succ)-max t (r j.castSucc))) := by
  rw [profile_eq_scaled_xHat_realLaw,realLaw_atomicTrial,xHat_atomicLaw r hx hx1 hxm]

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthAtomicLaw
