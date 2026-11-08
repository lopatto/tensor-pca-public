-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A prechosen finite family of disjoint CLOSED boundary bands and literal
continuous increasing ramps. The geometry is independent of every probability
law; only a good index is selected after the law is known. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGBoundaryBands
open MeasureTheory Set
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def spacing (a b : ℝ) (J : ℕ) : ℝ := (b-a)/((J : ℝ)+1)
def radius (a b : ℝ) (J : ℕ) : ℝ := spacing a b J/4
def threshold (a b : ℝ) (J : ℕ) (j : Fin J) : ℝ := a+((j : ℝ)+1)*spacing a b J
def band (a b : ℝ) (J : ℕ) (j : Fin J) : Set ℝ :=
  Icc (threshold a b J j-radius a b J) (threshold a b J j+radius a b J)
def ramp (a b : ℝ) (J : ℕ) (j : Fin J) (r : ℝ) : ℝ :=
  max 0 (min 1 ((r-(threshold a b J j-radius a b J))/(2*radius a b J)))

 theorem spacing_pos {a b : ℝ} (hab : a<b) (J : ℕ) : 0<spacing a b J := by unfold spacing; positivity
 theorem radius_pos {a b : ℝ} (hab : a<b) (J : ℕ) : 0<radius a b J := by
  unfold radius
  exact div_pos (spacing_pos hab J) (by norm_num)

 theorem band_endpoints {a b : ℝ} (hab : a<b) (J : ℕ) (j : Fin J) :
    a<threshold a b J j-radius a b J ∧ threshold a b J j+radius a b J<b := by
  have hs := spacing_pos hab J
  have he : ((J : ℝ)+1)*spacing a b J=b-a := by
    unfold spacing
    have hd : (J : ℝ)+1≠0 := by positivity
    field_simp
  have hj0 : 0≤(j : ℝ) := Nat.cast_nonneg j.val
  have hj1 : (j : ℝ)+1≤J := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hp0 := mul_nonneg hj0 hs.le
  have hp1 := mul_le_mul_of_nonneg_right hj1 hs.le
  unfold threshold radius
  constructor <;> nlinarith only [he,hp0,hp1,hs]

 theorem threshold_mem {a b : ℝ} (hab : a<b) (J : ℕ) (j : Fin J) : threshold a b J j∈Ioo a b := by
  have h := band_endpoints hab J j
  have hr := radius_pos hab J
  constructor <;> linarith only [h.1,h.2,hr]

 theorem band_subset_interval {a b : ℝ} (hab : a<b) (J : ℕ) (j : Fin J) : band a b J j⊆Ioo a b := by
  have h := band_endpoints hab J j
  intro r hr
  exact ⟨h.1.trans_le hr.1,hr.2.trans_lt h.2⟩

 theorem bands_disjoint {a b : ℝ} (hab : a<b) (J : ℕ) {i j : Fin J} (hij : i≠j) :
    Disjoint (band a b J i) (band a b J j) := by
  have hs := spacing_pos hab J
  have hOrdered {i j : Fin J} (hij : i<j) : threshold a b J i+radius a b J<threshold a b J j-radius a b J := by
    have hc : (i : ℝ)+1≤j := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have H := mul_le_mul_of_nonneg_right hc hs.le
    unfold threshold radius
    nlinarith only [H,hs]
  apply Set.disjoint_left.mpr
  intro r hi hj
  rcases lt_or_gt_of_ne hij with h|h
  · have H := hOrdered h
    exact (not_lt_of_ge (hj.1.trans hi.2)) H
  · have H := hOrdered h
    exact (not_lt_of_ge (hi.1.trans hj.2)) H

 theorem ramp_continuous (a b : ℝ) (J : ℕ) (j : Fin J) : Continuous (ramp a b J j) := by
  unfold ramp
  fun_prop

 theorem ramp_mem (a b : ℝ) (J : ℕ) (j : Fin J) (r : ℝ) : ramp a b J j r∈Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

 theorem ramp_zero_of_le {a b : ℝ} (hab : a<b) (J : ℕ) (j : Fin J) {r : ℝ}
    (hr : r≤threshold a b J j-radius a b J) : ramp a b J j r=0 := by
  have hh := radius_pos hab J
  have hScore : (r-(threshold a b J j-radius a b J))/(2*radius a b J)≤0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (by positivity)
  unfold ramp
  exact max_eq_left ((min_le_right _ _).trans hScore)

 theorem ramp_one_of_ge {a b : ℝ} (hab : a<b) (J : ℕ) (j : Fin J) {r : ℝ}
    (hr : threshold a b J j+radius a b J≤r) : ramp a b J j r=1 := by
  have hh := radius_pos hab J
  have hScore : 1≤(r-(threshold a b J j-radius a b J))/(2*radius a b J) := by
    apply (le_div_iff₀ (by positivity : 0<2*radius a b J)).mpr
    linarith only [hr]
  simp only [ramp,min_eq_left hScore,max_eq_right zero_le_one]

 theorem ramp_indicator_error_le_band {a b : ℝ} (hab : a<b) (J : ℕ) (j : Fin J) (r : ℝ) :
    |ramp a b J j r-(Ici (threshold a b J j)).indicator (fun _ ↦ (1 : ℝ)) r|≤
      (band a b J j).indicator (fun _ ↦ (1 : ℝ)) r := by
  have hm := ramp_mem a b J j r
  have hh := radius_pos hab J
  by_cases hr : r∈band a b J j
  · rw [indicator_of_mem hr]
    by_cases ht : threshold a b J j≤r
    · rw [indicator_of_mem (show r∈Ici (threshold a b J j) from ht),abs_of_nonpos (by linarith [hm.2])]
      linarith [hm.1]
    · rw [indicator_of_notMem (show r∉Ici (threshold a b J j) from ht),sub_zero,abs_of_nonneg hm.1]
      exact hm.2
  · rw [indicator_of_notMem hr]
    by_cases hLeft : r≤threshold a b J j-radius a b J
    · rw [ramp_zero_of_le hab J j hLeft,indicator_of_notMem (show r∉Ici (threshold a b J j) by
        change ¬threshold a b J j≤r
        linarith only [hLeft,hh])]
      norm_num
    · have hRight : threshold a b J j+radius a b J≤r := by
        by_contra h
        exact hr ⟨le_of_not_ge hLeft,le_of_lt (lt_of_not_ge h)⟩
      rw [ramp_one_of_ge hab J j hRight,indicator_of_mem (show r∈Ici (threshold a b J j) by
        change threshold a b J j≤r
        linarith only [hRight,hh])]
      norm_num

 theorem band_mass_sum_le_one {a b : ℝ} (hab : a<b) (J : ℕ)
    (rho : Measure ℝ) [IsProbabilityMeasure rho] : (∑j : Fin J,rho.real (band a b J j))≤1 := by
  have H := sum_measureReal_le_measureReal_univ (μ := rho) (s := Finset.univ)
    (fun j _ ↦ measurableSet_Icc) (fun i _ j _ hij ↦ bands_disjoint hab J hij)
  rwa [probReal_univ] at H

 theorem exists_small_band {a b : ℝ} (hab : a<b) {J : ℕ} (hJ : 0<J)
    (rho : Measure ℝ) [IsProbabilityMeasure rho] : ∃j : Fin J,rho.real (band a b J j)≤1/(J : ℝ) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  by_contra h
  push_neg at h
  have H := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ ↦ h j)
  have he : (∑_j : Fin J,1/(J : ℝ))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hJ0 : (J : ℝ)≠0 := by exact_mod_cast hJ.ne'
    field_simp
  rw [he] at H
  linarith [band_mass_sum_le_one hab J rho]

end
end TensorPCA.NonRSLowerProofs.FiniteGGBoundaryBands
