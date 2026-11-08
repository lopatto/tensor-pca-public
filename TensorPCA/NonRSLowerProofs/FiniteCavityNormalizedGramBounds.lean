-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityRadiusBounds

/-! Signed normalized-Gram support and errors for the finite cavity reference. The
cavity Gram constraint c^2≤s*s' is explicit; a bound |c|≤L alone would not imply the
required unit-interval support.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityNormalizedGramBounds
open Set FiniteCavityRadiusBounds
noncomputable section

theorem normalizedGram_abs_le_one {r r' s s' R c : ℝ}
    (hr : 0<r) (hr' : 0<r') (hs : 0≤s) (hs' : 0≤s')
    (hR : |R|≤1) (hc : c^2≤s*s') :
    |(r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s'))|≤1 := by
  have hC : 0<Real.sqrt ((r^2+s)*(r'^2+s')) := by positivity
  have hcabs : |c|≤Real.sqrt (s*s') := Real.abs_le_sqrt hc
  have hsqrt : (Real.sqrt (s*s'))^2=s*s' := Real.sq_sqrt (mul_nonneg hs hs')
  have hsq1 : (r*Real.sqrt s')^2=r^2*s' := by rw [mul_pow,Real.sq_sqrt hs']
  have hsq2 : (r'*Real.sqrt s)^2=r'^2*s := by rw [mul_pow,Real.sq_sqrt hs]
  have hcross : 2*r*r'*Real.sqrt (s*s')≤r^2*s'+r'^2*s := by
    rw [Real.sqrt_mul hs]
    nlinarith only [sq_nonneg (r*Real.sqrt s'-r'*Real.sqrt s),hsq1,hsq2]
  have hnorm : r*r'+Real.sqrt (s*s')≤Real.sqrt ((r^2+s)*(r'^2+s')) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hcross,hsqrt]
  rw [abs_div,abs_of_pos hC]
  apply (div_le_one hC).2
  calc
    _ ≤ |r*r'*R|+|c| := abs_add_le _ _
    _ ≤ r*r'+Real.sqrt (s*s') := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg hr.le hr'.le)]
      exact add_le_add (mul_le_of_le_one_right (mul_nonneg hr.le hr'.le) hR) hcabs
    _ ≤ _ := hnorm

private theorem sqrt_radius_factor {r s : ℝ} (hr : 0<r) (hs : 0≤s) :
    Real.sqrt (r^2+s)=r*Real.sqrt (1+s/r^2) := by
  have hrne : r≠0 := ne_of_gt hr
  have hid : r^2+s=r^2*(1+s/r^2) := by field_simp
  rw [hid,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]

theorem normalizedGram_shell_bounds {n L e r r' s s' R c : ℝ}
    (hn : 0<n) (hL : 0≤L) (he0 : 0≤e) (he1 : e≤1/2)
    (hr : 0≤r) (hr' : 0≤r') (hs : s∈Icc (0 : ℝ) L) (hs' : s'∈Icc (0 : ℝ) L)
    (hbox : r^2/n∈Icc (1-e) (1+e)) (hbox' : r'^2/n∈Icc (1-e) (1+e))
    (hR : |R|≤1) (hc : c^2≤s*s') :
    0<Real.sqrt ((r^2+s)*(r'^2+s')) ∧
    |(r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s'))|≤1 ∧
    |(r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s'))-R|≤4*L/n ∧ |c|≤L := by
  have hlo := (le_div_iff₀ hn).mp hbox.1
  have hlo' := (le_div_iff₀ hn).mp hbox'.1
  have hne : n*e≤n/2 := by convert mul_le_mul_of_nonneg_left he1 hn.le using 1 <;> ring
  have hhalf : n/2≤r^2 := by nlinarith only [hlo,hne]
  have hhalf' : n/2≤r'^2 := by nlinarith only [hlo',hne]
  have hrpos : 0<r := by nlinarith only [hhalf,hn,hr]
  have hr'pos : 0<r' := by nlinarith only [hhalf',hn,hr']
  have hsq : 0<r^2 := by positivity
  have hsq' : 0<r'^2 := by positivity
  let C := Real.sqrt ((r^2+s)*(r'^2+s'))
  let a := s/r^2
  let b := s'/r'^2
  have ha0 : 0≤a := div_nonneg hs.1 hsq.le
  have hb0 : 0≤b := div_nonneg hs'.1 hsq'.le
  have ha : a≤2*L/n := by
    apply (div_le_div_iff₀ hsq hn).2
    nlinarith only [mul_le_mul_of_nonneg_left hs.2 hn.le,mul_le_mul_of_nonneg_left hhalf hL]
  have hb : b≤2*L/n := by
    apply (div_le_div_iff₀ hsq' hn).2
    nlinarith only [mul_le_mul_of_nonneg_left hs'.2 hn.le,mul_le_mul_of_nonneg_left hhalf' hL]
  have hC : 0<C := Real.sqrt_pos.2
    (mul_pos (add_pos_of_pos_of_nonneg hsq hs.1) (add_pos_of_pos_of_nonneg hsq' hs'.1))
  have hhalfC : n/2≤C := by
    apply Real.le_sqrt_of_sq_le
    have h1 : n/2≤r^2+s := by linarith only [hhalf,hs.1]
    have h2 : n/2≤r'^2+s' := by linarith only [hhalf',hs'.1]
    simpa only [pow_two] using mul_le_mul h1 h2 (by positivity : (0 : ℝ)≤n/2) (add_nonneg (sq_nonneg r) hs.1)
  have hcabs : |c|≤L := by
    have hsprod : s*s'≤L^2 := by
      simpa only [pow_two] using mul_le_mul hs.2 hs'.2 hs'.1 hL
    nlinarith only [hc,hsprod,sq_abs c,abs_nonneg c,hL]
  have hfactor : C=r*r'*(Real.sqrt (1+a)*Real.sqrt (1+b)) := by
    dsimp [C,a,b]
    rw [Real.sqrt_mul (add_nonneg (sq_nonneg r) hs.1),sqrt_radius_factor hrpos hs.1,sqrt_radius_factor hr'pos hs'.1]
    ring
  have hratio : r*r'/C=(1/Real.sqrt (1+a))*(1/Real.sqrt (1+b)) := by
    rw [hfactor]
    have hrne := ne_of_gt hrpos
    have hr'ne := ne_of_gt hr'pos
    have han : Real.sqrt (1+a)≠0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hbn : Real.sqrt (1+b)≠0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
  have hunitA := inverse_sqrt_unit_bounds ha0
  have hunitB := inverse_sqrt_unit_bounds hb0
  have hprod := inverse_sqrt_product_second_order ha0 hb0
  have hratio1 : r*r'/C≤1 := by
    rw [hratio]
    exact (mul_le_mul hunitA.2.1 hunitB.2.1 hunitB.1 zero_le_one).trans_eq (by ring)
  have hratioGap : |r*r'/C-1|≤2*L/n := by
    rw [abs_of_nonpos (sub_nonpos.mpr hratio1),hratio]
    nlinarith only [hprod.1,ha,hb]
  have hcRatio : |c/C|≤2*L/n := by
    rw [abs_div,abs_of_pos hC]
    calc
      _ ≤ L/C := div_le_div_of_nonneg_right hcabs hC.le
      _ ≤ L/(n/2) := div_le_div_of_nonneg_left hL (by positivity) hhalfC
      _ = _ := by ring
  refine ⟨hC,normalizedGram_abs_le_one hrpos hr'pos hs.1 hs'.1 hR hc,?_,hcabs⟩
  have hid : (r*r'*R+c)/C-R=(r*r'/C-1)*R+c/C := by ring
  rw [hid]
  calc
    _ ≤ |(r*r'/C-1)*R|+|c/C| := abs_add_le _ _
    _ = |r*r'/C-1| *|R|+|c/C| := by rw [abs_mul]
    _ ≤ 2*L/n+2*L/n := add_le_add
      ((mul_le_of_le_one_right (abs_nonneg _) hR).trans hratioGap) hcRatio
    _ = _ := by ring

theorem bulk_shrink_bounds {n m L R : ℝ} (hn : 0<n) (hm : 0≤m) (hmL : m≤L) (hR : |R|≤1) :
    |n/(n+m)*R|≤1 ∧ |n/(n+m)*R-R|≤L/n := by
  have hL := hm.trans hmL
  have hD : 0<n+m := by positivity
  have hrho0 : 0≤n/(n+m) := by positivity
  have hrho1 : n/(n+m)≤1 := (div_le_one hD).2 (by linarith only [hm])
  have hratio : m/(n+m)≤L/n := by
    apply (div_le_div_iff₀ hD hn).2
    nlinarith only [mul_le_mul_of_nonneg_right hmL hn.le,mul_nonneg hL hm]
  constructor
  · rw [abs_mul,abs_of_nonneg hrho0]
    exact (mul_le_of_le_one_right hrho0 hR).trans hrho1
  · have hid : n/(n+m)*R-R=-(m/(n+m))*R := by field_simp; ring
    rw [hid,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤m/(n+m))]
    exact (mul_le_of_le_one_right (by positivity) hR).trans hratio

theorem first_order_reference_error {n m L e r r' s s' R c : ℝ}
    (hn : 0<n) (hm : 0≤m) (hmL : m≤L) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*L≤n) (hr : 0≤r) (hr' : 0≤r')
    (hs : s∈Icc m L) (hs' : s'∈Icc m L)
    (hbox : r^2/n∈Icc (1-e) (1+e)) (hbox' : r'^2/n∈Icc (1-e) (1+e))
    (hR : |R|≤1) (hc : |c|≤L) :
    |(n+m)*((r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s'))-n/(n+m)*R)-c|≤
      L-m+4*L*e+14*L^2/n := by
  let C := Real.sqrt ((r^2+s)*(r'^2+s'))
  have hL := hm.trans hmL
  have H := retained_radius_bounds hn hm hmL he0 he1 hscale hr hr' hs hs' hbox hbox'
  have hmid : |m-(s+s')/2|≤L-m := by
    rw [abs_of_nonpos (by linarith only [hs.1,hs'.1] : m-(s+s')/2≤0)]
    linarith only [hs.2,hs'.2]
  have hfirst : |(n+m)*r*r'/C-n|≤L-m+(2*L*e+10*L^2/n) := by
    have htri := abs_sub_le ((n+m)*r*r'/C-n) (m-(s+s')/2) 0
    simp only [sub_zero] at htri
    linarith only [htri,H.1,hmid]
  have hD : n+m≠0 := by positivity
  have hid : (n+m)*((r*r'*R+c)/C-n/(n+m)*R)-c=
      ((n+m)*r*r'/C-n)*R+((n+m)/C-1)*c := by field_simp; ring
  rw [hid]
  calc
    _ ≤ |((n+m)*r*r'/C-n)*R|+|((n+m)/C-1)*c| := abs_add_le _ _
    _ = |(n+m)*r*r'/C-n| *|R|+|(n+m)/C-1| *|c| := by rw [abs_mul,abs_mul]
    _ ≤ (L-m+(2*L*e+10*L^2/n))+(2*e+4*L/n)*L :=
      add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hR).trans hfirst)
        (mul_le_mul H.2 hc (abs_nonneg _) (by positivity))
    _ = _ := by ring


end
end TensorPCA.NonRSLowerProofs.FiniteCavityNormalizedGramBounds
