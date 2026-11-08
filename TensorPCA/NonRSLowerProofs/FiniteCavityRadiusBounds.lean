-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensator

/-! Finite scalar bounds for the Gaussian-radius cavity reference. The radius signs are
explicit. These estimates do not assert a cavity law or a free-energy comparison.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityRadiusBounds
open Set
noncomputable section

theorem inverse_sqrt_second_order {u : ℝ} (hu : 0≤u) :
    0≤1/Real.sqrt (1+u)-1+u/2 ∧
    1/Real.sqrt (1+u)-1+u/2≤3*u^2/8 := by
  let v := Real.sqrt (1+u)
  have hv : 1≤v := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ)≤1+u by linarith)
  have hvpos : 0<v := lt_of_lt_of_le zero_lt_one hv
  have hvne : v≠0 := ne_of_gt hvpos
  have hs : v^2=1+u := Real.sq_sqrt (by linarith : 0≤1+u)
  have hu_eq : u=v^2-1 := by linarith
  have he : 1/v-1+u/2=(v-1)^2*(v+2)/(2*v) := by
    rw [hu_eq]
    field_simp
    ring
  change 0≤1/v-1+u/2 ∧ 1/v-1+u/2≤3*u^2/8
  rw [he]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0<2*v)).2
    rw [hu_eq]
    have hp : 0≤(v-1)^3*(3*v^2+9*v+8) := by
      exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hv) 3) (by positivity)
    nlinarith only [hp]

theorem inverse_sqrt_unit_bounds {u : ℝ} (hu : 0≤u) :
    0≤1/Real.sqrt (1+u) ∧ 1/Real.sqrt (1+u)≤1 ∧
    0≤1-1/Real.sqrt (1+u) ∧ 1-1/Real.sqrt (1+u)≤u/2 := by
  have hv : 1≤Real.sqrt (1+u) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ)≤1+u by linarith)
  have hle : 1/Real.sqrt (1+u)≤1 := (div_le_one (by positivity)).2 hv
  have he := (inverse_sqrt_second_order hu).1
  exact ⟨by positivity,hle,sub_nonneg.mpr hle,by linarith⟩

theorem inverse_sqrt_product_second_order {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    0≤(1/Real.sqrt (1+u))*(1/Real.sqrt (1+v))-1+(u+v)/2 ∧
    (1/Real.sqrt (1+u))*(1/Real.sqrt (1+v))-1+(u+v)/2≤(u^2+v^2)/2 := by
  let a := 1/Real.sqrt (1+u)
  let b := 1/Real.sqrt (1+v)
  have ha := inverse_sqrt_unit_bounds hu
  have hb := inverse_sqrt_unit_bounds hv
  have hea := inverse_sqrt_second_order hu
  have heb := inverse_sqrt_second_order hv
  have hid : a*b-1+(u+v)/2=(a-1+u/2)*b+(b-1+v/2)+(u/2)*(1-b) := by ring
  change 0≤a*b-1+(u+v)/2 ∧ a*b-1+(u+v)/2≤(u^2+v^2)/2
  rw [hid]
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg hea.1 hb.1) heb.1)
      (mul_nonneg (by positivity) hb.2.2.1)
  · have heamul : (a-1+u/2)*b≤a-1+u/2 :=
      mul_le_of_le_one_right hea.1 hb.2.1
    have hlast : (u/2)*(1-b)≤(u/2)*(v/2) :=
      mul_le_mul_of_nonneg_left hb.2.2.2 (by positivity)
    nlinarith [sq_nonneg (u-v)]

private theorem radius_ratio_control {n m L e r s : ℝ}
    (hn : 0<n) (hm : 0≤m) (hL : 0≤L) (he0 : 0≤e) (he1 : e≤1/2)
    (hr : 0≤r) (hs : s∈Icc (0 : ℝ) L)
    (hbox : r^2/n∈Icc (1-e) (1+e)) :
    0<r ∧ n/2≤r^2 ∧ 0≤s/r^2 ∧ s/r^2≤2*L/n ∧
    |s-(n+m)*(s/r^2)|≤2*L*e+2*L*m/n := by
  have hlo := (le_div_iff₀ hn).mp hbox.1
  have hhi := (div_le_iff₀ hn).mp hbox.2
  have hhalf : n/2≤r^2 := by nlinarith
  have hsq : 0<r^2 := lt_of_lt_of_le (by positivity) hhalf
  have hrpos : 0<r := by nlinarith
  have ha0 : 0≤s/r^2 := div_nonneg hs.1 (sq_nonneg r)
  have ha1 : s/r^2≤2*L/n := by
    apply (div_le_div_iff₀ hsq hn).2
    nlinarith [mul_le_mul_of_nonneg_left hs.2 hn.le,
      mul_le_mul_of_nonneg_left hhalf hL]
  have herr : |r^2-n|≤n*e := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have herrm : |r^2-n-m|≤n*e+m := by
    have htri := abs_sub_le (r^2-n) 0 m
    have htri' : |r^2-n-m|≤|r^2-n|+m := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hm] using htri
    exact htri'.trans (by linarith only [herr])
  have hid : s-(n+m)*(s/r^2)=(s/r^2)*(r^2-n-m) := by
    field_simp
    ring
  refine ⟨hrpos,hhalf,ha0,ha1,?_⟩
  rw [hid,abs_mul,abs_of_nonneg ha0]
  calc
    _ ≤ (s/r^2)*(n*e+m) := mul_le_mul_of_nonneg_left herrm ha0
    _ ≤ (2*L/n)*(n*e+m) := mul_le_mul_of_nonneg_right ha1 (by positivity)
    _ = _ := by field_simp

private theorem sqrt_radius_factor {r s : ℝ} (hr : 0<r) (hs : 0≤s) :
    Real.sqrt (r^2+s)=r*Real.sqrt (1+s/r^2) := by
  have hrne : r≠0 := ne_of_gt hr
  have hid : r^2+s=r^2*(1+s/r^2) := by field_simp
  rw [hid,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]

theorem retained_radius_bounds {n m L e r r' s s' : ℝ}
    (hn : 0<n) (hm : 0≤m) (hmL : m≤L) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*L≤n) (hr : 0≤r) (hr' : 0≤r')
    (hs : s∈Icc m L) (hs' : s'∈Icc m L)
    (hbox : r^2/n∈Icc (1-e) (1+e)) (hbox' : r'^2/n∈Icc (1-e) (1+e)) :
    |(n+m)*r*r'/Real.sqrt ((r^2+s)*(r'^2+s'))-n-(m-(s+s')/2)|≤
        2*L*e+10*L^2/n ∧
    |(n+m)/Real.sqrt ((r^2+s)*(r'^2+s'))-1|≤2*e+4*L/n := by
  have hL : 0≤L := hm.trans hmL
  have hs0 := hm.trans hs.1
  have hs'0 := hm.trans hs'.1
  have H := radius_ratio_control hn hm hL he0 he1 hr ⟨hs0,hs.2⟩ hbox
  have H' := radius_ratio_control hn hm hL he0 he1 hr' ⟨hs'0,hs'.2⟩ hbox'
  let a := s/r^2
  let b := s'/r'^2
  let D := n+m
  let C := Real.sqrt ((r^2+s)*(r'^2+s'))
  have hD : 0≤D := by dsimp [D]; positivity
  have hDupper : D≤2*n := by dsimp [D]; linarith only [hmL,hscale,hn]
  have hfactor : C=r*r'*(Real.sqrt (1+a)*Real.sqrt (1+b)) := by
    dsimp [C,a,b]
    rw [Real.sqrt_mul (by positivity),sqrt_radius_factor H.1 hs0,sqrt_radius_factor H'.1 hs'0]
    ring
  have hsqrta : 0<Real.sqrt (1+a) := Real.sqrt_pos.2 (by dsimp [a]; positivity)
  have hsqrtb : 0<Real.sqrt (1+b) := Real.sqrt_pos.2 (by dsimp [b]; positivity)
  have hC : 0<C := by
    rw [hfactor]
    exact mul_pos (mul_pos H.1 H'.1) (mul_pos hsqrta hsqrtb)
  have hA : D*r*r'/C=D*((1/Real.sqrt (1+a))*(1/Real.sqrt (1+b))) := by
    rw [hfactor]
    have hrne := ne_of_gt H.1
    have hr'ne := ne_of_gt H'.1
    have hane := ne_of_gt hsqrta
    have hbne := ne_of_gt hsqrtb
    field_simp
  have hrem := inverse_sqrt_product_second_order H.2.2.1 H'.2.2.1
  have ha2 : a^2≤(2*L/n)^2 := pow_le_pow_left₀ H.2.2.1 H.2.2.2.1 2
  have hb2 : b^2≤(2*L/n)^2 := pow_le_pow_left₀ H'.2.2.1 H'.2.2.2.1 2
  have hremupper : (1/Real.sqrt (1+a))*(1/Real.sqrt (1+b))-1+(a+b)/2≤(2*L/n)^2 := by
    nlinarith only [hrem.2,ha2,hb2]
  have hangular : |D*((1/Real.sqrt (1+a))*(1/Real.sqrt (1+b))-1+(a+b)/2)|≤8*L^2/n := by
    rw [abs_of_nonneg (mul_nonneg hD hrem.1)]
    calc
      _ ≤ D*(2*L/n)^2 := mul_le_mul_of_nonneg_left hremupper hD
      _ ≤ (2*n)*(2*L/n)^2 := mul_le_mul_of_nonneg_right hDupper (sq_nonneg _)
      _ = _ := by field_simp; ring
  have hhalf : |((s-D*a)+(s'-D*b))/2|≤2*L*e+2*L*m/n := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have htri := abs_add_le (s-D*a) (s'-D*b)
    linarith only [htri,H.2.2.2.2,H'.2.2.2.2]
  constructor
  · change |D*r*r'/C-n-(m-(s+s')/2)|≤2*L*e+10*L^2/n
    rw [hA]
    have hid : D*((1/Real.sqrt (1+a))*(1/Real.sqrt (1+b)))-n-(m-(s+s')/2)=
        D*((1/Real.sqrt (1+a))*(1/Real.sqrt (1+b))-1+(a+b)/2)+((s-D*a)+(s'-D*b))/2 := by
      dsimp [D]
      ring
    rw [hid]
    have htri := abs_add_le (D*((1/Real.sqrt (1+a))*(1/Real.sqrt (1+b))-1+(a+b)/2))
      (((s-D*a)+(s'-D*b))/2)
    have hML : 2*L*m/n≤2*L^2/n := by
      apply div_le_div_of_nonneg_right _ hn.le
      nlinarith only [mul_nonneg hL (sub_nonneg.mpr hmL)]
    calc
      _ ≤ 8*L^2/n+(2*L*e+2*L*m/n) := htri.trans (add_le_add hangular hhalf)
      _ ≤ 8*L^2/n+(2*L*e+2*L^2/n) := by linarith only [hML]
      _ = _ := by ring
  · change |D/C-1|≤2*e+4*L/n
    have hrlo := (le_div_iff₀ hn).mp hbox.1
    have hrhi := (div_le_iff₀ hn).mp hbox.2
    have hr'lo := (le_div_iff₀ hn).mp hbox'.1
    have hr'hi := (div_le_iff₀ hn).mp hbox'.2
    have hne : n*e≤n/2 := by
      convert mul_le_mul_of_nonneg_left he1 hn.le using 1 <;> ring
    have hlow0 : 0≤n*(1-e)+m := by nlinarith only [hne,hn,hm]
    have hhigh0 : 0≤n*(1+e)+L := by positivity
    have hlow : n*(1-e)+m≤C := by
      apply Real.le_sqrt_of_sq_le
      have hl1 : n*(1-e)+m≤r^2+s := by nlinarith only [hrlo,hs.1]
      have hl2 : n*(1-e)+m≤r'^2+s' := by nlinarith only [hr'lo,hs'.1]
      simpa only [pow_two] using mul_le_mul hl1 hl2 hlow0 (by positivity : 0≤r^2+s)
    have hhigh : C≤n*(1+e)+L := by
      apply (Real.sqrt_le_left hhigh0).2
      have hh1 : r^2+s≤n*(1+e)+L := by nlinarith only [hrhi,hs.2]
      have hh2 : r'^2+s'≤n*(1+e)+L := by nlinarith only [hr'hi,hs'.2]
      simpa only [pow_two] using mul_le_mul hh1 hh2 (by positivity : 0≤r'^2+s') hhigh0
    have hhalfC : n/2≤C := by nlinarith only [hlow,hne,hm]
    let E := 2*e+4*L/n
    have hE : 0≤E := by dsimp [E]; positivity
    have hEC : n*e+2*L≤E*C := by
      calc
        _ = E*(n/2) := by dsimp [E]; field_simp; ring
        _ ≤ E*C := mul_le_mul_of_nonneg_left hhalfC hE
    apply abs_le.mpr
    constructor
    · have hnum : (1-E)*C≤D := by dsimp [D]; nlinarith only [hhigh,hEC,hL,hm]
      have hdiv := (le_div_iff₀ hC).2 hnum
      dsimp [E] at hdiv
      linarith only [hdiv]
    · have hnum : D≤(1+E)*C := by dsimp [D]; nlinarith only [hlow,hEC,hL]
      have hdiv := (div_le_iff₀ hC).2 hnum
      dsimp [E] at hdiv
      linarith only [hdiv]


end
end TensorPCA.NonRSLowerProofs.FiniteCavityRadiusBounds
