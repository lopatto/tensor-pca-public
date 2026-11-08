-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepSliceSignedTaylor
public import TensorPCA.NonRSLowerProofs.FiniteCavityNormalizedGramBounds

/-! Signed slice-polynomial covariance error for the finite spherical cavity reference.
No parity, convexity, random-law or ASS premise is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceCovarianceBounds
open Set OneStepSliceSignedTaylor OneStepSliceSignedDerivative
open FiniteCavityNormalizedGramBounds
noncomputable section

theorem xiSlice_reference_covariance_error (k : ℕ) (hk : 3≤k)
    {mu n m L e r r' s s' R c : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (hn : 0<n) (hm : 0≤m) (hmL : m≤L) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*L≤n) (hr : 0≤r) (hr' : 0≤r')
    (hs : s∈Icc m L) (hs' : s'∈Icc m L)
    (hbox : r^2/n∈Icc (1-e) (1+e)) (hbox' : r'^2/n∈Icc (1-e) (1+e))
    (hR : |R|≤1) (hc : c^2≤s*s') :
    |(n+m)*Scalar.xiSlice k mu ((r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s')))-
      (n+m)*Scalar.xiSlice k mu (n/(n+m)*R)-c*deriv (Scalar.xiSlice k mu) R|≤
      (L-m+4*L*e+14*L^2/n)*deriv (Scalar.xiSlice k mu) 1+
        64*L^2*deriv (deriv (Scalar.xiSlice k mu)) 1/n := by
  let f := Scalar.xiSlice k mu
  let D := n+m
  let T := (r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s'))
  let Y := n/(n+m)*R
  let K := deriv (deriv f) 1
  let E := L-m+4*L*e+14*L^2/n
  have hL : 0≤L := hm.trans hmL
  have hD : 0≤D := by dsimp [D]; positivity
  have hDupper : D≤2*n := by dsimp [D]; linarith only [hmL,hscale,hn]
  have hK : 0≤K := secondDeriv_one_nonneg k hk hmu
  have hgram := normalizedGram_shell_bounds hn hL he0 he1 hr hr'
    ⟨hm.trans hs.1,hs.2⟩ ⟨hm.trans hs'.1,hs'.2⟩ hbox hbox' hR hc
  have hbulk := bulk_shrink_bounds hn hm hmL hR
  have hT : T∈Icc (-1 : ℝ) 1 := abs_le.mp hgram.2.1
  have hY : Y∈Icc (-1 : ℝ) 1 := abs_le.mp hbulk.1
  have hRunit : R∈Icc (-1 : ℝ) 1 := abs_le.mp hR
  have hTgap : |T-R|≤4*L/n := hgram.2.2.1
  have hYgap : |Y-R|≤L/n := hbulk.2
  have hfirst : |D*(T-Y)-c|≤E :=
    first_order_reference_error hn hm hmL he0 he1 hscale hr hr' hs hs' hbox hbox' hR hgram.2.2.2
  have hfp : |deriv f R|≤deriv f 1 :=
    abs_deriv_le k hmu (show (1 : ℝ)∈Icc 0 1 by constructor <;> norm_num) hRunit
  have hfp0 : 0≤deriv f 1 := (abs_nonneg _).trans hfp
  have hT2 : (T-R)^2≤(4*L/n)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hTgap 2
  have hY2 : (Y-R)^2≤(L/n)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hYgap 2
  have hTaylorT : |f T-f R-deriv f R*(T-R)|≤K*(4*L/n)^2 :=
    (xiSlice_taylor_abs_le k hk hmu hT hRunit).trans (mul_le_mul_of_nonneg_left hT2 hK)
  have hTaylorY : |f Y-f R-deriv f R*(Y-R)|≤K*(L/n)^2 :=
    (xiSlice_taylor_abs_le k hk hmu hY hRunit).trans (mul_le_mul_of_nonneg_left hY2 hK)
  have hrem : D*(|f T-f R-deriv f R*(T-R)|+|f Y-f R-deriv f R*(Y-R)|)≤64*L^2*K/n := by
    calc
      _ ≤ D*(K*(4*L/n)^2+K*(L/n)^2) := mul_le_mul_of_nonneg_left (add_le_add hTaylorT hTaylorY) hD
      _ = D*(K*((4*L/n)^2+(L/n)^2)) := by ring
      _ ≤ (2*n)*(K*((4*L/n)^2+(L/n)^2)) :=
        mul_le_mul_of_nonneg_right hDupper (mul_nonneg hK (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ = 34*L^2*K/n := by field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hn.le
        nlinarith only [mul_nonneg (sq_nonneg L) hK]
  have hid : D*f T-D*f Y-c*deriv f R=
      D*((f T-f R-deriv f R*(T-R))-(f Y-f R-deriv f R*(Y-R)))+
        deriv f R*(D*(T-Y)-c) := by ring
  change |D*f T-D*f Y-c*deriv f R|≤E*deriv f 1+64*L^2*K/n
  rw [hid]
  calc
    _ ≤ |D*((f T-f R-deriv f R*(T-R))-(f Y-f R-deriv f R*(Y-R)))|+
        |deriv f R*(D*(T-Y)-c)| := abs_add_le _ _
    _ ≤ D*(|f T-f R-deriv f R*(T-R)|+|f Y-f R-deriv f R*(Y-R)|)+
        |deriv f R| *|D*(T-Y)-c| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hD]
      exact add_le_add (mul_le_mul_of_nonneg_left (by
        simpa only [sub_zero,zero_sub,abs_neg] using
          abs_sub_le (f T-f R-deriv f R*(T-R)) 0 (f Y-f R-deriv f R*(Y-R))) hD) le_rfl
    _ ≤ 64*L^2*K/n+deriv f 1*E := add_le_add hrem (mul_le_mul hfp hfirst (abs_nonneg _) hfp0)
    _ = _ := by ring

theorem thermal_xiSlice_reference_covariance_error (k : ℕ) (hk : 3≤k)
    {mu n m L e r r' s s' R c : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (hn : 0<n) (hm : 0≤m) (hmL : m≤L) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*L≤n) (hr : 0≤r) (hr' : 0≤r')
    (hs : s∈Icc m L) (hs' : s'∈Icc m L)
    (hbox : r^2/n∈Icc (1-e) (1+e)) (hbox' : r'^2/n∈Icc (1-e) (1+e))
    (hR : |R|≤1) (hc : c^2≤s*s') (beta : ℝ) :
    |(n+m)*beta^2*Scalar.xiSlice k mu ((r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s')))-
      (n+m)*beta^2*Scalar.xiSlice k mu (n/(n+m)*R)-beta^2*c*deriv (Scalar.xiSlice k mu) R|≤
      (L-m+4*L*e+14*L^2/n)*beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/n := by
  have H := mul_le_mul_of_nonneg_left
    (xiSlice_reference_covariance_error k hk hmu hn hm hmL he0 he1 hscale hr hr' hs hs' hbox hbox' hR hc)
    (sq_nonneg beta)
  rw [← abs_of_nonneg (sq_nonneg beta),← abs_mul] at H
  simp only [abs_of_nonneg (sq_nonneg beta)] at H
  convert H using 1 <;> ring

theorem thermal_xiSlice_reference_covariance_error_delta (k : ℕ) (hk : 3≤k)
    {mu n m delta e r r' s s' R c : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (hn : 0<n) (hm : 0≤m) (hdelta : 0≤delta) (he0 : 0≤e) (he1 : e≤1/2)
    (hscale : 2*(m*(1+delta))≤n) (hr : 0≤r) (hr' : 0≤r')
    (hs : s∈Icc m (m*(1+delta))) (hs' : s'∈Icc m (m*(1+delta)))
    (hbox : r^2/n∈Icc (1-e) (1+e)) (hbox' : r'^2/n∈Icc (1-e) (1+e))
    (hR : |R|≤1) (hc : c^2≤s*s') (beta : ℝ) :
    let L := m*(1+delta)
    |(n+m)*beta^2*Scalar.xiSlice k mu ((r*r'*R+c)/Real.sqrt ((r^2+s)*(r'^2+s')))-
      (n+m)*beta^2*Scalar.xiSlice k mu (n/(n+m)*R)-beta^2*c*deriv (Scalar.xiSlice k mu) R|≤
      (m*delta+4*L*e+14*L^2/n)*beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/n := by
  dsimp only
  have hmL : m≤m*(1+delta) := by nlinarith only [mul_nonneg hm hdelta]
  have H := thermal_xiSlice_reference_covariance_error k hk hmu hn hm hmL he0 he1 hscale hr hr'
    hs hs' hbox hbox' hR hc beta
  convert H using 1 <;> ring


end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceCovarianceBounds
