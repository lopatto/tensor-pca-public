-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticForwardSpine
public import TensorPCA.NonRSLowerProofs.OneStepGaussianShellMomentsProbability

/-! Uniform Gaussian state cutoffs and terminal shell probabilities. No conditional
logarithmic or good-root conclusion is asserted here.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSpineCutoffs
open MeasureTheory ProbabilityTheory
open FiniteGaussianAffineKernel FiniteGaussianQuadraticSpine
open FiniteGaussianQuadraticForwardSpine FiniteCSGaussianDepthPrecision
open OneStepGaussianShellMoments
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem isotropic_norm_sq_cutoff {M : ℕ} (hM : 0< M) {V Bmax C : ℝ}
    (hV : 0≤ V) (hVB : V≤Bmax^2) (hC : Bmax^2< C^2) :
    ((stdGaussian (Model.Vector M)).map (fun g => Real.sqrt V •g)).real
      {h | C^2*(M : ℝ)< ‖h‖^2}≤
      4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2) := by
  have hMr : 0< (M : ℝ) := by exact_mod_cast hM
  have hGap : 0< C^2-Bmax^2 := sub_pos.mpr hC
  let t := (C^2-Bmax^2)*(M : ℝ)
  have ht : 0< t := mul_pos hGap hMr
  have hsub : {g : Model.Vector M | C^2*(M : ℝ)< ‖Real.sqrt V •g‖^2}⊆
      {g | t≤|‖(0 : Model.Vector M)+Real.sqrt V •g‖^2-
        (‖(0 : Model.Vector M)‖^2+(Real.sqrt V)^2*(M : ℝ))|} := by
    intro g hg
    change C^2*(M : ℝ)< ‖Real.sqrt V •g‖^2 at hg
    have hAbs := le_abs_self (‖Real.sqrt V •g‖^2-V*(M : ℝ))
    simp only [zero_add,norm_zero,show (0 : ℝ)^2=0 by norm_num,Real.sq_sqrt hV]
    dsimp only [t]
    have hProd := mul_le_mul_of_nonneg_right hVB hMr.le
    change (C^2-Bmax^2)*(M : ℝ)≤|‖Real.sqrt V •g‖^2-V*(M : ℝ)|
    rw [sub_mul]
    linarith only [hg,hProd,hAbs]
  have HP := (measureReal_mono hsub).trans
    (shifted_norm_sq_centered_tail (0 : Model.Vector M) (Real.sqrt V) ht)
  have hfour : (Real.sqrt V)^4=V^2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt hV]
  rw [map_measureReal_apply (by fun_prop) (measurableSet_lt measurable_const (by fun_prop))]
  apply HP.trans
  simp only [norm_zero,show (0 : ℝ)^2=0 by norm_num,mul_zero,zero_add,hfour]
  calc
    4*V^2*(M : ℝ)/t^2≤4*Bmax^4*(M : ℝ)/t^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg t)
      have HV : V^2≤Bmax^4 := by nlinarith only [hVB,hV,sq_nonneg (Bmax^2-V)]
      nlinarith only [HV,hMr]
    _=4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2) := by
      dsimp only [t]
      field_simp
      <;> ring

theorem prefix_state_cutoff_bound {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B y0 Bmax C : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (hMax : B≤Bmax) (hC : Bmax^2< C^2) {i : ℕ} (hi : i≤d) :
    (prefixStateKernel M hx hDelta hB y0 i 0).real
      {h | C^2*(M : ℝ)< ‖h‖^2}≤
      4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2) := by
  have hBp := precision_B_pos hx hDelta hB
  have hV : 0≤stateVariance x Delta B y0 i := mul_nonneg (sq_nonneg _)
    (FiniteGaussianQuadraticUniformBounds.prefixVariance_mem_Icc hx hDelta hB hy hroot i).1
  have hVB : stateVariance x Delta B y0 i≤Bmax^2 := by
    apply (prefixStateKernel_norm_scale_bound hx hDelta hB hy hroot i).trans
    nlinarith only [hBp,hMax]
  rw [prefixStateKernel_eq_affine M hx hDelta hB hy hroot hi,affineKernel_apply]
  simpa only [zero_smul,zero_add] using isotropic_norm_sq_cutoff hM hV hVB hC

theorem terminal_spin_shell_bad_mass {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B y0 eps : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (heps : 0< eps) :
    (quenchedSpinLaw M hx hDelta hB y0).real
      {sigma | eps*(M : ℝ)< |‖sigma‖^2-(M : ℝ)|}≤4/((M : ℝ)*eps^2) := by
  have hMr : 0< (M : ℝ) := by exact_mod_cast hM
  have HT := shifted_norm_sq_centered_tail (0 : Model.Vector M) (1 : ℝ) (mul_pos heps hMr)
  rw [quenchedSpinLaw_eq_stdGaussian M hx hDelta hB hy hroot]
  have hsub : {sigma : Model.Vector M | eps*(M : ℝ)< |‖sigma‖^2-(M : ℝ)|}⊆
      {sigma | eps*(M : ℝ)≤|‖(0 : Model.Vector M)+(1 : ℝ) •sigma‖^2-
        (‖(0 : Model.Vector M)‖^2+(1 : ℝ)^2*(M : ℝ))|} := by
    simpa only [one_smul,zero_add,norm_zero,show (0 : ℝ)^2=0 by norm_num,one_pow,one_mul] using
      (show {sigma : Model.Vector M | eps*(M : ℝ)< |‖sigma‖^2-(M : ℝ)|}⊆
        {sigma | eps*(M : ℝ)≤|‖sigma‖^2-(M : ℝ)|} from
          fun _ h => (show eps*(M : ℝ)< _ from h).le)
  apply (measureReal_mono hsub).trans (HT.trans _)
  simp only [norm_zero,zero_pow,mul_zero,zero_add,one_pow,mul_one]
  field_simp
  <;> nlinarith

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticSpineCutoffs
