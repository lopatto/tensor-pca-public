-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit scalar constants for comparing the lower and upper window estimates. This
does not assert any invariance or duplication law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGWindowContradictionConstants
open Set
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem exists_window_separation_constants {p gap : ℝ} (hp : p∈Ioc (0 : ℝ) 1) (hGap : 0<gap) :
    ∃kappa eps t c : ℝ,0<kappa ∧ kappa≤(3/4 : ℝ) ∧ 0<eps ∧ 0≤t ∧ 0<c ∧
      ∀D W0 W1 : ℝ,0≤D→
        p/3-kappa-Real.sqrt D-4*eps/3≤W0→
        W1≤7*Real.exp (-t*gap)+Real.exp t*Real.sqrt D→
        |W0-W1|≤eps→c≤D := by
  let kappa := p/24
  let eps := p/32
  let t := Real.log (168/p)/gap
  let c := (p/(6*(1+Real.exp t)))^2
  have hp0 : 0<p := hp.1
  have hK : 0<kappa := by dsimp [kappa]; positivity
  have hKupper : kappa≤(3/4 : ℝ) := by dsimp [kappa]; linarith only [hp.2]
  have hEps : 0<eps := by dsimp [eps]; positivity
  have hArg : 0<(168 : ℝ)/p := div_pos (by norm_num) hp.1
  have hArgOne : 1≤(168 : ℝ)/p := (le_div_iff₀ hp.1).mpr (by linarith only [hp.2])
  have ht : 0≤t := div_nonneg (Real.log_nonneg hArgOne) hGap.le
  have htMul : t*gap=Real.log (168/p) := by
    dsimp only [t]
    exact div_mul_cancel₀ _ hGap.ne'
  have hExp : 7*Real.exp (-t*gap)=p/24 := by
    rw [neg_mul,htMul,Real.exp_neg,Real.exp_log hArg,inv_div]
    ring
  have hDen : 0<6*(1+Real.exp t) := by positivity
  have hRatio : 0<p/(6*(1+Real.exp t)) := div_pos hp.1 hDen
  have hc : 0<c := pow_pos hRatio 2
  refine ⟨kappa,eps,t,c,hK,hKupper,hEps,ht,hc,?_⟩
  intro D W0 W1 hD hLower hUpper hInvariant
  have hAbs := (abs_le.mp hInvariant).2
  have H : p/3-kappa-Real.sqrt D-4*eps/3≤7*Real.exp (-t*gap)+Real.exp t*Real.sqrt D+eps := by
    linarith only [hLower,hUpper,hAbs]
  rw [hExp] at H
  dsimp only [kappa,eps] at H
  have hNum : p/6≤(1+Real.exp t)*Real.sqrt D := by nlinarith only [H,hp.1]
  have hQuotient : p/(6*(1+Real.exp t))≤Real.sqrt D := by
    apply (div_le_iff₀ hDen).mpr
    nlinarith only [hNum]
  have hSq := pow_le_pow_left₀ hRatio.le hQuotient 2
  rw [Real.sq_sqrt hD] at hSq
  exact hSq

end
end TensorPCA.NonRSLowerProofs.FiniteGGWindowContradictionConstants
