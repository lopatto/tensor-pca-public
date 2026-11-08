-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedMass

/-! Fixed cavity dimension first, then a small fixed retained radius box, then the bulk
dimension limit. The logarithmic radius mass is paid.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceErrorAsymptotics
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCavityRetainedMass
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_radiusBox_eventually_cost_control (M : ℕ) (delta A B : ℝ)
    {eps : ℝ} (heps : 0<eps) :
    ∃e : ℝ,e∈Ioc (0 : ℝ) (1/2) ∧ ∀ᶠ N : ℕ in atTop,
      0<N ∧ 2*((M : ℝ)*(1+delta))≤(N : ℝ) ∧
      (((M : ℝ)*delta+4*((M : ℝ)*(1+delta))*e+14*((M : ℝ)*(1+delta))^2/(N : ℝ))*A+
        64*((M : ℝ)*(1+delta))^2*B/(N : ℝ))-Real.log (radiusBoxMass N e)≤(M : ℝ)*delta*A+eps := by
  let L := (M : ℝ)*(1+delta)
  let e := min (1/2 : ℝ) (eps/(16*(|L*A|+1)))
  have hden : 0<16*(|L*A|+1) := by positivity
  have he : 0<e := lt_min (by norm_num) (div_pos heps hden)
  have he1 : e≤1/2 := min_le_left _ _
  have hemul : e*(16*(|L*A|+1))≤eps :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : 4*L*e*A≤eps/2 := by
    have H := mul_le_mul_of_nonneg_right (le_abs_self (L*A)) he.le
    nlinarith only [hemul,H,he.le,heps]
  let C := 14*L^2*A+64*L^2*B
  have hInv : Tendsto (fun N : ℕ => C/(N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hRest : Tendsto (fun N : ℕ => C/(N : ℝ)-Real.log (radiusBoxMass N e)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_zero] using hInv.sub (log_radiusBoxMass_tendsto_zero he)
  have hScale : ∀ᶠ N : ℕ in atTop,2*L≤(N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2*L))
  refine ⟨e,⟨he,he1⟩,?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ),hScale,
    hRest.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<eps/2))] with N hN hscale hrest
  refine ⟨hN,hscale,?_⟩
  have hid : (((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*A+64*L^2*B/(N : ℝ))-
      Real.log (radiusBoxMass N e)=
      (M : ℝ)*delta*A+4*L*e*A+(C/(N : ℝ)-Real.log (radiusBoxMass N e)) := by
    dsimp only [C]
    ring
  change (((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*A+64*L^2*B/(N : ℝ))-
    Real.log (radiusBoxMass N e)≤_
  rw [hid]
  linarith only [hsmall,hrest]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceErrorAsymptotics
