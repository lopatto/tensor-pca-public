-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityActualAnalyticLower
public import TensorPCA.NonRSLowerProofs.FiniteCavityActualMarkedMoments
public import TensorPCA.NonRSLowerProofs.FiniteCavityPressureLowerReduction

/-! A finite-temperature lower bound for the spherical slice. The GG/tree construction
bounds every finite marked-moment error. Cavity size is chosen first, then one fixed
perturbation cutoff and amplitude cube, before the bulk dimension tends to infinity.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPhysicalLower
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteCS FiniteCavityActualAnalyticLower FiniteCavityActualMarkedMoments
open FiniteCavityObservedFunctionalAveraging FiniteCavityPerturbedASSLower
open FiniteCavityPressureLowerReduction PhysicalPressureGroundReduction FiniteGGPositiveGrid
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem eventually_cube_cavity_lower (k : ℕ) (hk : 1≤k) {beta m gamma error : ℝ}
    (hbeta : 0<beta) (hm0 : 0 < |m|) (hm1 : |m|<1)
    (hgamma : 0<gamma) (he : 0<error) :
    ∀ᶠ M : ℕ in atTop,∃ K : ℕ,∀ᶠ N : ℕ in atTop,
      beta*(rawValue k beta m).toReal/2-error≤
        (∫amp,perturbedCavityFunctional N M k K m beta ((N : ℝ)^gamma) amp
          ∂positiveCubeLaw K)/(M : ℝ) := by
  have HT := fixed_bulk_lower_of_moment_errors k hk hbeta hm0 hm1 he
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  filter_upwards [HT] with M HM
  obtain ⟨hM,LN,b,cap,hLN,hb,hb1,hcap,n,delta,hd,hLower⟩ := HM
  obtain ⟨depth,Q,hModels⟩ := exists_actual_population_marked_moments M k n hM hm beta hLN hb hb1 hcap hd
  let K := Q+1
  obtain ⟨V,hV,hAll⟩ := hModels K (Nat.le_succ Q)
  refine ⟨K,?_⟩
  have hGrow : Tendsto (fun N : ℕ => (N : ℝ)^gamma) atTop atTop :=
    (tendsto_rpow_atTop hgamma).comp tendsto_natCast_atTop_atTop
  filter_upwards [hGrow.eventually (eventually_ge_atTop V),eventually_gt_atTop (0 : ℕ)] with N hNV hN
  apply cube_cavity_lower_of_fixed_bulk_lower (N := N) (M := M) (k := k) (K := K)
    hN hM hm beta ((N : ℝ)^gamma) (beta*(rawValue k beta m).toReal/2-error)
  intro gB
  obtain ⟨x,hxs,hx,hxm,hx1,hMom⟩ := hAll hN gB ((N : ℝ)^gamma) hNV
  apply hLower N K hN ((N : ℝ)^gamma) gB depth x (grid (depth+1)) hxs hx hxm hx1
    (by rw [grid_zero]) (grid_monotone (Nat.succ_pos depth)) (grid_last (Nat.succ_pos depth))
  · intro j hj
    exact (hMom j hj).1
  · intro j hj
    exact (hMom j hj).2

theorem finite_pressure_lower (k : ℕ) (hk : 3≤k) {m : ℝ}
    (hm0 : 0 < |m|) (hm1 : |m|<1) :
    FinitePressureLower k m := by
  have hm : m∈Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  apply finitePressureLower_of_cavity k hk (gamma := 1/3) hm (by norm_num) (by norm_num)
  intro beta hbeta error he
  exact eventually_cube_cavity_lower k (by omega) hbeta hm0 hm1 (by norm_num) he

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPhysicalLower
