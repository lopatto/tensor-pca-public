-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticRootLoss

/-! Good-root averaging for a nonnegative integrable observable. The lower bound on the
good event comes from the spherical comparison; the Gaussian bad-root loss is
estimated here.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticGoodRootMean
open MeasureTheory ProbabilityTheory Set Filter
open FiniteGaussianQuadraticRootLoss OneStepGaussianShellMoments
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quadraticRoot_integral_eq {M : ℕ} (hM : 0<M) (c a : ℝ) :
    (∫g : Model.Vector M,c+a*‖g‖^2/(M : ℝ)∂stdGaussian (Model.Vector M))=c+a := by
  have hRadius : (∫g : Model.Vector M,‖g‖^2∂stdGaussian (Model.Vector M))=(M : ℝ) := by
    simpa using integral_norm_shift_sq (0 : Model.Vector M) 1
  have hI : Integrable (fun g : Model.Vector M ↦ ‖g‖^2) (stdGaussian (Model.Vector M)) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  rw [integral_add (integrable_const c) ((hI.const_mul a).div_const (M : ℝ)),
    integral_div,integral_const_mul,hRadius,integral_const,probReal_univ,one_smul]
  have hMN : (M : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hM
  field_simp [hMN]

theorem goodRoot_mean_lower {M : ℕ} (hM : 0<M) (c a : ℝ)
    (F : Model.Vector M→ℝ) (hF : Integrable F (stdGaussian (Model.Vector M)))
    (hF0 : ∀g,0≤F g) {bad : Set (Model.Vector M)} (hbad : MeasurableSet bad)
    {eta : ℝ} (hmass : (stdGaussian (Model.Vector M)).real bad≤eta)
    (hGood : ∀g,g∉bad → c+a*‖g‖^2/(M : ℝ)≤F g) :
    c+a-Real.sqrt (2*c^2+6*a^2)*Real.sqrt eta≤∫g,F g∂stdGaussian (Model.Vector M) := by
  let U := fun g : Model.Vector M ↦ c+a*‖g‖^2/(M : ℝ)
  have hU : Integrable U (stdGaussian (Model.Vector M)) :=
    (quadraticRoot_memLp_two M c a).integrable (by norm_num)
  have hGoodMean : (∫g in badᶜ,U g∂stdGaussian (Model.Vector M))≤
      ∫g in badᶜ,F g∂stdGaussian (Model.Vector M) := by
    apply integral_mono_ae hU.integrableOn hF.integrableOn
    exact (ae_restrict_iff' hbad.compl).mpr (.of_forall (fun g hg ↦ hGood g hg))
  have hSplitU := integral_add_compl hbad hU
  have hSplitF := integral_add_compl hbad hF
  have hBadF : 0≤∫g in bad,F g∂stdGaussian (Model.Vector M) :=
    setIntegral_nonneg hbad (fun g _ ↦ hF0 g)
  have hBadU := (le_abs_self (∫g in bad,U g∂stdGaussian (Model.Vector M))).trans
    (quadraticRoot_bad_integral_abs_le hM c a hbad hmass)
  rw [quadraticRoot_integral_eq hM c a] at hSplitU
  linarith only [hGoodMean,hSplitU,hSplitF,hBadF,hBadU]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticGoodRootMean
