-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalJoint

/-! Terminal joint-good probability and the conditional root. Two marginal failure
bounds control the terminal good event.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalGood
open MeasureTheory ProbabilityTheory Set
open FiniteGaussianAffineKernel FiniteGaussianQuadraticSpine
open FiniteGaussianQuadraticSpineCutoffs FiniteGaussianQuadraticTerminalJoint
open FiniteCSGaussianDepthPrecision
open scoped ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def terminalGoodSet (M : ℕ) (C eps : ℝ) : Set (Model.Vector M×Model.Vector M) :=
  {p | ‖p.1‖^2≤C^2*(M : ℝ) ∧ |‖p.2‖^2-(M : ℝ)|≤eps*(M : ℝ)}

theorem terminalGoodSet_measurable (M : ℕ) (C eps : ℝ) :
    MeasurableSet (terminalGoodSet M C eps) := by
  change MeasurableSet ({p : Model.Vector M×Model.Vector M | ‖p.1‖^2≤C^2*(M : ℝ)}∩
    {p | |‖p.2‖^2-(M : ℝ)|≤eps*(M : ℝ)})
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    (measurableSet_le (by fun_prop) measurable_const)

def terminalGoodProbability {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (C eps : ℝ) (h : Model.Vector M) : ℝ :=
  (terminalJointKernel M hx hDelta hB h).real (terminalGoodSet M C eps)

theorem terminalGoodProbability_measurable {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (C eps : ℝ) :
    Measurable (terminalGoodProbability M hx hDelta hB C eps) :=
  ((terminalJointKernel M hx hDelta hB).measurable_coe (terminalGoodSet_measurable M C eps)).ennreal_toReal

theorem terminalGoodProbability_mem_Icc {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (C eps : ℝ) (h : Model.Vector M) :
    terminalGoodProbability M hx hDelta hB C eps h∈Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩

theorem joint_good_lower {M : ℕ} (nu : Measure (Model.Vector M×Model.Vector M))
    [IsProbabilityMeasure nu] (A S : Set (Model.Vector M))
    (hA : MeasurableSet A) (hS : MeasurableSet S) :
    1-nu.fst.real Aᶜ-nu.snd.real Sᶜ≤nu.real (A×ˢS) := by
  have hf : nu.fst.real Aᶜ=nu.real (Prod.fst ⁻¹' Aᶜ) := by
    rw [measureReal_def,Measure.fst_apply hA.compl]
    rfl
  have hs : nu.snd.real Sᶜ=nu.real (Prod.snd ⁻¹' Sᶜ) := by
    rw [measureReal_def,Measure.snd_apply hS.compl]
    rfl
  have heq : (A×ˢS)ᶜ=(Prod.fst ⁻¹' Aᶜ)∪(Prod.snd ⁻¹' Sᶜ) := by
    ext p
    simp only [mem_compl_iff,mem_prod,mem_union,mem_preimage,not_and_or]
  have H := measureReal_add_measureReal_compl (μ := nu) (hA.prod hS)
  rw [heq,probReal_univ] at H
  have HU := measureReal_union_le (μ := nu) (Prod.fst ⁻¹' Aᶜ) (Prod.snd ⁻¹' Sᶜ)
  rw [hf,hs]
  linarith only [H,HU]

theorem integral_kernel_real_comp {M : ℕ}
    (K : Kernel (Model.Vector M) (Model.Vector M×Model.Vector M)) [IsMarkovKernel K]
    (I : Kernel (Model.Vector M) (Model.Vector M)) (h : Model.Vector M)
    (S : Set (Model.Vector M×Model.Vector M)) (hS : MeasurableSet S) :
    (∫z,(K z).real S∂I h)=((K ∘ₖ I) h).real S := by
  rw [measureReal_def,Kernel.comp_apply' _ _ _ hS]
  exact integral_toReal (K.measurable_coe hS).aemeasurable
    (.of_forall (fun z => lt_top_iff_ne_top.mpr (measure_ne_top (K z) S)))

theorem terminalGoodProbability_root_integral {d : ℕ} (M : ℕ) {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 C eps : ℝ) :
    (∫g,terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g)
      ∂stdGaussian (Model.Vector M))=
      (rootJointKernel M hx hDelta hB y0 0).real (terminalGoodSet M C eps) := by
  have H := integral_kernel_real_comp (terminalJointKernel M hx hDelta hB)
    (affineKernel M 0 (Real.sqrt y0)) 0 (terminalGoodSet M C eps) (terminalGoodSet_measurable M C eps)
  change (∫z,terminalGoodProbability M hx hDelta hB C eps z
    ∂affineKernel M 0 (Real.sqrt y0) 0)=_ at H
  rw [affineKernel_apply,integral_map (by fun_prop : Measurable
    (fun g : Model.Vector M => (0 : ℝ) •(0 : Model.Vector M)+Real.sqrt y0 •g)).aemeasurable
    (terminalGoodProbability_measurable M hx hDelta hB C eps).aestronglyMeasurable] at H
  simpa only [zero_smul,zero_add,rootJointKernel] using H

theorem terminalGoodProbability_root_lower {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B y0 Bmax C eps : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (hMax : B≤Bmax) (hC : Bmax^2< C^2) (heps : 0< eps) :
    1-(4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2)+4/((M : ℝ)*eps^2))≤
      ∫g,terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g)
        ∂stdGaussian (Model.Vector M) := by
  let nu := rootJointKernel M hx hDelta hB y0 0
  let A := {h : Model.Vector M | ‖h‖^2≤C^2*(M : ℝ)}
  let S := {sigma : Model.Vector M | |‖sigma‖^2-(M : ℝ)|≤eps*(M : ℝ)}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hF : nu.fst=FiniteGaussianQuadraticForwardSpine.prefixStateKernel M hx hDelta hB y0 d 0 := by
    change (rootJointKernel M hx hDelta hB y0 0).map Prod.fst=_
    rw [← Kernel.fst_apply,rootJointKernel_fst]
  have hSpin : nu.snd=stdGaussian (Model.Vector M) := by
    change (rootJointKernel M hx hDelta hB y0 0).map Prod.snd=_
    rw [← Kernel.snd_apply]
    exact rootJointKernel_snd_eq_stdGaussian M hx hDelta hB hy hroot
  have hBadA : nu.fst.real Aᶜ≤4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2) := by
    rw [hF]
    simpa only [A,compl_setOf,not_le] using
      prefix_state_cutoff_bound hM hx hDelta hB hy hroot hMax hC (le_refl d)
  have hBadS : nu.snd.real Sᶜ≤4/((M : ℝ)*eps^2) := by
    rw [hSpin,← quenchedSpinLaw_eq_stdGaussian M hx hDelta hB hy hroot]
    simpa only [S,compl_setOf,not_le] using
      terminal_spin_shell_bad_mass hM hx hDelta hB hy hroot heps
  have H := joint_good_lower nu A S hA hS
  rw [terminalGoodProbability_root_integral]
  change 1-_≤nu.real (A×ˢS)
  linarith only [H,hBadA,hBadS]

theorem terminalGoodProbability_bad_root_mass {d M : ℕ} (hM : 0< M)
    {x Delta : Fin d→ℝ} {B y0 Bmax C eps : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (hMax : B≤Bmax) (hC : Bmax^2< C^2) (heps : 0< eps) :
    (stdGaussian (Model.Vector M)).real
      {g | terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g)< (1 : ℝ)/2}≤
      2*(4*Bmax^4/((M : ℝ)*(C^2-Bmax^2)^2)+4/((M : ℝ)*eps^2)) := by
  let G := fun g : Model.Vector M => terminalGoodProbability M hx hDelta hB C eps (Real.sqrt y0 •g)
  have hGm : Measurable G := (terminalGoodProbability_measurable M hx hDelta hB C eps).comp (by fun_prop)
  have hGb (g : Model.Vector M) : G g∈Icc (0 : ℝ) 1 :=
    terminalGoodProbability_mem_Icc M hx hDelta hB C eps _
  have hGi : Integrable G (stdGaussian (Model.Vector M)) :=
    (integrable_const (1 : ℝ)).mono' hGm.aestronglyMeasurable
      (.of_forall (fun g => by rw [Real.norm_eq_abs,abs_of_nonneg (hGb g).1]; exact (hGb g).2))
  have hDi := (integrable_const (1 : ℝ)).sub hGi
  have HM := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (fun g : Model.Vector M => sub_nonneg.mpr (hGb g).2)) hDi ((1 : ℝ)/2)
  have hsub : {g : Model.Vector M | G g<(1 : ℝ)/2}⊆{g | (1 : ℝ)/2≤1-G g} := by
    intro g hg
    change (1 : ℝ)/2≤1-G g
    change G g<(1 : ℝ)/2 at hg
    linarith only [hg]
  have HMass := measureReal_mono (μ := stdGaussian (Model.Vector M)) hsub
  have HL := terminalGoodProbability_root_lower hM hx hDelta hB hy hroot hMax hC heps
  have HMean : (∫g,(1-G g)∂stdGaussian (Model.Vector M))=
      1-∫g,G g∂stdGaussian (Model.Vector M) := by
    rw [integral_sub (integrable_const (1 : ℝ)) hGi,integral_const,probReal_univ,one_smul]
  change (stdGaussian (Model.Vector M)).real {g | G g<(1 : ℝ)/2}≤_
  change (1 : ℝ)/2*(stdGaussian (Model.Vector M)).real {g | (1 : ℝ)/2≤1-G g}≤
    ∫g,(1-G g)∂stdGaussian (Model.Vector M) at HM
  rw [HMean] at HM
  change 1-_≤∫g,G g∂stdGaussian (Model.Vector M) at HL
  linarith only [HM,HMass,HL]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticTerminalGood
