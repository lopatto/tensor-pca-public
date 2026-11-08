-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticLogSteps

/-! Affine Gaussian log-step evaluation. Scalar compensation uses the one-coordinate
Gaussian bank and terminal sqrt(M)*h(0).
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianLinearLogSteps
open MeasureTheory ProbabilityTheory
open FiniteGaussianQuadraticStep FiniteGaussianQuadraticLogSteps
open FiniteGaussianLogStepsCompression OneStepGaussianStepLipschitz
open scoped NNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem affine_lipschitz {N : ℕ} (u : Model.Vector N) (C : ℝ) :
    LipschitzWith ‖u‖₊ (fun h : Model.Vector N => C+inner ℝ u h) := by
  apply LipschitzWith.of_dist_le_mul
  intro h h'
  change |(C+inner ℝ u h)-(C+inner ℝ u h')|≤‖u‖*‖h-h'‖
  rw [add_sub_add_left_eq_sub,← inner_sub_right]
  exact abs_real_inner_le_norm _ _

def scalarCoefficient (M : ℕ) : Model.Vector 1 :=
  EuclideanSpace.single (0 : Fin 1) (Real.sqrt (M : ℝ))

theorem scalarCoefficient_inner (M : ℕ) (h : Model.Vector 1) :
    inner ℝ (scalarCoefficient M) h=Real.sqrt (M : ℝ)*h 0 := by
  simp [scalarCoefficient,EuclideanSpace.inner_single_left]

theorem scalarCoefficient_norm_sq (M : ℕ) : ‖scalarCoefficient M‖^2=(M : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [scalarCoefficient,EuclideanSpace.single,PiLp.single_apply,Real.sq_sqrt (Nat.cast_nonneg M)]

theorem affine_exp_integrable {N : ℕ} (C : ℝ) (u h : Model.Vector N) (mass Delta : ℝ) :
    Integrable (fun g : Model.Vector N => Real.exp (mass*(C+inner ℝ u (h+shift N Delta g))))
      (stdGaussian (Model.Vector N)) :=
  shifted_exp_integrable (affine_lipschitz u C) (shift N Delta) mass h

theorem gaussianNormalizer_affine {N : ℕ} (C : ℝ) (u h : Model.Vector N) (mass : ℝ)
    {Delta : ℝ} (hDelta : 0≤Delta) :
    gaussianNormalizer (shift N Delta) mass (fun z => C+inner ℝ u z) h=
      Real.exp (mass*(C+inner ℝ u h)+mass^2*Delta*‖u‖^2/2) := by
  have hfun : (fun g : Model.Vector N => Real.exp (mass*(C+inner ℝ u (h+shift N Delta g))))=
      (fun g => Real.exp (mass*(C+inner ℝ u h))*Real.exp ((mass*Real.sqrt Delta)*inner ℝ u g)) := by
    funext g
    rw [← Real.exp_add]
    congr 1
    simp only [shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,inner_add_right,inner_smul_right]
    ring
  unfold gaussianNormalizer
  rw [hfun,integral_const_mul,GaussianDensityProofs.integral_exp_inner_stdGaussian,← Real.exp_add]
  congr 1
  rw [mul_pow,Real.sq_sqrt hDelta]

theorem gaussianLogStep_affine {N : ℕ} (C : ℝ) (u h : Model.Vector N) (mass : ℝ)
    {Delta : ℝ} (hDelta : 0≤Delta) :
    gaussianLogStep (shift N Delta) mass (fun z => C+inner ℝ u z) h=
      C+inner ℝ u h+mass*Delta*‖u‖^2/2 := by
  by_cases hm : mass=0
  · subst mass
    simp only [gaussianLogStep,↓reduceIte,zero_mul,zero_div,add_zero]
    have hfun : (fun g : Model.Vector N => C+inner ℝ u (h+shift N Delta g))=
        (fun g => (C+inner ℝ u h)+Real.sqrt Delta*inner ℝ u g) := by
      funext g
      simp only [shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,inner_add_right,inner_smul_right]
      ring
    have hI : Integrable (fun g : Model.Vector N => inner ℝ u g) (stdGaussian (Model.Vector N)) :=
      IsGaussian.memLp_two_id.const_inner u |>.integrable one_le_two
    have hMean : (∫g : Model.Vector N,inner ℝ u g∂stdGaussian (Model.Vector N))=0 :=
      integral_strongDual_stdGaussian (innerSL ℝ u)
    rw [hfun,integral_add (integrable_const _) (hI.const_mul _),integral_const,
      probReal_univ,one_smul,integral_const_mul,hMean,mul_zero,add_zero]
  · simp only [gaussianLogStep,if_neg hm]
    rw [gaussianNormalizer_affine C u h mass hDelta,Real.log_exp]
    field_simp
    <;> ring

theorem gaussianLogSteps_affine {d N : ℕ} (x Delta : Fin d→ℝ) (hDelta : ∀j,0≤Delta j)
    (C : ℝ) (u h : Model.Vector N) :
    gaussianLogSteps (quadraticSteps N x Delta) (fun z => C+inner ℝ u z) h=
      C+inner ℝ u h+‖u‖^2/2*(∑j : Fin d,x j*Delta j) := by
  let H := fun i (z : Model.Vector N) =>
    C+‖u‖^2/2*FiniteCSGaussianDepthPrecision.tail (fun j => x j*Delta j) i+inner ℝ u z
  have hEnd : H (quadraticSteps N x Delta).length=(fun z => C+inner ℝ u z) := by
    simp only [H,quadraticSteps,List.length_ofFn,FiniteCSGaussianDepthPrecision.tail_end,mul_zero,add_zero]
  have hStep (i : ℕ) (hi : i<(quadraticSteps N x Delta).length) :
      H i=gaussianLogStep ((quadraticSteps N x Delta)[i]).2 ((quadraticSteps N x Delta)[i]).1 (H (i+1)) := by
    have hi' : i<d := by simpa only [quadraticSteps,List.length_ofFn] using hi
    let j : Fin d := ⟨i,hi'⟩
    have HT := FiniteCSGaussianDepthPrecision.tail_succ (fun l => x l*Delta l) hi'
    funext z
    have HG := gaussianLogStep_affine
      (C+‖u‖^2/2*FiniteCSGaussianDepthPrecision.tail (fun l => x l*Delta l) (i+1)) u z
      (mass := x j) (hDelta j)
    calc
      H i z=(C+‖u‖^2/2*FiniteCSGaussianDepthPrecision.tail (fun l => x l*Delta l) (i+1))+
          inner ℝ u z+x j*Delta j*‖u‖^2/2 := by
        dsimp only [H]
        rw [HT]
        ring
      _=gaussianLogStep (shift N (Delta j)) (x j) (H (i+1)) z := HG.symm
      _=gaussianLogStep ((quadraticSteps N x Delta)[i]).2 ((quadraticSteps N x Delta)[i]).1 (H (i+1)) z := by
        simp only [quadraticSteps,List.getElem_ofFn]
        rfl
  have HE := gaussianLogSteps_eq_of_recursion (quadraticSteps N x Delta)
    (fun z => C+inner ℝ u z) H hEnd hStep
  calc
    _=H 0 h := congrArg (fun F => F h) HE
    _=_ := by dsimp only [H]; rw [FiniteCSGaussianDepthPrecision.tail_zero]; ring

theorem expected_gaussianLogSteps_affine_integrable {d N : ℕ} (x Delta : Fin d→ℝ)
    (C : ℝ) (u : Model.Vector N) (rootScale : ℝ) :
    Integrable (fun g : Model.Vector N =>
      gaussianLogSteps (quadraticSteps N x Delta) (fun z => C+inner ℝ u z) (rootScale •g))
      (stdGaussian (Model.Vector N)) := by
  simpa only [zero_add,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using
    shifted_integrable (gaussianLogSteps_lipschitz (affine_lipschitz u C) (quadraticSteps N x Delta))
      (rootScale •ContinuousLinearMap.id ℝ (Model.Vector N)) (0 : Model.Vector N)

theorem expected_gaussianLogSteps_affine {d N : ℕ} (x Delta : Fin d→ℝ) (hDelta : ∀j,0≤Delta j)
    (C : ℝ) (u : Model.Vector N) (rootScale : ℝ) :
    (∫g : Model.Vector N,gaussianLogSteps (quadraticSteps N x Delta) (fun z => C+inner ℝ u z)
      (rootScale •g)∂stdGaussian (Model.Vector N))=
      C+‖u‖^2/2*(∑j : Fin d,x j*Delta j) := by
  simp_rw [gaussianLogSteps_affine x Delta hDelta]
  have hfun : (fun g : Model.Vector N => C+inner ℝ u (rootScale •g)+‖u‖^2/2*(∑j : Fin d,x j*Delta j))=
      (fun g => (C+‖u‖^2/2*(∑j : Fin d,x j*Delta j))+rootScale*inner ℝ u g) := by
    funext g
    rw [inner_smul_right]
    ring
  have hI : Integrable (fun g : Model.Vector N => inner ℝ u g) (stdGaussian (Model.Vector N)) :=
    IsGaussian.memLp_two_id.const_inner u |>.integrable one_le_two
  have hMean : (∫g : Model.Vector N,inner ℝ u g∂stdGaussian (Model.Vector N))=0 :=
    integral_strongDual_stdGaussian (innerSL ℝ u)
  rw [hfun,integral_add (integrable_const _) (hI.const_mul _),integral_const,
    probReal_univ,one_smul,integral_const_mul,hMean,mul_zero,add_zero]

theorem expected_scalar_compensation {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ)
    (hDelta : ∀j,0≤Delta j) (rootVariance : ℝ) :
    (∫g : Model.Vector 1,gaussianLogSteps (quadraticSteps 1 x Delta)
      (fun h => Real.sqrt (M : ℝ)*h 0) (Real.sqrt rootVariance •g)
      ∂stdGaussian (Model.Vector 1))=(M : ℝ)/2*(∑j : Fin d,x j*Delta j) := by
  simpa only [zero_add,scalarCoefficient_inner,scalarCoefficient_norm_sq] using
    expected_gaussianLogSteps_affine x Delta hDelta 0 (scalarCoefficient M) (Real.sqrt rootVariance)

theorem expected_scalar_compensation_integrable {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ)
    (rootVariance : ℝ) :
    Integrable (fun g : Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 x Delta)
      (fun h => Real.sqrt (M : ℝ)*h 0) (Real.sqrt rootVariance •g))
      (stdGaussian (Model.Vector 1)) := by
  simpa only [zero_add,scalarCoefficient_inner] using
    expected_gaussianLogSteps_affine_integrable x Delta 0 (scalarCoefficient M) (Real.sqrt rootVariance)


end
end TensorPCA.NonRSLowerProofs.FiniteGaussianLinearLogSteps
