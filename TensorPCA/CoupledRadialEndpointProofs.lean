-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.SpherePolarProofs
public import TensorPCA.ChiSquareTailProofs
public import TensorPCA.GaussianMaximumComparisonProofs
public import TensorPCA.CoupledGaussianIntegralProofs
public import TensorPCA.CoupledEndpointModel
public import Mathlib.Probability.ConditionalProbability

/-! Radial barycenter comparison for the coupled thermal endpoint.
A retained probability law is constructed from the radius distribution;
its mean is exactly one and its density cost is at most the upper-tail probability. Scalar Jensen is applied to the random exponent, never a presumed
jointly convex bilinear function of the two radii. -/

@[expose] public section
namespace TensorPCA.CoupledRadialEndpointProofs
open MeasureTheory ProbabilityTheory Set Filter CoupledEndpointModel
open scoped Topology RealInnerProductSpace ENNReal ProbabilityTheory
noncomputable section

/-- An explicit retained mean-one probability law. Mixing the original law
with its actual upper-tail conditioning replaces the cutoff selection in the
PT barycenter argument, with exactly the same upper-tail domination cost. -/
theorem exists_mean_one_retained_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun r : ℝ ↦ r) μ) (hSq : Integrable (fun r : ℝ ↦ r^2) μ)
    (hmean : (∫ r : ℝ, r ∂μ) ≤ 1) (htail : 0 < μ.real (Ici (1 : ℝ))) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ Integrable (fun r : ℝ ↦ r) ν ∧
      Integrable (fun r : ℝ ↦ r^2) ν ∧ (∫ r : ℝ, r ∂ν) = 1 ∧
        ν ≤ (μ (Ici (1 : ℝ)))⁻¹ • μ := by
  let S := Ici (1 : ℝ)
  let cap : ℝ≥0∞ := (μ S)⁻¹
  have hmass : μ S ≠ 0 := by
    intro hz
    have hh : μ.real S = 0 := by simp only [Measure.real, hz, ENNReal.toReal_zero]
    exact htail.ne' hh
  have hcap : cap ≠ ∞ := ENNReal.inv_ne_top.mpr hmass
  have hcap1 : 1 ≤ cap := ENNReal.one_le_inv.mpr prob_le_one
  have hFull : μ ≤ cap • μ := by
    intro s
    rw [Measure.smul_apply, smul_eq_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap1 (zero_le : (0 : ℝ≥0∞) ≤ μ s)
  let T := ProbabilityTheory.cond μ S
  have : IsProbabilityMeasure T := cond_isProbabilityMeasure hmass
  have hiT : Integrable (fun r : ℝ ↦ r) T := hi.restrict.smul_measure hcap
  have hTailDom : T ≤ cap • μ := by
    intro s
    simp only [T, ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (Measure.restrict_apply_le S s) (zero_le : (0 : ℝ≥0∞) ≤ cap)
  let M := ∫ r : ℝ, r ∂μ
  let L := ∫ r : ℝ, r ∂T
  have hTailMean : 1 ≤ L := by
    have hLow : μ.real S ≤ ∫ r in S, r ∂μ := by
      have H := integral_mono_ae (integrable_const (1 : ℝ)) hi.restrict
        ((ae_restrict_mem measurableSet_Ici).mono (fun r hr ↦ hr))
      simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using H
    have heq : L = (∫ r in S, r ∂μ)/μ.real S := by
      simp only [L,T,ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,Measure.real]
      ring
    rw [heq]
    exact (le_div_iff₀ htail).mpr (by simpa only [one_mul] using hLow)
  by_cases hEq : L = M
  · refine ⟨μ,inferInstance,hi,hSq,?_,hFull⟩
    change M = 1
    linarith
  · have hDen : 0 < L-M := sub_pos.mpr (lt_of_le_of_ne (hmean.trans hTailMean) (Ne.symm hEq))
    let t := (1-M)/(L-M)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hmean) hDen.le
    have ht1 : t ≤ 1 := (div_le_one hDen).mpr (by linarith)
    have hOne : 0 ≤ 1-t := sub_nonneg.mpr ht1
    let ν := ENNReal.ofReal (1-t) • μ+ENNReal.ofReal t • T
    have hνprob : IsProbabilityMeasure ν := by
      constructor
      simp only [ν,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
      rw [← ENNReal.ofReal_add hOne ht0]
      simp only [sub_add_cancel,ENNReal.ofReal_one]
    have hνDom : ν ≤ cap • μ := by
      intro s
      simp only [ν,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
      have hF := hFull s
      have hT := hTailDom s
      simp only [Measure.smul_apply,smul_eq_mul] at hF hT
      calc
        _ ≤ ENNReal.ofReal (1-t)*(cap*μ s)+ENNReal.ofReal t*(cap*μ s) :=
          add_le_add (mul_le_mul_of_nonneg_left hF (zero_le : (0 : ℝ≥0∞) ≤ _))
            (mul_le_mul_of_nonneg_left hT (zero_le : (0 : ℝ≥0∞) ≤ _))
        _ = (ENNReal.ofReal (1-t)+ENNReal.ofReal t)*(cap*μ s) := by ring
        _ = _ := by rw [← ENNReal.ofReal_add hOne ht0,sub_add_cancel,ENNReal.ofReal_one,one_mul]
    refine ⟨ν,hνprob,hi.of_measure_le_smul hcap hνDom,hSq.of_measure_le_smul hcap hνDom,?_,hνDom⟩
    rw [integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top) (hiT.smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure,integral_smul_measure,ENNReal.toReal_ofReal hOne,ENNReal.toReal_ofReal ht0]
    change (1-t)*M+t*L = 1
    dsimp [t]
    field_simp [hDen.ne']
    ring

/-- The actual radius normalized by the physical A4 diagonal precision. -/
def gaussianRadiusLaw (N : ℕ) (b : ℝ) : Measure ℝ :=
  (stdGaussian (Model.Vector N)).map (fun g ↦ ‖g‖/Real.sqrt ((N : ℝ)*b))

instance gaussianRadiusLaw_probability (N : ℕ) (b : ℝ) : IsProbabilityMeasure (gaussianRadiusLaw N b) := by
  unfold gaussianRadiusLaw
  infer_instance

theorem gaussianRadiusLaw_memLp_two (N : ℕ) (b : ℝ) :
    MemLp (fun r : ℝ ↦ r) 2 (gaussianRadiusLaw N b) := by
  unfold gaussianRadiusLaw
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable (by fun_prop)).mpr
  have hnorm : MemLp (fun g : Model.Vector N ↦ ‖g‖) 2 (stdGaussian (Model.Vector N)) :=
    IsGaussian.memLp_two_id.norm
  simpa only [Function.comp_def,id_eq,div_eq_mul_inv,mul_comm] using
    hnorm.const_mul (Real.sqrt ((N : ℝ)*b))⁻¹

theorem gaussianRadiusLaw_mean_le_one {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    (∫ r : ℝ, r ∂gaussianRadiusLaw N b) ≤ 1 := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hs : 0 < Real.sqrt ((N : ℝ)*b) := Real.sqrt_pos.mpr (mul_pos hNp hbp)
  unfold gaussianRadiusLaw
  rw [integral_map (by fun_prop) (by fun_prop),integral_div]
  apply (div_le_one hs).mpr
  apply (show (∫ g : Model.Vector N, ‖g‖ ∂stdGaussian (Model.Vector N)) ≤ Real.sqrt N from by
    simpa only [finrank_euclideanSpace_fin] using
      (GaussianNormMean.integral_norm_stdGaussian_le_sqrt_finrank (E := Model.Vector N))).trans
  apply Real.sqrt_le_sqrt
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hNp.le

theorem gaussianRadiusLaw_tail_eq {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    gaussianRadiusLaw N b (Ici (1 : ℝ)) = gaussianTailMass N b := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hs : 0 < Real.sqrt ((N : ℝ)*b) := Real.sqrt_pos.mpr (mul_pos hNp hbp)
  unfold gaussianRadiusLaw gaussianTailMass
  rw [Measure.map_apply (by fun_prop) measurableSet_Ici]
  congr 1
  ext g
  change (1 ≤ ‖g‖/Real.sqrt ((N : ℝ)*b)) ↔ (N : ℝ)*b ≤ ‖g‖^2
  rw [le_div_iff₀ hs,one_mul]
  have he := Real.sq_sqrt (mul_nonneg hNp.le hbp.le)
  constructor
  · intro h
    exact he.symm.trans_le ((sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg g)).mpr h)
  · intro h
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg g)).mp (he.trans_le h)

/-- The actual Gaussian radius supplies a constructed retained mean-one law,
with finite second moment and exactly the true Gaussian tail domination. -/
theorem exists_gaussian_retained_radius {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 1 ≤ b) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ Integrable (fun r : ℝ ↦ r) ν ∧
      Integrable (fun r : ℝ ↦ r^2) ν ∧ (∫ r : ℝ, r ∂ν) = 1 ∧
        ν ≤ (gaussianTailMass N b)⁻¹ • gaussianRadiusLaw N b := by
  have hp := (ChiSquareTailProofs.chiSquare_tail_lower hN hb).1
  have htail : 0 < (gaussianRadiusLaw N b).real (Ici (1 : ℝ)) := by
    rw [Measure.real,gaussianRadiusLaw_tail_eq hN hb]
    exact hp
  obtain ⟨ν,hν,hi,hSq,hm,hdom⟩ := exists_mean_one_retained_law (gaussianRadiusLaw N b)
    ((gaussianRadiusLaw_memLp_two N b).integrable (by norm_num))
    (gaussianRadiusLaw_memLp_two N b).integrable_sq (gaussianRadiusLaw_mean_le_one hN hb) htail
  rw [gaussianRadiusLaw_tail_eq hN hb] at hdom
  exact ⟨ν,hν,hi,hSq,hm,hdom⟩

/-- Scaling the already verified sphere/radius reconstruction gives the
literal A4 Gaussian vector law. No substitute angular distribution is used. -/
theorem gaussianRadiusLaw_radial_reconstruction {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) :
    MeasurePreserving (fun p : Model.Vector N × ℝ ↦ (Real.sqrt N*p.2) • p.1)
      ((Model.spherePrior N).prod (gaussianRadiusLaw N b))
      ((stdGaussian (Model.Vector N)).map (fun g ↦ (Real.sqrt b)⁻¹ • g)) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNp).ne'
  have hsB : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hr : gaussianRadiusLaw N b =
      ((stdGaussian (Model.Vector N)).map (fun g ↦ ‖g‖)).map
        (fun r ↦ r/Real.sqrt ((N : ℝ)*b)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  refine ⟨by fun_prop, ?_⟩
  rw [hr, ← (Measure.map_id (μ := Model.spherePrior N)),
    Measure.map_prod_map _ _ measurable_id (show Measurable (fun r : ℝ ↦ r/Real.sqrt ((N : ℝ)*b)) by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : (fun p : Model.Vector N × ℝ ↦ (Real.sqrt N*p.2) • p.1) ∘
      Prod.map id (fun r : ℝ ↦ r/Real.sqrt ((N : ℝ)*b)) =
      (fun g : Model.Vector N ↦ (Real.sqrt b)⁻¹ • g) ∘
        (fun p : Model.Vector N × ℝ ↦ p.2 • p.1) := by
    funext p
    simp only [Prod.map,id_eq,Function.comp_apply,smul_smul,Real.sqrt_mul hNp.le]
    congr 1
    field_simp
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    (SpherePolarProofs.spherePrior_gaussian_radial_reconstruction hN).map_eq]

/-- Mean one forces the second moment to be at least one. -/
theorem retained_second_moment_ge_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun r : ℝ ↦ r) ν) (hSq : Integrable (fun r : ℝ ↦ r^2) ν)
    (hm : (∫ r : ℝ, r ∂ν) = 1) : 1 ≤ ∫ r : ℝ, r^2 ∂ν := by
  have hn : 0 ≤ ∫ r : ℝ, (r^2-2*r)+1 ∂ν :=
    integral_nonneg (fun r ↦ by change 0 ≤ r^2-2*r+1; nlinarith [sq_nonneg (r-1)])
  rw [integral_add (f := fun r : ℝ ↦ r^2-2*r) (g := fun _ ↦ (1 : ℝ))
      (hSq.sub (hi.const_mul 2)) (integrable_const (1 : ℝ)),
    integral_sub (f := fun r : ℝ ↦ r^2) (g := fun r ↦ 2*r) hSq (hi.const_mul 2),integral_const_mul,hm] at hn
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
    (show 1 ≤ ∫ r : ℝ, r^2 ∂ν from by
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hn
      linarith)

/-- The random exponent used in the PT radial barycenter argument. -/
def radialExponent (A B C D : ℝ) (rs : ℝ × ℝ) : ℝ :=
  A*rs.1+B*rs.2+C*(rs.1*rs.2)+D*(rs.1^2+rs.2^2)

theorem radialExponent_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun r : ℝ ↦ r) ν) (hSq : Integrable (fun r : ℝ ↦ r^2) ν)
    (A B C D : ℝ) : Integrable (radialExponent A B C D) (ν.prod ν) :=
  (((hi.comp_fst ν).const_mul A).add ((hi.comp_snd ν).const_mul B)).add
    (((hi.mul_prod hi).const_mul C).add (((hSq.comp_fst ν).add (hSq.comp_snd ν)).const_mul D)) |>.congr
      (Eventually.of_forall (fun rs ↦ by dsimp [radialExponent]; ring))

/-- Independence keeps the bilinear mean exact. A nonnegative fresh-level
quadratic contributes at least its value at the mean radii. -/
theorem radialExponent_mean_lower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun r : ℝ ↦ r) ν) (hSq : Integrable (fun r : ℝ ↦ r^2) ν)
    (hm : (∫ r : ℝ, r ∂ν) = 1) (A B C : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    A+B+C+2*D ≤ ∫ rs, radialExponent A B C D rs ∂ν.prod ν := by
  have h1 := hi.comp_fst ν
  have h2 := hi.comp_snd ν
  have h12 := hi.mul_prod hi
  have h11 := hSq.comp_fst ν
  have h22 := hSq.comp_snd ν
  have he1 : (∫ rs : ℝ × ℝ, rs.1 ∂ν.prod ν) = 1 := by
    rw [integral_prod _ h1]
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hm
  have he2 : (∫ rs : ℝ × ℝ, rs.2 ∂ν.prod ν) = 1 := by
    rw [integral_prod _ h2]
    simp only [hm,integral_const,probReal_univ,smul_eq_mul,one_mul]
  have he11 : (∫ rs : ℝ × ℝ, rs.1^2 ∂ν.prod ν) = ∫ r : ℝ,r^2 ∂ν := by
    rw [integral_prod _ h11]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  have he22 : (∫ rs : ℝ × ℝ, rs.2^2 ∂ν.prod ν) = ∫ r : ℝ,r^2 ∂ν := by
    rw [integral_prod _ h22]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hs := retained_second_moment_ge_one ν hi hSq hm
  unfold radialExponent
  rw [integral_add (f := fun rs : ℝ × ℝ ↦ A*rs.1+B*rs.2+C*(rs.1*rs.2))
      (g := fun rs ↦ D*(rs.1^2+rs.2^2))
      (((h1.const_mul A).add (h2.const_mul B)).add (h12.const_mul C)) ((h11.add h22).const_mul D),
    integral_add (f := fun rs : ℝ × ℝ ↦ A*rs.1+B*rs.2) (g := fun rs ↦ C*(rs.1*rs.2))
      ((h1.const_mul A).add (h2.const_mul B)) (h12.const_mul C),
    integral_add (h1.const_mul A) (h2.const_mul B),
    integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul,
    integral_add h11 h22,he1,he2,he11,he22,integral_prod_mul (fun r : ℝ ↦ r) (fun r : ℝ ↦ r),hm]
  nlinarith

/-- Scalar Jensen on the exponent is valid despite its bilinear term.
The exponential's integrability is an analytic prerequisite, later
supplied by the positive-precision Gaussian integral. -/
theorem radial_jensen (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun r : ℝ ↦ r) ν) (hSq : Integrable (fun r : ℝ ↦ r^2) ν)
    (hm : (∫ r : ℝ, r ∂ν) = 1) (A B C : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (he : Integrable (fun rs ↦ Real.exp (radialExponent A B C D rs)) (ν.prod ν)) :
    Real.exp (A+B+C+2*D) ≤ ∫ rs, Real.exp (radialExponent A B C D rs) ∂ν.prod ν := by
  have hp := radialExponent_integrable ν hi hSq A B C D
  let M := ∫ rs, radialExponent A B C D rs ∂ν.prod ν
  have ht : Integrable (fun rs ↦ Real.exp M*(radialExponent A B C D rs-M+1)) (ν.prod ν) :=
    ((hp.sub (integrable_const M)).add (integrable_const (1 : ℝ))).const_mul _
  have hmono : (∫ rs, Real.exp M*(radialExponent A B C D rs-M+1) ∂ν.prod ν) ≤
      ∫ rs, Real.exp (radialExponent A B C D rs) ∂ν.prod ν := by
    apply integral_mono ht he
    intro rs
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (radialExponent A B C D rs-M))
      (Real.exp_pos M).le
    rw [← Real.exp_add] at hh
    rw [show M+(radialExponent A B C D rs-M) = radialExponent A B C D rs by ring] at hh
    exact hh
  have htEq : (∫ rs, Real.exp M*(radialExponent A B C D rs-M+1) ∂ν.prod ν) = Real.exp M := by
    rw [integral_const_mul,
      integral_add (f := fun rs ↦ radialExponent A B C D rs-M) (g := fun _ ↦ (1 : ℝ))
        (hp.sub (integrable_const M)) (integrable_const (1 : ℝ)),
      integral_sub hp (integrable_const M)]
    simp only [M,integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self,zero_add,mul_one]
  rw [htEq] at hmono
  exact (Real.exp_le_exp.mpr (radialExponent_mean_lower ν hi hSq hm A B C hD)).trans hmono

/-- Reordering independent factors preserves their actual product laws. -/
theorem measurePreserving_pairShuffle {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) ↦ ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μb μc μd))
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μa μc (μb.prod μd))
  have H := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  exact H

/-- The two-sphere/two-radius construction reconstructs two independent
literal precision-b Gaussians. -/
theorem gaussianRadiusLaw_pair_reconstruction {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) :
    MeasurePreserving (fun p : (Model.Vector N × Model.Vector N) × (ℝ × ℝ) ↦
      ((Real.sqrt N*p.2.1) • p.1.1,(Real.sqrt N*p.2.2) • p.1.2))
      (((Model.spherePrior N).prod (Model.spherePrior N)).prod
        ((gaussianRadiusLaw N b).prod (gaussianRadiusLaw N b)))
      ((CoupledGaussianIntegralProofs.scaledStdGaussian N b).prod
        (CoupledGaussianIntegralProofs.scaledStdGaussian N b)) := by
  exact ((gaussianRadiusLaw_radial_reconstruction hN hb).prod
    (gaussianRadiusLaw_radial_reconstruction hN hb)).comp
      (measurePreserving_pairShuffle (Model.spherePrior N) (Model.spherePrior N)
        (gaussianRadiusLaw N b) (gaussianRadiusLaw N b))

theorem spherePair_norm_ae {N : ℕ} (hN : 0 < N) :
    ∀ᵐ xy : Model.Vector N × Model.Vector N ∂(Model.spherePrior N).prod (Model.spherePrior N),
      ‖xy.1‖ = 1 ∧ ‖xy.2‖ = 1 := by
  have hx : ∀ᵐ xy : Model.Vector N × Model.Vector N ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hy : ∀ᵐ xy : Model.Vector N × Model.Vector N ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.2‖ = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hN)
  exact hx.and hy

/-- The actual angular/radial exponent, with the fresh level retained. -/
def radialPairWeight (N : ℕ) (a d L : ℝ) (g : Model.Vector N)
    (xy : Model.Vector N × Model.Vector N) (rs : ℝ × ℝ) : ℝ :=
  Real.exp (radialExponent (Real.sqrt ((N : ℝ)*a)*inner ℝ xy.1 g)
    (Real.sqrt ((N : ℝ)*a)*inner ℝ xy.2 g) ((N : ℝ)*L*inner ℝ xy.1 xy.2)
      ((N : ℝ)*(d-a)/2) rs)

theorem radialPairWeight_eq {N : ℕ} (a d L : ℝ) (g : Model.Vector N)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1)
    (rs : ℝ × ℝ) :
    radialPairWeight N a d L g xy rs =
      CoupledGaussianIntegralProofs.pairWeight N (d-a) L (Real.sqrt a • g)
        ((Real.sqrt N*rs.1) • xy.1,(Real.sqrt N*rs.2) • xy.2) := by
  unfold radialPairWeight radialExponent CoupledGaussianIntegralProofs.pairWeight
  congr 1
  simp only [inner_add_right,real_inner_smul_left,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,hx,hy,mul_one,
    Real.sq_sqrt (Nat.cast_nonneg N),Real.sqrt_mul (Nat.cast_nonneg N)]
  rw [real_inner_comm g xy.1,real_inner_comm g xy.2]
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

theorem radialPairWeight_integrable {N : ℕ} (hN : 0 < N) {a d L : ℝ}
    (ha : 0 ≤ a) (hd : a ≤ d) (hL : 0 ≤ L) (hP : 0 < 1+a-L) (g : Model.Vector N) :
    Integrable (fun p ↦ radialPairWeight N a d L g p.1 p.2)
      (((Model.spherePrior N).prod (Model.spherePrior N)).prod
        ((gaussianRadiusLaw N (1+d)).prod (gaussianRadiusLaw N (1+d)))) := by
  have hR := gaussianRadiusLaw_pair_reconstruction hN (by linarith : 0 < 1+d)
  have hi := hR.integrable_comp_of_integrable
    (CoupledGaussianIntegralProofs.endpointMoment_integrable N ha hd hL hP g)
  apply hi.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (spherePair_norm_ae hN)] with p hp
  exact (radialPairWeight_eq a d L g p.1 hp.1 hp.2 p.2).symm

theorem radialPairWeight_integral {N : ℕ} (hN : 0 < N) {a d L : ℝ}
    (ha : 0 ≤ a) (hd : a ≤ d) (_hL : 0 ≤ L) (_hP : 0 < 1+a-L) (g : Model.Vector N) :
    (∫ p, radialPairWeight N a d L g p.1 p.2
      ∂((Model.spherePrior N).prod (Model.spherePrior N)).prod
        ((gaussianRadiusLaw N (1+d)).prod (gaussianRadiusLaw N (1+d)))) =
      CoupledGaussianIntegralProofs.endpointMoment N a d L g := by
  have hR := gaussianRadiusLaw_pair_reconstruction hN (by linarith : 0 < 1+d)
  rw [CoupledGaussianIntegralProofs.endpointMoment,CoupledGaussianIntegralProofs.pairMoment,
    ← hR.map_eq,integral_map hR.measurable.aemeasurable (by unfold CoupledGaussianIntegralProofs.pairWeight; fun_prop)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (spherePair_norm_ae hN)] with p hp
  exact radialPairWeight_eq a d L g p.1 hp.1 hp.2 p.2

/-- Two retained radii cost at most the square of the actual tail inverse. -/
theorem retained_pair_domination {N : ℕ} {b : ℝ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hdom : ν ≤ (gaussianTailMass N b)⁻¹ • gaussianRadiusLaw N b) :
    ((Model.spherePrior N).prod (Model.spherePrior N)).prod (ν.prod ν) ≤
      ((gaussianTailMass N b)⁻¹*(gaussianTailMass N b)⁻¹) •
        (((Model.spherePrior N).prod (Model.spherePrior N)).prod
          ((gaussianRadiusLaw N b).prod (gaussianRadiusLaw N b))) := by
  have h := Measure.prod_mono (le_refl ((Model.spherePrior N).prod (Model.spherePrior N)))
    (Measure.prod_mono hdom hdom)
  simpa only [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul] using h

theorem commonWeight_integrable {N : ℕ} (hN : 0 < N) (a : ℝ) (g : Model.Vector N) :
    Integrable (fun xy : Model.Vector N × Model.Vector N ↦
      Real.exp (Real.sqrt ((N : ℝ)*a)*inner ℝ (xy.1+xy.2) g))
      ((Model.spherePrior N).prod (Model.spherePrior N)) := by
  have hi := GaussianSpinInterpolation.weight_integrable
    ((Model.spherePrior N).prod (Model.spherePrior N)) (fun _ ↦ (1 : ℝ))
    (CoupledGaussianKernelProofs.commonLinear N a) measurable_const
    (CoupledGaussianKernelProofs.commonLinear_continuous N a).measurable (C := 1)
    ((spherePair_norm_ae hN).mono (fun xy hxy ↦ ⟨by norm_num,
      CoupledGaussianKernelProofs.commonLinear_norm_le N a xy hxy.1 hxy.2⟩)) g
  unfold GaussianSpinInterpolation.weight CoupledGaussianKernelProofs.commonLinear at hi
  simpa only [one_mul,smul_apply,innerSL_apply_apply,smul_eq_mul] using hi

/-- Actual pointwise PT endpoint comparison. Its two tail factors come from
two explicitly constructed mean-one retained radius laws. -/
theorem signed_common_radial_bound {N : ℕ} (hN : 0 < N) {a d L : ℝ}
    (ha : 0 ≤ a) (hd : a ≤ d) (hL : 0 ≤ L) (hP : 0 < 1+a-L)
    (u eta : ℝ) (g : Model.Vector N) :
    Real.exp ((N : ℝ)*(d-a))*signedCommonPartition N a u eta g ≤
      Real.exp (-(N : ℝ)*L*u+(N : ℝ)*L*eta)/(gaussianTailMass N (1+d)).toReal^2 *
        CoupledGaussianIntegralProofs.endpointMoment N a d L g := by
  let μ := (Model.spherePrior N).prod (Model.spherePrior N)
  let R := gaussianRadiusLaw N (1+d)
  let tail := gaussianTailMass N (1+d)
  let C := Real.exp (-(N : ℝ)*L*u+(N : ℝ)*L*eta)
  let S := CoupledGaussianKernelProofs.signedPairWindow N u eta
  have hS : MeasurableSet S := (CoupledGaussianKernelProofs.isOpen_signedPairWindow N u eta).measurableSet
  have htailp : 0 < tail.toReal := (ChiSquareTailProofs.chiSquare_tail_lower hN (by linarith : 1 ≤ 1+d)).1
  have htailne : tail ≠ 0 := by intro hz; simp only [hz,ENNReal.toReal_zero,lt_self_iff_false] at htailp
  have hcap : tail⁻¹*tail⁻¹ ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr htailne) (ENNReal.inv_ne_top.mpr htailne)
  obtain ⟨ν,hν,hi,hSq,hm,hdom⟩ := exists_gaussian_retained_radius hN (by linarith : 1 ≤ 1+d)
  have : IsProbabilityMeasure ν := hν
  have hdprod := retained_pair_domination ν hdom
  have hiR := radialPairWeight_integrable hN ha hd hL hP g
  have hiν : Integrable (fun p ↦ radialPairWeight N a d L g p.1 p.2) (μ.prod (ν.prod ν)) :=
    hiR.of_measure_le_smul hcap hdprod
  have hdomint : (∫ p,radialPairWeight N a d L g p.1 p.2 ∂μ.prod (ν.prod ν)) ≤
      tail.toReal⁻¹*tail.toReal⁻¹*CoupledGaussianIntegralProofs.endpointMoment N a d L g := by
    have H := integral_mono_measure hdprod
      (Eventually.of_forall (fun p ↦ (Real.exp_pos _).le)) (hiR.smul_measure hcap)
    rw [integral_smul_measure,ENNReal.toReal_mul,ENNReal.toReal_inv,smul_eq_mul] at H
    change (∫ p,radialPairWeight N a d L g p.1 p.2 ∂μ.prod (ν.prod ν)) ≤
      tail.toReal⁻¹*tail.toReal⁻¹*(∫ p,radialPairWeight N a d L g p.1 p.2 ∂μ.prod (R.prod R)) at H
    rw [radialPairWeight_integral hN ha hd hL hP g] at H
    exact H
  have hB := commonWeight_integrable hN a g
  have hleft : Integrable (fun xy : Model.Vector N × Model.Vector N ↦
      Real.exp ((N : ℝ)*(d-a))*S.indicator
        (fun xy ↦ Real.exp (Real.sqrt ((N : ℝ)*a)*inner ℝ (xy.1+xy.2) g)) xy) μ :=
    (hB.indicator hS).const_mul _
  have hright : Integrable (fun xy ↦ C*∫ rs,radialPairWeight N a d L g xy rs ∂ν.prod ν) μ :=
    hiν.integral_prod_left.const_mul C
  have hAE : ∀ᵐ xy ∂μ, Real.exp ((N : ℝ)*(d-a))*S.indicator
        (fun xy ↦ Real.exp (Real.sqrt ((N : ℝ)*a)*inner ℝ (xy.1+xy.2) g)) xy ≤
      C*∫ rs,radialPairWeight N a d L g xy rs ∂ν.prod ν := by
    filter_upwards [spherePair_norm_ae hN,hiν.prod_right_ae] with xy hxy hiexp
    by_cases hmem : xy ∈ S
    · rw [Set.indicator_of_mem hmem]
      have hJ := radial_jensen ν hi hSq hm
        (Real.sqrt ((N : ℝ)*a)*inner ℝ xy.1 g)
        (Real.sqrt ((N : ℝ)*a)*inner ℝ xy.2 g) ((N : ℝ)*L*inner ℝ xy.1 xy.2)
        (show 0 ≤ (N : ℝ)*(d-a)/2 by positivity) hiexp
      have hr : u-eta < inner ℝ xy.1 xy.2 := by
        change |inner ℝ xy.1 xy.2-u| < eta at hmem
        linarith [(abs_lt.mp hmem).1]
      have hpos : 0 ≤ (N : ℝ)*L*(inner ℝ xy.1 xy.2-u+eta) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hL) (by linarith)
      have hstep : Real.exp ((N : ℝ)*(d-a))*
          Real.exp (Real.sqrt ((N : ℝ)*a)*inner ℝ (xy.1+xy.2) g) ≤
          C*Real.exp (Real.sqrt ((N : ℝ)*a)*inner ℝ xy.1 g+
            Real.sqrt ((N : ℝ)*a)*inner ℝ xy.2 g+
              (N : ℝ)*L*inner ℝ xy.1 xy.2+2*((N : ℝ)*(d-a)/2)) := by
        unfold C
        rw [← Real.exp_add,← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [inner_add_left]
        nlinarith only [hpos]
      exact hstep.trans (mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le)
    · rw [Set.indicator_of_notMem hmem,mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun rs ↦ (Real.exp_pos _).le))
  have H := integral_mono_ae hleft hright hAE
  rw [integral_const_mul,integral_indicator hS,integral_const_mul,
    ← integral_prod (fun p ↦ radialPairWeight N a d L g p.1 p.2) hiν] at H
  change Real.exp ((N : ℝ)*(d-a))*signedCommonPartition N a u eta g ≤
    C*(∫ p,radialPairWeight N a d L g p.1 p.2 ∂μ.prod (ν.prod ν)) at H
  calc
    _ ≤ C*(∫ p,radialPairWeight N a d L g p.1 p.2 ∂μ.prod (ν.prod ν)) := H
    _ ≤ C*(tail.toReal⁻¹*tail.toReal⁻¹*CoupledGaussianIntegralProofs.endpointMoment N a d L g) :=
      mul_le_mul_of_nonneg_left hdomint (Real.exp_pos _).le
    _ = _ := by dsimp [C,tail]; ring

end
end TensorPCA.CoupledRadialEndpointProofs
