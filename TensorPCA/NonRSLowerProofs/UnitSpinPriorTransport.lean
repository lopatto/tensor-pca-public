-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.SphericalSelectedPerturbationKernel
public import TensorPCA.NonRSUpperProofs.GaussianSpinKernels
public import Mathlib.MeasureTheory.Measure.Tilted

/-! Exact transport of genuinely unit-supported ambient priors to the
standard intrinsic unit-spin subtype. No off-sphere choice map is used. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.UnitSpinPriorTransport
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open RetainedCountProofs.FiniteModel GaussianSpinInterpolation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem unit_set_measurable (N : ℕ) : MeasurableSet {x : Vector N | ‖x‖=1} :=
  (isClosed_eq continuous_norm continuous_const).measurableSet

def prior {N : ℕ} (nu : Measure (Vector N)) : Measure (UnitSpin N) :=
  nu.comap ((↑) : UnitSpin N → Vector N)

theorem prior_probability {N : ℕ} (nu : Measure (Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐ x ∂nu, ‖x‖=1) : IsProbabilityMeasure (prior nu) := by
  apply (MeasurableEmbedding.subtype_coe (unit_set_measurable N)).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe,Set.mem_setOf_eq] using hnu

theorem map_prior {N : ℕ} (nu : Measure (Vector N)) (hnu : ∀ᵐ x ∂nu, ‖x‖=1) :
    (prior nu).map ((↑) : UnitSpin N → Vector N)=nu := by
  exact (map_comap_subtype_coe (unit_set_measurable N) nu).trans
    (Measure.restrict_eq_self_of_ae_mem hnu)

theorem integral_prior {N : ℕ} (nu : Measure (Vector N)) (hnu : ∀ᵐ x ∂nu, ‖x‖=1)
    (f : Vector N → ℝ) : (∫ z : UnitSpin N, f z.val ∂prior nu)=∫ x, f x ∂nu := by
  have hmp : MeasurePreserving ((↑) : UnitSpin N → Vector N) (prior nu) nu :=
    ⟨measurable_subtype_coe,map_prior nu hnu⟩
  exact hmp.integral_comp (MeasurableEmbedding.subtype_coe (unit_set_measurable N)) f

theorem map_tilted_prior {N : ℕ} (nu : Measure (Vector N)) (hnu : ∀ᵐ x ∂nu, ‖x‖=1)
    (f : Vector N → ℝ) (hf : Measurable f) :
    ((prior nu).tilted (fun z : UnitSpin N ↦ f z.val)).map ((↑) : UnitSpin N → Vector N)=nu.tilted f := by
  have hZ := integral_prior nu hnu (fun x ↦ Real.exp (f x))
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs,tilted_apply' _ _ (measurable_subtype_coe hs),tilted_apply' _ _ hs,hZ]
  have H := setLIntegral_map (μ := prior nu) hs
    ((hf.exp.div_const (∫ x, Real.exp (f x) ∂nu)).ennreal_ofReal) measurable_subtype_coe
  rw [map_prior nu hnu] at H
  exact H.symm

private theorem gibbsMeasure_eq_tilted {V H : Type*} [MeasurableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (nu : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) :
    gibbsMeasure nu L w=nu.tilted (fun x ↦ L x w) := by
  simp only [gibbsMeasure,Measure.tilted,GaussianSpinInterpolation.moment,weight,one_mul]

theorem map_gibbs_prior {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (nu : Measure (Vector N)) (hnu : ∀ᵐ x ∂nu, ‖x‖=1)
    (L : Vector N → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    (gibbsMeasure (prior nu) (fun z : UnitSpin N ↦ L z.val) w).map ((↑) : UnitSpin N → Vector N)=
      gibbsMeasure nu L w := by
  simp_rw [gibbsMeasure_eq_tilted]
  exact map_tilted_prior nu hnu (fun x ↦ L x w)
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL)

theorem integral_gibbs_prior {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (nu : Measure (Vector N)) (hnu : ∀ᵐ x ∂nu, ‖x‖=1)
    (L : Vector N → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) (f : Vector N → ℝ) :
    (∫ z : UnitSpin N, f z.val ∂gibbsMeasure (prior nu) (fun z : UnitSpin N ↦ L z.val) w)=
      ∫ x, f x ∂gibbsMeasure nu L w := by
  have hmp : MeasurePreserving ((↑) : UnitSpin N → Vector N)
      (gibbsMeasure (prior nu) (fun z : UnitSpin N ↦ L z.val) w) (gibbsMeasure nu L w) :=
    ⟨measurable_subtype_coe,map_gibbs_prior nu hnu L hL w⟩
  exact hmp.integral_comp (MeasurableEmbedding.subtype_coe (unit_set_measurable N)) f

/-- Standard output pullback of an ambient kernel. Its parameter measurability is
provided by Mathlib's comapRight construction.
-/
def priorKernel {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (G : Kernel Ω (Vector N)) :
    Kernel Ω (UnitSpin N) := G.comapRight (MeasurableEmbedding.subtype_coe (unit_set_measurable N))

theorem priorKernel_apply {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (G : Kernel Ω (Vector N)) (w : Ω) : priorKernel G w=prior (G w) := rfl

theorem priorKernel_markov {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (G : Kernel Ω (Vector N)) [IsMarkovKernel G] (hG : ∀ w, ∀ᵐ x ∂G w, ‖x‖=1) :
    IsMarkovKernel (priorKernel G) := ⟨fun w ↦ prior_probability (G w) (hG w)⟩

theorem priorKernel_measurable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (G : Kernel Ω (Vector N)) : Measurable (fun w ↦ priorKernel G w) := (priorKernel G).measurable

theorem map_priorKernel {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (G : Kernel Ω (Vector N)) (hG : ∀ w, ∀ᵐ x ∂G w, ‖x‖=1) :
    (priorKernel G).map ((↑) : UnitSpin N → Vector N)=G := by
  apply Kernel.ext
  intro w
  rw [Kernel.map_apply _ measurable_subtype_coe,priorKernel_apply,map_prior (G w) (hG w)]

end
end TensorPCA.NonRSLowerProofs.UnitSpinPriorTransport
