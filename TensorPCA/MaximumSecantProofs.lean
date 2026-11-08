-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import TensorPCA.CheckedReduction

/-! Finite maximum secants for arbitrary measurable randomized MLEs.
The event is at one fixed strength and may be shared over all deterministic steps. -/

@[expose] public section
namespace TensorPCA.MaximumSecantProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

theorem normalizedMaximum_eq_score_of_maximizer {N k : ℕ}
    (y : Model.Tensor N k) (v : Model.Vector N) (hv : v ∈ Model.unitSphere N)
    (hmax : ∀ z ∈ Model.unitSphere N, Model.score y z ≤ Model.score y v) :
    Model.normalizedMaximum y = Model.score y v/Real.sqrt N := by
  unfold Model.normalizedMaximum
  rw [(show IsGreatest (Model.score y '' Model.unitSphere N) (Model.score y v) from
    ⟨mem_image_of_mem _ hv, by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz⟩).csSup_eq]

theorem maximum_subgradient {N k : ℕ} (hN : 0 < N) (a b : ℝ)
    (z : Model.Vector N × Model.Tensor N k) (v : Model.Vector N)
    (hv : v ∈ Model.unitSphere N)
    (hmax : ∀ x ∈ Model.unitSphere N,
      Model.score (Model.observation a z) x ≤ Model.score (Model.observation a z) v) :
    Model.normalizedMaximum (Model.observation a z)+(b-a)*(inner ℝ v z.1)^k ≤
      Model.normalizedMaximum (Model.observation b z) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [normalizedMaximum_eq_score_of_maximizer _ _ hv hmax]
  have halg : Model.score (Model.observation a z) v/Real.sqrt N+(b-a)*(inner ℝ v z.1)^k =
      Model.score (Model.observation b z) v/Real.sqrt N := by
    simp only [Model.score, Model.observation, inner_add_right, inner_smul_right,
      Geometry.feature_inner]
    field_simp [hs.ne']
    ring
  rw [halg]
  exact div_le_div_of_nonneg_right
    (le_csSup (Geometry.score_image_bddAbove _) (mem_image_of_mem _ hv)) hs.le

theorem maximum_secants {N k : ℕ} (hN : 0 < N) (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (z : Model.Vector N × Model.Tensor N k) (v : Model.Vector N)
    (hv : v ∈ Model.unitSphere N)
    (hmax : ∀ x ∈ Model.unitSphere N,
      Model.score (Model.observation lam z) x ≤ Model.score (Model.observation lam z) v) :
    (Model.normalizedMaximum (Model.observation lam z)-
      Model.normalizedMaximum (Model.observation (lam-h) z))/h ≤ (inner ℝ v z.1)^k ∧
      (inner ℝ v z.1)^k ≤ (Model.normalizedMaximum (Model.observation (lam+h) z)-
        Model.normalizedMaximum (Model.observation lam z))/h := by
  constructor
  · apply (div_le_iff₀ hh).mpr
    have H := maximum_subgradient hN lam (lam-h) z v hv hmax
    nlinarith
  · apply (le_div_iff₀ hh).mpr
    have H := maximum_subgradient hN lam (lam+h) z v hv hmax
    nlinarith

theorem ae_maximum_secants {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (est : Model.Estimator N k A) (hMLE : Model.IsMLE N k lam est ν) :
    ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ∀ h : ℝ, 0 < h →
      (Model.normalizedMaximum (Model.observation lam z.1)-
        Model.normalizedMaximum (Model.observation (lam-h) z.1))/h ≤
          (inner ℝ (est (Model.observation lam z.1) z.2) z.1.1)^k ∧
      (inner ℝ (est (Model.observation lam z.1) z.2) z.1.1)^k ≤
        (Model.normalizedMaximum (Model.observation (lam+h) z.1)-
          Model.normalizedMaximum (Model.observation lam z.1))/h := by
  have hobs : MeasurePreserving (Model.observation lam)
      (Model.experimentLaw N k) (Model.observationLaw N k lam) :=
    ⟨Model.measurable_observation N k lam, rfl⟩
  have hmp := hobs.prod (MeasurePreserving.id ν)
  filter_upwards [hmp.quasiMeasurePreserving.ae hMLE.2] with z hz
  intro h hh
  exact maximum_secants hN lam hh z.1 (est (Model.observation lam z.1) z.2)
    (hMLE.1.2 _ _) hz


/-- Arbitrary-coupling secant bounds obtained from finite maximizers. Only countably many dimensions are intersected at fixed λ. -/
theorem maximumEnvelopeSecants : CheckedReduction.MaximumEnvelopeSecants.{u,v} := by
  intro k hk lam hlam hnoncritical Ω _ μ _ E A _ ν _ R hPaper
  have hmp (n : ℕ) : MeasurePreserving
      (fun ω ↦ (E.sample n ω, R.auxiliary n ω)) μ
      ((Model.experimentLaw (n+1) k).prod (ν n)) :=
    ⟨(E.measurable n).prodMk (R.measurable n), R.independentLaw n⟩
  have hall := ae_all_iff.mpr (fun n : ℕ ↦
    (hmp n).quasiMeasurePreserving.ae
      (ae_maximum_secants (Nat.succ_pos n) lam (ν n) (R.estimator n) (hPaper.1 n)))
  filter_upwards [hall] with ω hω
  intro j
  apply Filter.Eventually.of_forall
  intro n
  have hh : 0 < LimitTools.secantStep lam j := by
    exact div_pos hlam (by positivity)
  simpa only [Statements.sampleMaximum, Reduction.overlapSlope] using
    hω n (LimitTools.secantStep lam j) hh

end
end TensorPCA.MaximumSecantProofs
