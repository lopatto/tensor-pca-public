-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingEmpirical
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorIntegrability

/-! Spherical numerator clipping, uniformly in bulk dimension, unit-supported
probability prior and positive iid sample cutoff. The Gaussian mark is shared across
the iid spin samples.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.NumeratorMarkClippingTheorems
open MeasureTheory ProbabilityTheory Set
open GGFiniteEmpiricalNormalizer NumeratorMarkClippingMeasure NumeratorMarkClippingEmpirical
open FiniteCavityNumeratorMoments
noncomputable section

theorem numerator_mean_clip_tail_le {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) {L : ℝ} (hL : 1≤L) :
    let P := (stdGaussian (CavityDisorder N M k)).prod nu
    Integrable (fun p : CavityDisorder N M k×Model.Vector N =>
      numeratorMark k mu beta p.1 p.2-min (numeratorMark k mu beta p.1 p.2) L) P ∧
      0≤(∫p,numeratorMark k mu beta p.1 p.2-min (numeratorMark k mu beta p.1 p.2) L ∂P) ∧
      (∫p,numeratorMark k mu beta p.1 p.2-min (numeratorMark k mu beta p.1 p.2) L ∂P)≤
        Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)/L := by
  dsimp only
  have H := clip_tail_integrable_and_bound ((stdGaussian (CavityDisorder N M k)).prod nu)
    (numeratorMark_joint_measurable N M k mu beta)
    (Filter.Eventually.of_forall (fun p => numeratorMark_one_le hM k mu beta p.1 p.2))
    (numeratorMark_joint_sq_integrable hM k hmu beta nu hnu) hL
  exact ⟨H.1,H.2.1,H.2.2.trans (div_le_div_of_nonneg_right
    (numeratorMark_joint_second_moment hM k hmu beta nu hnu) (zero_le_one.trans hL))⟩

theorem numerator_empirical_log_clip_error_le {N M K : ℕ} (hM : 0<M) (hK : 0<K)
    (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) {L : ℝ} (hL : 1≤L) :
    let P := (stdGaussian (CavityDisorder N M k)).prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun p : CavityDisorder N M k×(Fin K→Model.Vector N) => empiricalMean K (numeratorMark k mu beta p.1) p.2
    let C := fun p : CavityDisorder N M k×(Fin K→Model.Vector N) =>
      empiricalMean K (fun x => min (numeratorMark k mu beta p.1 x) L) p.2
    Integrable (fun p => Real.log (A p)) P ∧ Integrable (fun p => Real.log (C p)) P ∧
      0≤(∫p,Real.log (A p) ∂P)-(∫p,Real.log (C p) ∂P) ∧
      (∫p,Real.log (A p) ∂P)-(∫p,Real.log (C p) ∂P)≤
        Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)/L := by
  dsimp only
  have H := empirical_log_clip_error_le hK (stdGaussian (CavityDisorder N M k)) nu
    (numeratorMark_joint_measurable N M k mu beta)
    (Filter.Eventually.of_forall (fun p => numeratorMark_one_le hM k mu beta p.1 p.2))
    (numeratorMark_joint_sq_integrable hM k hmu beta nu hnu) hL
  dsimp only at H
  exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.trans (div_le_div_of_nonneg_right
    (numeratorMark_joint_second_moment hM k hmu beta nu hnu) (zero_le_one.trans hL))⟩

theorem numerator_normalized_empirical_power_clip_error_le {N M K : ℕ} (hM : 0<M) (hK : 0<K)
    (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) {L r : ℝ} (hL : 1≤L) (hr0 : 0<r) (hr1 : r≤1) :
    let P := (stdGaussian (CavityDisorder N M k)).prod (Measure.pi (fun _ : Fin K => nu))
    let A := fun p : CavityDisorder N M k×(Fin K→Model.Vector N) => empiricalMean K (numeratorMark k mu beta p.1) p.2
    let C := fun p : CavityDisorder N M k×(Fin K→Model.Vector N) =>
      empiricalMean K (fun x => min (numeratorMark k mu beta p.1 x) L) p.2
    Integrable (fun p => (A p)^r) P ∧ Integrable (fun p => (C p)^r) P ∧
      0≤((∫p,(A p)^r ∂P)-(∫p,(C p)^r ∂P))/r ∧
      ((∫p,(A p)^r ∂P)-(∫p,(C p)^r ∂P))/r≤
        Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)/L := by
  dsimp only
  have HF := numeratorMark_joint_measurable N M k mu beta
  have H1 : ∀ᵐp : CavityDisorder N M k×Model.Vector N∂(stdGaussian (CavityDisorder N M k)).prod nu,
      1≤numeratorMark k mu beta p.1 p.2 :=
    Filter.Eventually.of_forall (fun p => numeratorMark_one_le hM k mu beta p.1 p.2)
  have H2 := numeratorMark_joint_sq_integrable hM k hmu beta nu hnu
  have HI := empirical_power_clip_error_le hK (stdGaussian (CavityDisorder N M k)) nu HF H1 H2 hL hr0.le hr1
  have H := normalized_empirical_power_clip_error_le hK (stdGaussian (CavityDisorder N M k)) nu HF H1 H2 hL hr0 hr1
  dsimp only at HI H
  exact ⟨HI.1,HI.2.1,H.1,H.2.trans (div_le_div_of_nonneg_right
    (numeratorMark_joint_second_moment hM k hmu beta nu hnu) (zero_le_one.trans hL))⟩

theorem exists_numerator_clipping_cutoff (M k : ℕ) (mu beta : ℝ) {eta : ℝ} (heta : 0<eta) :
    ∃L : ℝ,1≤L ∧ Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)/L≤eta := by
  let B := Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)
  have hB : 0<B := Real.exp_pos _
  have hratio : 0<B/eta := div_pos hB heta
  refine ⟨1+B/eta,by linarith only [hratio],?_⟩
  change B/(1+B/eta)≤eta
  rw [div_le_iff₀ (by linarith only [hratio] : (0 : ℝ)<1+B/eta)]
  have H : eta*(B/eta)=B := by field_simp
  nlinarith only [H,heta]

end
end TensorPCA.NonRSLowerProofs.NumeratorMarkClippingTheorems
