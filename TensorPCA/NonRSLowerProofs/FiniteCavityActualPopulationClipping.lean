-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPopulationClippedMeans
public import TensorPCA.NonRSLowerProofs.FiniteCavityObservedFunctionalAveraging

/-! Fixed-bulk observed population means in the product-law order used by finite GG and
ASS. Per-prior expected-log comparisons are averaged before the final bulk-disorder
integration.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityActualPopulationClipping
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation GaussianCompactFeatureComparison
open FiniteCavityNumeratorMoments FiniteCavityGaussianCompatibility FiniteCavityPerturbedFields
open FiniteCavityPopulationClippedMeans FiniteCavityObservedFunctionalAveraging
open FiniteCavityCompensationThetaComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Actual
variable {N M k K : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ} (beta v : ℝ)
  (gB : GroundState.Disorder N k)
local notation "Omega" => (Fin K→ℝ)×PerturbationDisorder N K
local notation "d" => Measure.prod (positiveCubeLaw K) (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
local notation "F" => limitingCompensatorFeature (N := N) M (fun j : Fin k => (j : ℕ)+1)
  (fun j => beta^2*VariationalProofs.sliceCoefficient k mu j)
include hN hM

theorem actual_clipped_means_facts {LN b cap : ℝ} (hLN : 1≤LN) (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap) :
    let AN := fun p : Omega×CavityDisorder N M k => ∫x,min (numeratorMark k mu beta p.2 x) LN ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
    let AC := fun p : Omega×GroundState.Disorder N k => ∫x,max b (min (Real.exp (inner ℝ (F x) p.2)) cap) ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
    Measurable AN ∧ (∀p,1≤AN p ∧ AN p≤LN) ∧ Measurable AC ∧ (∀p,b≤AC p ∧ AC p≤cap) := by
  have hYN : Measurable (fun p : CavityDisorder N M k×Model.Vector N => min (numeratorMark k mu beta p.1 p.2) LN) :=
    (numeratorMark_joint_measurable N M k mu beta).min measurable_const
  have hYC : Measurable (fun p : GroundState.Disorder N k×Model.Vector N => max b (min (Real.exp (inner ℝ (F p.2) p.1)) cap)) := by
    have hF := (thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable
    exact measurable_const.max ((FiniteCavityCompensatorGaussianMoments.expMark_joint_measurable hF).min measurable_const)
  refine ⟨actual_population_mean_measurable hN M k K mu beta v gB _ hYN,?_,
    actual_population_mean_measurable hN M k K mu beta v gB _ hYC,?_⟩
  · intro p
    letI := perturbedBulkGibbs_probability hN M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))
    exact numerator_clipped_mean_bounds hM k mu beta ((perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))) hLN p.2
  · intro p
    letI := perturbedBulkGibbs_probability hN M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))
    exact compensation_clipped_mean_bounds (N := N) (M := M) (k := k) (mu := mu) beta ((perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))) hb hb1 hc p.2

theorem actual_population_clipping_control (hmu : mu∈Icc (-1 : ℝ) 1)
    {LN b cap : ℝ} (hLN : 1≤LN) (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap) :
    let RN := fun p : Omega×CavityDisorder N M k => Real.log (∫x,numeratorMark k mu beta p.2 x ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
    let CN := fun p : Omega×CavityDisorder N M k => Real.log (∫x,min (numeratorMark k mu beta p.2 x) LN ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
    let RC := fun p : Omega×GroundState.Disorder N k => Real.log (∫x,Real.exp (inner ℝ (F x) p.2) ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
    let CC := fun p : Omega×GroundState.Disorder N k => Real.log (∫x,max b (min (Real.exp (inner ℝ (F x) p.2)) cap) ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
    Integrable RN ((d).prod (stdGaussian (CavityDisorder N M k))) ∧
    Integrable CN ((d).prod (stdGaussian (CavityDisorder N M k))) ∧
    Integrable RC ((d).prod (stdGaussian (GroundState.Disorder N k))) ∧
    Integrable CC ((d).prod (stdGaussian (GroundState.Disorder N k))) ∧
    0≤(∫p,RN p ∂(d).prod (stdGaussian (CavityDisorder N M k)))-(∫p,CN p ∂(d).prod (stdGaussian (CavityDisorder N M k))) ∧
    (∫p,RC p ∂(d).prod (stdGaussian (GroundState.Disorder N k)))-(∫p,CC p ∂(d).prod (stdGaussian (GroundState.Disorder N k)))≤
      2*Real.exp (9*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1))/2)/cap+
        2*b*Real.exp (2*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1))) := by
  let RN := fun p : Omega×CavityDisorder N M k => Real.log (∫x,numeratorMark k mu beta p.2 x ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
  let CN := fun p : Omega×CavityDisorder N M k => Real.log (∫x,min (numeratorMark k mu beta p.2 x) LN ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
  let RC := fun p : Omega×GroundState.Disorder N k => Real.log (∫x,Real.exp (inner ℝ (F x) p.2) ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
  let CC := fun p : Omega×GroundState.Disorder N k => Real.log (∫x,max b (min (Real.exp (inner ℝ (F x) p.2)) cap) ∂(perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
  obtain ⟨hAN,hBN,hAC,hBC⟩ := actual_clipped_means_facts hN hM beta v gB hLN hb hb1 hc
  obtain ⟨hiRN,hiRC⟩ := fixed_bulk_raw_logs_integrable (N := N) (M := M) (k := k) (K := K) hN hM hmu beta v gB
  have hiCN : Integrable CN ((d).prod (stdGaussian (CavityDisorder N M k))) := by
    apply Integrable.of_bound hAN.log.aestronglyMeasurable (|Real.log LN|)
    exact ae_of_all _ (fun p => by
      have H := hBN p
      have h0 := Real.log_nonneg H.1
      have h1 := Real.log_le_log (zero_lt_one.trans_le H.1) H.2
      rw [Real.norm_eq_abs,abs_of_nonneg h0]
      exact h1.trans (le_abs_self _))
  have hiCC : Integrable CC ((d).prod (stdGaussian (GroundState.Disorder N k))) := by
    apply Integrable.of_bound hAC.log.aestronglyMeasurable (|Real.log b|+|Real.log cap|)
    exact ae_of_all _ (fun p => by
      have H := hBC p
      have hlo := Real.log_le_log hb H.1
      have hhi := Real.log_le_log (hb.trans_le H.1) H.2
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le (Real.log b),le_abs_self (Real.log cap),abs_nonneg (Real.log b),abs_nonneg (Real.log cap)])
  have hNum : (∫p,CN p ∂(d).prod (stdGaussian (CavityDisorder N M k)))≤
      ∫p,RN p ∂(d).prod (stdGaussian (CavityDisorder N M k)) := by
    have H := integral_mono hiCN.integral_prod_left hiRN.integral_prod_left (fun p => by
      letI := perturbedBulkGibbs_probability hN M k K mu beta v p.1 (sumJoin (gB,p.2))
      have hUnit : ∀ᵐx∂(perturbedBulkGibbs N M k K mu beta v p.1 (sumJoin (gB,p.2))),x∈Model.unitSphere N := perturbedBulkGibbs_unit_ae hN M k K mu beta v p.1 (sumJoin (gB,p.2))
      have HC := numerator_population_log_clipping hM k hmu beta ((perturbedBulkGibbs N M k K mu beta v p.1 (sumJoin (gB,p.2)))) hUnit hLN
      exact sub_nonneg.mp HC.2.2.1)
    rw [←integral_prod CN hiCN,←integral_prod RN hiRN] at H
    exact H
  let W := 2*Real.exp (9*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1))/2)/cap+
    2*b*Real.exp (2*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1)))
  have hComp : (∫p,RC p ∂(d).prod (stdGaussian (GroundState.Disorder N k)))-
      (∫p,CC p ∂(d).prod (stdGaussian (GroundState.Disorder N k)))≤W := by
    have H := integral_mono (hiRC.integral_prod_left.sub hiCC.integral_prod_left) (integrable_const W) (fun p => by
      letI := perturbedBulkGibbs_probability hN M k K mu beta v p.1 (sumJoin (gB,p.2))
      have hUnit : ∀ᵐx∂(perturbedBulkGibbs N M k K mu beta v p.1 (sumJoin (gB,p.2))),x∈Model.unitSphere N := perturbedBulkGibbs_unit_ae hN M k K mu beta v p.1 (sumJoin (gB,p.2))
      have HC := compensation_population_log_clipping (N := N) (M := M) (k := k) (mu := mu) beta hN hmu ((perturbedBulkGibbs N M k K mu beta v p.1 (sumJoin (gB,p.2)))) hUnit hb hb1 hc
      exact (abs_le.mp HC.2.2).2)
    simp only [Pi.sub_apply,integral_const,probReal_univ,one_smul] at H
    rw [integral_sub hiRC.integral_prod_left hiCC.integral_prod_left,
      ←integral_prod RC hiRC,←integral_prod CC hiCC] at H
    exact H
  exact ⟨hiRN,hiCN,hiRC,hiCC,sub_nonneg.mpr hNum,hComp⟩
end Actual

end
end TensorPCA.NonRSLowerProofs.FiniteCavityActualPopulationClipping
