-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalLowDegreeStarBudget
public import TensorPCA.NonRSUpperProofs.SphericalPerturbationPairMass

/-! Positivity for EVERY sufficiently large finite cutoff, on the same
tensor perturbation bank and positive-amplitude cube as the GG bounds.
The finite-error bookkeeping adapts the checked local
NonRSUpperProofs.SphericalUniformPositivity argument (whose immutable
Apache-2.0 provenance is recorded in that source), using the new threshold
uniform in the total cutoff. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalLargeCutoffPositivity
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianGGEnsemble
open NonRSUpperProofs.GaussianGGCutoffs NonRSUpperProofs.GaussianPerturbationDeviation
open RetainedCountProofs.FiniteModel SphericalLowDegreeStarBudget
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_uniform_largeCutoff_perturbation_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K0 : ℕ, ∃ V : ℝ, 0<K0 ∧ 1≤V ∧
      ∀ {N K : ℕ}, K0≤K → ∀ (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
        (v : ℝ), V≤v → (perturbedOverlapLaw (K := K) ν v).real (Iic (-ε))≤η := by
  obtain ⟨n,M,k,C,hn,hM,hC,hFinite⟩ :=
    exists_uniform_finite_power_bound hε hε1 (by positivity : 0<η/2)
  let Q : ℝ := ∑m∈Finset.Ico 1 n, ∑j : Fin M, ∑p∈Finset.range (k+1), (1:ℝ)
  have hQ : 0≤Q := by dsimp [Q];positivity
  let δ : ℝ := η/(2*C*(Q+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have hδeq : 2*C*(Q+1)*δ=η := by
    dsimp [δ]
    field_simp
  obtain ⟨V,hV1,hPower⟩ := exists_uniform_lowDegree_star_threshold (k+1) hδ
  refine ⟨k+1,V,by omega,hV1,?_⟩
  intro N K hK0 ν _ v hV
  have hv : 0<v := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hV1.trans hV)
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := ambientParameterizedGibbsKernel (K := K) ν v
  let _ : IsMarkovKernel G := ambientParameterizedGibbsKernel_markov ν hv.le
  have hG : ∀ᵐ x ∂positiveCubeLaw K, ∀ᵐ w ∂d, ∀ᵐ z ∂G (x,w), ‖z‖≤1 :=
    .of_forall fun x => .of_forall fun w =>
      (ambientParameterizedGibbsKernel_unit_support ν v (x,w)).mono fun z hz => hz.le
  have hFin := hFinite (Fin K → ℝ) (PerturbationDisorder N K) (Vector N)
    (positiveCubeLaw K) d G hG
  have hEach (m : ℕ) (j : Fin M) (p : ℕ) (hp : p∈Finset.range (k+1)) :
      cubeMeanPowerDefect (K := K) ν v (-leftEndpoint ε M j) m p≤δ := by
    by_cases hp0 : p=0
    · subst p
      rw [cubeMeanPowerDefect_zero_degree ν hv.le]
      exact hδ.le
    · let q : Fin K := ⟨p-1,by have := Finset.mem_range.mp hp;omega⟩
      have hq : q.val+1=p := by dsimp [q];omega
      simpa only [hq] using hPower ν v hV q (by rw [hq]; have hp1 := Finset.mem_range.mp hp; omega) (-leftEndpoint ε M j) m
  have hErr : finitePowerError (positiveCubeLaw K) d G ε n M k≤Q*δ := by
    unfold finitePowerError
    calc
      _ ≤ ∑m∈Finset.Ico 1 n, ∑j : Fin M, ∑p∈Finset.range (k+1), δ := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro p hp
        exact hEach m j p hp
      _ = Q*δ := by dsimp [Q];simp only [Finset.sum_mul,one_mul]
  have hsmall : C*(Q*δ)≤η/2 := by
    have hnon : 0≤C*δ := by positivity
    nlinarith [hδeq]
  rw [perturbedOverlapLaw_negative_mass ν hv.le]
  change (∫x,starMass d (G.sectR x) ε 1 ∂positiveCubeLaw K)≤η
  calc
    _ ≤ η/2+C*finitePowerError (positiveCubeLaw K) d G ε n M k := hFin
    _ ≤ η/2+C*(Q*δ) := add_le_add (le_refl (η/2)) (mul_le_mul_of_nonneg_left hErr hC.le)
    _ ≤ η := by linarith

theorem exists_uniform_largeCutoff_gibbs_pair_positivity {eps eta : ℝ}
    (heps : 0<eps) (heps1 : eps≤1) (heta : 0<eta) :
    ∃ K0 : ℕ, ∃ V : ℝ, 0<K0 ∧ 1≤V ∧ ∀ {N K : ℕ}, K0≤K →
      ∀ (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ), V≤v →
        (∫ x, ∫ w, ((GaussianSpinInterpolation.gibbsMeasure nu (unitLinear (coefficients v x)) w).prod
          (GaussianSpinInterpolation.gibbsMeasure nu (unitLinear (coefficients v x)) w)).real
          {z : UnitSpin N×UnitSpin N | inner ℝ z.1.val z.2.val≤-eps}
          ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K)≤eta := by
  obtain ⟨K0,V,hK0,hV,hPos⟩ := exists_uniform_largeCutoff_perturbation_positivity heps heps1 heta
  refine ⟨K0,V,hK0,hV,?_⟩
  intro N K hK nu _ v hv
  have hvnon : 0≤v := le_trans (by norm_num : (0 : ℝ)≤1) (hV.trans hv)
  have heq := perturbedOverlapLaw_mass_eq_gibbs_pair_integral (K := K) nu hvnon (Iic (-eps)) measurableSet_Iic
  exact heq.symm.trans_le (hPos hK nu v hv)

end
end TensorPCA.NonRSLowerProofs.SphericalLargeCutoffPositivity
