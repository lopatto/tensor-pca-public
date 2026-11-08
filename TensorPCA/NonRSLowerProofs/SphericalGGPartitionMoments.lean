-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGUniformInvariance
public import TensorPCA.NonRSLowerProofs.GGFiniteReplicaWeightMoments

/-! Finite partition-weight monomials from added zero-test iid replicas. Each weight
test sees the same original anchor block. Uniform thresholds precede dimensions,
priors and the bounded measurable tests.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGPartitionMoments
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation NonRSUpperProofs.GaussianReplicaKernel
open GGFiniteFirstJet GGFiniteReweightingDerivative GGFiniteReweightingJets
open GGFiniteReplicaWeightMoments SphericalGGJetFamily SphericalGGZeroJets SphericalGGUniformInvariance
open scoped BigOperators
noncomputable section

theorem momentLift_joint_measurable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    (n m : ℕ) {Phi : X → (Fin (n+1) → V) → ℝ}
    (hPhi : Measurable (fun p : X×(Fin (n+1) → V) ↦ Phi p.1 p.2))
    (b : X → Fin m → (((Fin (n+1) → V)×V) → ℝ))
    (hb : ∀ i, Measurable (fun p : X×((Fin (n+1) → V)×V) ↦ b p.1 i p.2)) :
    Measurable (fun p : X×(Fin (n+m+1) → V) ↦ momentLift n (Phi p.1) m (b p.1) p.2) := by
  induction m with
  | zero => exact hPhi
  | succ m ih =>
    have HI := ih (fun x ↦ Fin.init (b x)) (fun i ↦ hb i.castSucc)
    have H0 : Measurable (fun p : X×(Fin (n+(m+1)+1) → V) ↦
        momentLift n (Phi p.1) m (Fin.init (b p.1)) (initial p.2)) := by
      convert HI.comp (measurable_fst.prodMk ((initial_measurable _).comp measurable_snd)) using 1 <;> rfl
    have H1 : Measurable (fun p : X×(Fin (n+(m+1)+1) → V) ↦
        b p.1 (Fin.last m) (basePrefix n m (initial p.2),p.2 (Fin.last (n+m+1)))) := by
      convert (hb (Fin.last m)).comp (measurable_fst.prodMk
        ((((basePrefix_measurable n m).comp (initial_measurable _)).comp measurable_snd).prodMk
          ((measurable_pi_apply _).comp measurable_snd))) using 1 <;> rfl
    convert H0.mul H1 using 1
    rfl

theorem tests_padZero (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ) :
    tests (padZero n P m)=padZero n (tests P) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change tests (Fin.snoc (padZero n P m) 0)=Fin.snoc (padZero n (tests P) m) 0
    rw [tests_snoc_zero,ih]
    rfl

theorem pairMean_padZero {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n m : ℕ) (psi : Fin (n+1) → ℝ → ℝ) (x : Fin K → ℝ) :
    (fun j ↦ pairMean nu v (padZero n psi m j) x)=padZero n (fun j ↦ pairMean nu v (psi j) x) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (fun j : Fin ((n+m)+2) ↦ pairMean nu v
      ((Fin.snoc (padZero n psi m) (fun _ : ℝ ↦ 0) : Fin ((n+m)+2) → ℝ → ℝ) j) x)=
      Fin.snoc (padZero n (fun j ↦ pairMean nu v (psi j) x) m) 0
    rw [pairMean_snoc_zero,ih]

theorem padZero_degree_le (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ) {K : ℕ}
    (hP : ∀ j, (P j).natDegree≤K) : ∀ j, (padZero n P m j).natDegree≤K := by
  induction m with
  | zero => exact hP
  | succ m ih =>
    intro j
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · simp only [padZero,Fin.snoc_last,Polynomial.natDegree_zero]; exact Nat.zero_le _
    · simpa only [padZero,Fin.snoc_castSucc] using ih l

def partitionMoment {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (b : (Fin K → ℝ) → Fin m → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (x : Fin K → ℝ) (t : ℝ) : ℝ :=
  let G := (parameterizedGibbsKernel nu v).sectR x
  ∫ w, (∫ old : Fin (n+1) → UnitSpin N,
    (Phi x old*Real.exp (t*(∑ l, correctedScore n unitOverlap (tests P)
      (fun j ↦ pairMean nu v (tests P j) x) old l))/
      (reweightingNormalizer n G unitOverlap (tests P) t w old)^(n+1))*
        (∏ i, tiltedWeightMean n G unitOverlap (tests P) (b x i) t w old)
    ∂Measure.pi (fun _ : Fin (n+1) ↦ G w))
    ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)

theorem lifted_jet_eq_partitionMoment {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : ∀ x, Measurable (Phi x)) {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (b : (Fin K → ℝ) → Fin m → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (hbM : ∀ x i, Measurable (b x i)) (hbb : ∀ x i p, |b x i p|≤1) (x : Fin K → ℝ) (t : ℝ) :
    polynomialJet nu v 0 (n+m) (padZero n P m)
      (fun x ↦ momentLift n (Phi x) m (b x)) x t=partitionMoment nu v n m P Phi b x t := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  simp only [polynomialJet,jet,reweightingJet,tests_padZero,pairMean_padZero]
  exact finite_weight_identity _ _ n m (SphericalFirstJetPowerBudget.unitOverlap_measurable N)
    (tests_measurable P) (fun j ↦ pairMean nu v (tests P j) x) (testBounds P) (tests_bound P)
      (fun j ↦ pairMean_abs_le nu hv (tests_bound P j) x) (hPhi x) hC (hp x) (b x) (hbM x) (hbb x) t

theorem partitionMoment_zero {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ)
    (b : (Fin K → ℝ) → Fin m → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (x : Fin K → ℝ) :
    partitionMoment nu v n m P Phi b x 0=
      let G := (parameterizedGibbsKernel nu v).sectR x
      ∫ w, (∫ old : Fin (n+1) → UnitSpin N,
        Phi x old*(∏ i, ∫ z, b x i (old,z) ∂G w)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ G w))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  simp only [partitionMoment,tiltedWeightMean_zero,reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,
    zero_mul,Real.exp_zero,integral_const,probReal_univ,one_smul,one_pow,mul_one,div_one]

theorem partitionMoment_measurable {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (n m : ℕ) (P : Fin (n+1) → Polynomial ℝ)
    {Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ}
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2))
    {C : ℝ} (hC : 0≤C) (hp : ∀ x old, |Phi x old|≤C)
    (b : (Fin K → ℝ) → Fin m → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ))
    (hbM : ∀ i, Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 i p.2))
    (hbb : ∀ x i p, |b x i p|≤1) (t : ℝ) :
    Measurable (fun x ↦ partitionMoment nu v n m P Phi b x t) := by
  have hPhis (x : Fin K → ℝ) : Measurable (Phi x) := by
    convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hbs (x : Fin K → ℝ) (i : Fin m) : Measurable (b x i) := by
    convert (hbM i).comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have H := polynomialJet_measurable nu hv 0 (n+m) (padZero n P m)
    (Phi := fun x ↦ momentLift n (Phi x) m (b x))
    (momentLift_joint_measurable n m hPhi b hbM) t
  simpa only [lifted_jet_eq_partitionMoment nu hv n m P hPhis hC hp b hbs hbb] using H

theorem exists_uniform_partition_moment_threshold (K n m : ℕ)
    (P : Fin (n+1) → Polynomial ℝ) (hPK : ∀ j, (P j).natDegree≤K)
    {C : ℝ} (hC : 0≤C) (t : ℝ) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ), V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old, |Phi x old|≤C) →
        ∀ b : (Fin K → ℝ) → Fin m → (((Fin (n+1) → UnitSpin N)×UnitSpin N) → ℝ),
          (∀ i, Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦ b p.1 i p.2)) →
          (∀ x i p, |b x i p|≤1) →
          (∫ x, |partitionMoment nu v n m P Phi b x t-partitionMoment nu v n m P Phi b x 0|
            ∂positiveCubeLaw K)≤eps := by
  obtain ⟨V,hV,hU⟩ := exists_uniform_polynomial_invariance_threshold K (n+m) (padZero n P m)
    (padZero_degree_le n m P hPK) hC t heps
  refine ⟨V,hV,?_⟩
  intro N nu _ v hv Phi hPhi hp b hbM hbb
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  have hPhis (x : Fin K → ℝ) : Measurable (Phi x) := by
    convert hPhi.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have hbs (x : Fin K → ℝ) (i : Fin m) : Measurable (b x i) := by
    convert (hbM i).comp (measurable_const.prodMk measurable_id) using 1 <;> rfl
  have HL := hU nu v hv (fun x ↦ momentLift n (Phi x) m (b x))
    (momentLift_joint_measurable n m hPhi b hbM)
    (fun x old ↦ momentLift_abs_le n m hC (hp x) (b x) (hbb x) old)
  simpa only [lifted_jet_eq_partitionMoment nu hv0 n m P hPhis hC hp b hbs hbb] using HL

end
end TensorPCA.NonRSLowerProofs.SphericalGGPartitionMoments
