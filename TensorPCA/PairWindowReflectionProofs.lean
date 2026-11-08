-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.CoupledGaussianKernelProofs
public import TensorPCA.PairConcentrationProofs

/-! The absolute-overlap partition is controlled by the signed positive-overlap partition. Even physical Hamiltonians and second-spin prior
reflection justify the factor two; its logarithmic cost is kept explicitly. -/

@[expose] public section
namespace TensorPCA.PairWindowReflectionProofs
open MeasureTheory ProbabilityTheory Set Filter CoupledGaussianKernelProofs
open scoped Topology RealInnerProductSpace ENNReal
noncomputable section

def pairReflect (N : ℕ) (xy : Model.Vector N × Model.Vector N) : Model.Vector N × Model.Vector N :=
  (xy.1,-xy.2)

def signedPairPartition (N k : ℕ) (lam u eta : ℝ) (w : Model.Tensor N k) : ℝ :=
  ∫ xy, (signedPairWindow N u eta).indicator (fun xy ↦ Real.exp
    (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2))) xy
      ∂(Model.spherePrior N).prod (Model.spherePrior N)

def signedWindowLaw (N : ℕ) (u eta : ℝ) : Measure (Model.Vector N × Model.Vector N) :=
  ((Model.spherePrior N).prod (Model.spherePrior N)).restrict (signedPairWindow N u eta)

instance signedWindowLaw_finite (N : ℕ) (u eta : ℝ) : IsFiniteMeasure (signedWindowLaw N u eta) := by
  unfold signedWindowLaw
  infer_instance

theorem pairReflect_measurePreserving (N : ℕ) :
    MeasurePreserving (pairReflect N) ((Model.spherePrior N).prod (Model.spherePrior N))
      ((Model.spherePrior N).prod (Model.spherePrior N)) := by
  let T : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := LinearIsometryEquiv.neg ℝ
  have hmap := Measure.map_prod_map (Model.spherePrior N) (Model.spherePrior N) measurable_id T.continuous.measurable
  rw [Measure.map_id, Geometry.spherePrior_rotation_invariant T] at hmap
  refine ⟨continuous_fst.measurable.prodMk continuous_snd.neg.measurable, ?_⟩
  exact hmap.symm

theorem hamiltonian_neg_of_even {N k : ℕ} (heven : Even k) (w : Model.Tensor N k) (x : Model.Vector N) :
    Model.hamiltonian w (-x) = Model.hamiltonian w x := by
  have hf : Model.feature k (-x) = Model.feature k x := by
    rw [← neg_one_smul ℝ x, Geometry.feature_smul, heven.neg_one_pow, one_smul]
  simp only [Model.hamiltonian, Model.score, hf]

theorem signedPairPartition_eq_moment (N k : ℕ) (lam u eta : ℝ) (w : Model.Tensor N k) :
    signedPairPartition N k lam u eta w = GaussianSpinInterpolation.moment
      (signedWindowLaw N u eta) (fun _ ↦ 1) (physicalLinear N k lam) w := by
  unfold signedPairPartition signedWindowLaw GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
  rw [integral_indicator (isOpen_signedPairWindow N u eta).measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall (fun xy ↦ by simp only [one_mul, physicalLinear_apply])

theorem physicalLinear_bound_prod {N k : ℕ} (hN : 0 < N) (lam : ℝ) :
    ∀ᵐ xy ∂(Model.spherePrior N).prod (Model.spherePrior N),
      ‖physicalLinear N k lam xy‖ ≤ 2*|lam| *Real.sqrt N := by
  have hx : ∀ᵐ xy : Model.Vector N × Model.Vector N ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.1‖ = 1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hy : ∀ᵐ xy : Model.Vector N × Model.Vector N ∂(Model.spherePrior N).prod (Model.spherePrior N), ‖xy.2‖ = 1 :=
    Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hN)
  filter_upwards [hx,hy] with xy hx hy
  exact physicalLinear_norm_le N k lam xy hx hy

theorem pairWeight_integrable {N k : ℕ} (hN : 0 < N) (lam : ℝ) (w : Model.Tensor N k) :
    Integrable (fun xy : Model.Vector N × Model.Vector N ↦ Real.exp
      (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2)))
        ((Model.spherePrior N).prod (Model.spherePrior N)) := by
  have hi := GaussianSpinInterpolation.weight_integrable
    ((Model.spherePrior N).prod (Model.spherePrior N)) (fun _ ↦ (1 : ℝ)) (physicalLinear N k lam)
    measurable_const (physicalLinear_continuous N k lam).measurable (C := 1)
    ((physicalLinear_bound_prod (k := k) hN lam).mono (fun xy hxy ↦ ⟨by norm_num, hxy⟩)) w
  unfold GaussianSpinInterpolation.weight at hi
  simpa only [one_mul, physicalLinear_apply] using hi

theorem signedPairPartition_pos {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ) {u eta : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) (w : Model.Tensor N k) :
    0 < signedPairPartition N k lam u eta w := by
  have : NeZero (signedWindowLaw N u eta) := ⟨fun hz ↦
    (signedPairWindow_mass_pos hN hu heta).ne' (Measure.restrict_eq_zero.mp hz)⟩
  rw [signedPairPartition_eq_moment]
  exact GaussianSpinInterpolation.moment_one_pos (signedWindowLaw N u eta) (physicalLinear N k lam)
    (physicalLinear_continuous N k lam).measurable
    (ae_restrict_of_ae (physicalLinear_bound_prod (k := k) (by omega) lam)) w

/-- The actual even thermal absolute-window partition loses at most a factor
two when restricted to the signed positive-overlap window. -/
theorem pairPartition_le_two_signed {N k : ℕ} (hN : 0 < N) (heven : Even k)
    (lam u eta : ℝ) (w : Model.Tensor N k) :
    Coupled.pairPartition N k lam u eta w ≤ 2*signedPairPartition N k lam u eta w := by
  let μ := (Model.spherePrior N).prod (Model.spherePrior N)
  let F : (Model.Vector N × Model.Vector N) → ℝ :=
    (signedPairWindow N u eta).indicator (fun xy ↦ Real.exp
      (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2)))
  have hmF : Measurable F := (PairGibbsProofs.pairWeight_measurable N k lam w).indicator
    (isOpen_signedPairWindow N u eta).measurableSet
  have hiF : Integrable F μ := (pairWeight_integrable hN lam w).indicator
    (isOpen_signedPairWindow N u eta).measurableSet
  have hiFmap : Integrable F (μ.map (pairReflect N)) := by
    rw [(pairReflect_measurePreserving N).map_eq]
    exact hiF
  have hiR : Integrable (fun xy ↦ F (pairReflect N xy)) μ :=
    hiFmap.comp_measurable (pairReflect_measurePreserving N).measurable
  have hIntRef : (∫ xy, F (pairReflect N xy) ∂μ) = ∫ xy, F xy ∂μ := by
    have H := integral_map (μ := μ) (pairReflect_measurePreserving N).measurable.aemeasurable
      hmF.aestronglyMeasurable
    rw [(pairReflect_measurePreserving N).map_eq] at H
    exact H.symm
  have hpoint (xy : Model.Vector N × Model.Vector N) :
      (Coupled.pairWindow N u eta).indicator (fun xy ↦ Real.exp
        (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2))) xy ≤ F xy+F (pairReflect N xy) := by
    have hF0 (z : Model.Vector N × Model.Vector N) : 0 ≤ F z := by
      dsimp only [F]
      by_cases hz : z ∈ signedPairWindow N u eta
      · rw [indicator_of_mem hz]
        exact (Real.exp_pos _).le
      · rw [indicator_of_notMem hz]
    have hWeight : Real.exp (-lam*(Model.hamiltonian w (pairReflect N xy).1+
        Model.hamiltonian w (pairReflect N xy).2)) =
        Real.exp (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2)) := by
      simp only [pairReflect, hamiltonian_neg_of_even heven]
    by_cases hxy : xy ∈ Coupled.pairWindow N u eta
    · rw [indicator_of_mem hxy]
      by_cases hr : 0 ≤ inner ℝ xy.1 xy.2
      · have hS : xy ∈ signedPairWindow N u eta := by
          change |inner ℝ xy.1 xy.2-u| < eta
          change |inner ℝ xy.1 xy.2| ∈ Ioo (u-eta) (u+eta) at hxy
          rw [abs_of_nonneg hr] at hxy
          exact abs_lt.mpr ⟨by linarith [hxy.1], by linarith [hxy.2]⟩
        rw [show F xy = Real.exp (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2)) from indicator_of_mem hS _]
        exact le_add_of_nonneg_right (hF0 _)
      · have hS : pairReflect N xy ∈ signedPairWindow N u eta := by
          change |inner ℝ xy.1 (-xy.2)-u| < eta
          rw [inner_neg_right]
          change |inner ℝ xy.1 xy.2| ∈ Ioo (u-eta) (u+eta) at hxy
          rw [abs_of_neg (lt_of_not_ge hr)] at hxy
          exact abs_lt.mpr ⟨by linarith [hxy.1], by linarith [hxy.2]⟩
        have hFR : F (pairReflect N xy) = Real.exp (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2)) := by
          dsimp only [F]
          rw [indicator_of_mem hS, hWeight]
        rw [hFR]
        exact le_add_of_nonneg_left (hF0 _)
    · rw [indicator_of_notMem hxy]
      exact add_nonneg (hF0 _) (hF0 _)
  have H := integral_mono ((pairWeight_integrable hN lam w).indicator (PairGibbsProofs.pairWindow_measurableSet N u eta))
    (hiF.add hiR) hpoint
  simp only [Pi.add_apply] at H
  rw [integral_add hiF hiR, hIntRef] at H
  simpa only [Coupled.pairPartition, signedPairPartition, F, μ, two_mul] using H

/-- The exact logarithmic price of replacing the frozen absolute window by
its actual signed positive half. -/
theorem log_pairPartition_le_signed {N k : ℕ} (hN : 2 ≤ N) (heven : Even k)
    (lam : ℝ) {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta)
    (w : Model.Tensor N k) :
    Real.log (Coupled.pairPartition N k lam u eta w)/(N : ℝ) ≤
      Real.log (signedPairPartition N k lam u eta w)/(N : ℝ)+Real.log 2/(N : ℝ) := by
  have hNp : 0 < N := by omega
  have hmass : Coupled.windowMass N u eta ≠ 0 :=
    (WindowMassProofs.positiveWindowMass N hN u hu eta heta).ne'
  have H := Real.log_le_log (PairRegularityProofs.pairPartition_pos hNp lam u eta hmass w)
    (pairPartition_le_two_signed hNp heven lam u eta w)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (signedPairPartition_pos hN lam hu heta w).ne'] at H
  have HH := div_le_div_of_nonneg_right H (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at HH
  linarith

/-- The physical signed-window log partition is Lipschitz under its genuine
finite nonzero base law, retaining the base-mass constant. -/
theorem log_signedPairPartition_lipschitz {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    LipschitzWith (2*|lam| *Real.sqrt N).toNNReal
      (fun w ↦ Real.log (signedPairPartition N k lam u eta w)) := by
  have : NeZero (signedWindowLaw N u eta) := ⟨fun hz ↦
    (signedPairWindow_mass_pos hN hu heta).ne' (Measure.restrict_eq_zero.mp hz)⟩
  have H := PairConcentrationProofs.logPartition_lipschitz (signedWindowLaw N u eta)
    (physicalLinear N k lam) (physicalLinear_continuous N k lam).measurable (by positivity)
      (ae_restrict_of_ae (physicalLinear_bound_prod (k := k) (by omega) lam))
  have heq : (fun w ↦ Real.log (signedPairPartition N k lam u eta w)) =
      GaussianSpinInterpolation.logPartition (signedWindowLaw N u eta) (physicalLinear N k lam) := by
    funext w
    rw [signedPairPartition_eq_moment]
    rfl
  rw [heq]
  exact H

/-- The signed log partition is integrable, including its unnormalized base
mass offset; no probability assumption on signedWindowLaw is used. -/
theorem log_signedPairPartition_integrable {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    Integrable (fun w ↦ Real.log (signedPairPartition N k lam u eta w)) (Model.noiseLaw N k) := by
  let F : Model.Tensor N k → ℝ := fun w ↦ Real.log (signedPairPartition N k lam u eta w)
  let K : ℝ := 2*|lam| *Real.sqrt N
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hLip := log_signedPairPartition_lipschitz (k := k) hN lam hu heta
  have hnorm : Integrable (fun w : Model.Tensor N k ↦ K*‖w‖) (Model.noiseLaw N k) := by
    change Integrable (fun w : Model.Tensor N k ↦ K*‖w‖) (stdGaussian (Model.Tensor N k))
    exact IsGaussian.integrable_id.norm.const_mul K
  apply ((integrable_const |F 0|).add hnorm).mono' hLip.continuous.aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  have hdist := hLip.dist_le_mul w 0
  rw [Real.dist_eq, Real.coe_toNNReal _ hK, dist_zero_right] at hdist
  have htri : |F w| ≤ |F w-F 0|+|F 0| := by
    simpa only [sub_zero] using abs_sub_le (F w) (F 0) 0
  simpa only [Real.norm_eq_abs, Pi.add_apply, add_comm] using htri.trans (add_le_add hdist (le_refl _))

/-- Actual expected signed-window free energy, with its base-mass offset. -/
def meanSignedPairFreeEnergy (N k : ℕ) (lam u eta : ℝ) : ℝ :=
  ∫ w, Real.log (signedPairPartition N k lam u eta w)/(N : ℝ) ∂Model.noiseLaw N k

/-- The frozen EReal absolute-window quantity is bounded by the genuine signed
mean plus exactly log2/N. Positive window support is discharged here. -/
theorem expectedCoupledFreeEnergy_le_signed {N k : ℕ} (hN : 2 ≤ N) (heven : Even k)
    (lam : ℝ) {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    Coupled.expectedCoupledFreeEnergy N k lam u eta ≤
      ((meanSignedPairFreeEnergy N k lam u eta+Real.log 2/(N : ℝ) : ℝ) : EReal) := by
  have hmass : Coupled.windowMass N u eta ≠ 0 :=
    (WindowMassProofs.positiveWindowMass N hN u hu eta heta).ne'
  rw [PairConcentrationProofs.expectedCoupledFreeEnergy_eq N k lam u eta hmass]
  have hAbs := ((PairRegularityProofs.log_pairPartition_memLp (k := k) (by omega)
    lam u eta hmass 1 (by norm_num)).integrable le_rfl).div_const (N : ℝ)
  have hSigned := (log_signedPairPartition_integrable (k := k) hN lam hu heta).div_const (N : ℝ)
  have H := integral_mono hAbs (hSigned.add (integrable_const (Real.log 2/(N : ℝ))))
    (fun w ↦ log_pairPartition_le_signed hN heven lam hu heta w)
  simp only [Pi.add_apply] at H
  rw [integral_add hSigned (integrable_const (Real.log 2/(N : ℝ))),
    integral_const, probReal_univ, one_smul] at H
  change Coupled.meanPairFreeEnergy N k lam u eta ≤
    meanSignedPairFreeEnergy N k lam u eta+Real.log 2/(N : ℝ) at H
  exact_mod_cast H

/-- Every actual constrained thermal partition is at most the unconstrained
two-replica partition, directly from its Gibbs probability meaning. -/
theorem pairPartition_le_square {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ) (w : Model.Tensor N k) :
    Coupled.pairPartition N k lam u eta w ≤ (Model.partitionFunction N k lam w)^2 := by
  have := ThermalReplicaProofs.thermalGibbs_probability hN lam w
  have H : ((ThermalReplicaProofs.thermalGibbs N k lam w).prod
      (ThermalReplicaProofs.thermalGibbs N k lam w)).real (Coupled.pairWindow N u eta) ≤ 1 :=
    measureReal_le_one
  rw [PairGibbsProofs.thermalGibbs_pairWindow_real hN lam u eta w] at H
  exact (div_le_one (sq_pos_of_pos (FreeEnergyProofs.partitionFunction_pos hN lam w))).mp H

/-- Pointwise positive-branch constrained free energy is at most twice the
actual null free energy, in every positive dimension. -/
theorem pairFreeEnergy_le_twice_null {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (hm : Coupled.windowMass N u eta ≠ 0) (w : Model.Tensor N k) :
    Real.log (Coupled.pairPartition N k lam u eta w)/(N : ℝ) ≤ 2*Model.freeEnergy N k lam w := by
  calc
    _ ≤ Real.log ((Model.partitionFunction N k lam w)^2)/(N : ℝ) :=
      div_le_div_of_nonneg_right
        (Real.log_le_log (PairRegularityProofs.pairPartition_pos hN lam u eta hm w)
          (pairPartition_le_square hN lam u eta w)) (Nat.cast_nonneg N)
    _ = _ := by rw [Real.log_pow, Model.freeEnergy]; push_cast; ring

/-- A coarse actual bound handles exceptional dimensions, including N=1,
without changing the frozen EReal empty-window convention. -/
theorem expectedCoupledFreeEnergy_le_sq {N k : ℕ} (hN : 0 < N) (heven : Even k)
    (lam : ℝ) (hlam : 0 ≤ lam) (u eta : ℝ) :
    Coupled.expectedCoupledFreeEnergy N k lam u eta ≤ ((lam^2 : ℝ) : EReal) := by
  by_cases hm : Coupled.windowMass N u eta = 0
  · simp only [Coupled.expectedCoupledFreeEnergy, hm, ite_true]
    exact bot_le
  · rw [PairConcentrationProofs.expectedCoupledFreeEnergy_eq N k lam u eta hm]
    have hiPair := ((PairRegularityProofs.log_pairPartition_memLp (k := k) hN
      lam u eta hm 1 (by norm_num)).integrable le_rfl).div_const (N : ℝ)
    have hiFE := (FreeEnergyProofs.freeEnergy_memLp (k := k) hN lam 1 (by norm_num)).integrable le_rfl
    have H := integral_mono hiPair (hiFE.const_mul 2) (pairFreeEnergy_le_twice_null hN lam u eta hm)
    rw [integral_const_mul] at H
    change Coupled.meanPairFreeEnergy N k lam u eta ≤ 2*Coupled.meanNullFE N k lam at H
    have hgap := (ThermalReplicaProofs.freeEnergyGap_bounds hN heven hlam).1
    unfold ThermalReplicaProofs.freeEnergyGap at hgap
    exact_mod_cast (by linarith : Coupled.meanPairFreeEnergy N k lam u eta ≤ lam^2)

end
end TensorPCA.PairWindowReflectionProofs
