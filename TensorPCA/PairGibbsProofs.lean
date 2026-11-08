-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.ThermalReplicaProofs

/-! The literal two-replica Gibbs probability and constrained partition function. -/
@[expose] public section
namespace TensorPCA.PairGibbsProofs
open Set MeasureTheory ProbabilityTheory ThermalReplicaProofs FreeEnergyProofs
open scoped ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem thermalDensity_measurable (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    Measurable (fun x : Model.Vector N ↦
      Real.exp (-lam*Model.hamiltonian w x)/Model.partitionFunction N k lam w) := by
  have H : Continuous (fun x : Model.Vector N ↦ thermalLinear N k 1 x (lam • w)) :=
    (thermalLinear_continuous N k 1).clm_apply continuous_const
  simpa only [Function.comp_apply, thermalLinear_base_apply] using
    (Real.continuous_exp.comp H).measurable.div_const (Model.partitionFunction N k lam w)

theorem pairWindow_measurableSet (N : ℕ) (u eta : ℝ) :
    MeasurableSet (Coupled.pairWindow N u eta) := by
  exact (isOpen_Ioo.preimage
    ((continuous_fst.inner continuous_snd : Continuous
      (fun xy : Model.Vector N × Model.Vector N ↦ inner ℝ xy.1 xy.2)).abs)).measurableSet

theorem thermalGibbs_product_eq_withDensity {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (w : Model.Tensor N k) :
    (thermalGibbs N k lam w).prod (thermalGibbs N k lam w) =
      ((Model.spherePrior N).prod (Model.spherePrior N)).withDensity
        (fun xy ↦ ENNReal.ofReal (Real.exp (-lam*
          (Model.hamiltonian w xy.1+Model.hamiltonian w xy.2)) /
            (Model.partitionFunction N k lam w)^2)) := by
  have hm := (thermalDensity_measurable N k lam w).ennreal_ofReal
  have hz := partitionFunction_pos (k := k) hN lam w
  unfold thermalGibbs
  rw [prod_withDensity hm hm]
  congr 1
  funext xy
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hz.le)]
  congr 1
  rw [div_mul_div_comm, ← Real.exp_add, ← sq]
  congr 2
  ring

theorem pairWeight_measurable (N k : ℕ) (lam : ℝ) (w : Model.Tensor N k) :
    Measurable (fun xy : Model.Vector N × Model.Vector N ↦ Real.exp
      (-lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2))) := by
  have H : Continuous (fun x : Model.Vector N ↦ Model.hamiltonian w x) := by
    unfold Model.hamiltonian Model.score
    exact continuous_const.mul ((Model.continuous_feature N k).inner continuous_const)
  exact (Real.continuous_exp.comp (continuous_const.mul
    ((H.comp continuous_fst).add (H.comp continuous_snd)))).measurable

theorem thermalGibbs_product_real {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    (w : Model.Tensor N k) {S : Set (Model.Vector N × Model.Vector N)}
    (hS : MeasurableSet S) :
    ((thermalGibbs N k lam w).prod (thermalGibbs N k lam w)).real S =
      (∫ xy, S.indicator (fun xy ↦ Real.exp (-lam*
        (Model.hamiltonian w xy.1+Model.hamiltonian w xy.2))) xy
          ∂(Model.spherePrior N).prod (Model.spherePrior N)) /
        (Model.partitionFunction N k lam w)^2 := by
  have hd := ((pairWeight_measurable N k lam w).div_const
    ((Model.partitionFunction N k lam w)^2)).ennreal_ofReal
  rw [← integral_indicator_one hS, thermalGibbs_product_eq_withDensity hN lam w,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le (sq_nonneg _)), smul_eq_mul]
  rw [← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xy ↦ by
    by_cases hxy : xy ∈ S <;> simp [hxy])

theorem thermalGibbs_pairWindow_real {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (w : Model.Tensor N k) :
    ((thermalGibbs N k lam w).prod (thermalGibbs N k lam w)).real
      (Coupled.pairWindow N u eta) =
        Coupled.pairPartition N k lam u eta w / (Model.partitionFunction N k lam w)^2 :=
  thermalGibbs_product_real hN lam w (pairWindow_measurableSet N u eta)

theorem log_thermalGibbs_pairWindow {N k : ℕ} (hN : 0 < N) (lam u eta : ℝ)
    (w : Model.Tensor N k) (hp : 0 < Coupled.pairPartition N k lam u eta w) :
    Real.log (((thermalGibbs N k lam w).prod (thermalGibbs N k lam w)).real
      (Coupled.pairWindow N u eta)) / (N : ℝ) =
        Real.log (Coupled.pairPartition N k lam u eta w)/(N : ℝ) -
          2*Model.freeEnergy N k lam w := by
  rw [thermalGibbs_pairWindow_real hN lam u eta w,
    Real.log_div hp.ne' (pow_ne_zero 2 (partitionFunction_pos (k := k) hN lam w).ne'),
    Real.log_pow]
  unfold Model.freeEnergy
  push_cast
  ring

end
end TensorPCA.PairGibbsProofs
