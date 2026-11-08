-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.PhysicalPressureGroundReduction
/-! Combine a pressure lower bound with a physical upper bound. The upper, pure/RS and
concentration estimates are assembled in the companion module.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.PhysicalPressureLimitReduction
open Set Filter
open scoped Topology
open PhysicalPressureGroundReduction
noncomputable section

/-- The interior nonRS finite-temperature input, with pure overlap, the closed RS domain
and poles covered by separate theorems.
-/
def NonRSFinitePressureLower : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ m ∈ Icc (-1 : ℝ) 1, 0 < |m| →
    |m| < Real.sqrt (1-1/((k : ℝ)-1)) → FinitePressureLower k m

theorem rsCutoff_le_one (k : ℕ) (hk : 3 ≤ k) :
    Real.sqrt (1-1/((k : ℝ)-1)) ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  exact Real.sqrt_le_one.mpr (sub_le_self 1 (one_div_nonneg.mpr (sub_nonneg.mpr hk1)))

theorem sliceGroundLimit_of_finitePressure_and_upper (k : ℕ) (hk : 3 ≤ k)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (hpressure : FinitePressureLower k m)
    (hUpper : ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop,
      GroundState.expectedSliceGround (n+1) k m ≤
        Scalar.variationalValue (Scalar.xiSlice k m) 0+eps) :
    GroundState.SliceGroundLimit k m := by
  unfold GroundState.SliceGroundLimit
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have heps : 0 < (Scalar.variationalValue (Scalar.xiSlice k m) 0-c)/2 := by linarith
    filter_upwards [eventually_expectedSliceGround_lower_of_finitePressure k hk hm hpressure heps]
      with n hn
    linarith
  · intro c hc
    have heps : 0 < (c-Scalar.variationalValue (Scalar.xiSlice k m) 0)/2 := by linarith
    filter_upwards [hUpper ((c-Scalar.variationalValue (Scalar.xiSlice k m) 0)/2) heps] with n hn
    linarith


end
end TensorPCA.NonRSLowerProofs.PhysicalPressureLimitReduction
