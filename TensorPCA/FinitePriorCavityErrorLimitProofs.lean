-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GuerraPinningProofs

/-! The explicit finite-prior cavity error vanishes at the square-root reveal
rate. Constants are fixed in dimension; no overlap-concentration hypothesis is
used by this deterministic limit. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityErrorLimitProofs
open Filter
noncomputable section

/-- The collision, thermal-pinning, last-spin reveal and adjacent-rate errors
all vanish. At use L is log(card S); this limit needs no sign assumptions. -/
theorem cavity_error_tendsto_zero (C K L : ℝ) :
    Tendsto (fun N : ℕ =>
      C*(1/(N : ℝ)+Real.sqrt (4*K^4*Real.sqrt
        (L/((N : ℝ)*(1/Real.sqrt N)))))+
      (1/Real.sqrt N)*L+2*L/Real.sqrt (N+1 : ℕ)) atTop (nhds 0) := by
  have hp : Tendsto (fun N : ℕ => C*Real.sqrt (4*K^4*Real.sqrt
      (L/((N : ℝ)*(1/Real.sqrt N))))) atTop (nhds 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    exact GuerraPinningProofs.pinning_error_tendsto_zero L C K
  have h1 : Tendsto (fun N : ℕ => C*(1/(N : ℝ))) atTop (nhds 0) := by
    simpa only [mul_one_div] using tendsto_const_div_atTop_nhds_zero_nat C
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun N : ℕ => (1/Real.sqrt N)*L) atTop (nhds 0) := by
    simpa only [zero_mul] using (hs.const_div_atTop 1).mul_const L
  have h3 : Tendsto (fun N : ℕ => 2*L/Real.sqrt (N+1 : ℕ)) atTop (nhds 0) :=
    (hs.comp (tendsto_add_atTop_nat 1)).const_div_atTop (2*L)
  simpa only [mul_add,zero_add,add_zero] using ((h1.add hp).add h2).add h3

end
end TensorPCA.FinitePriorCavityErrorLimitProofs
