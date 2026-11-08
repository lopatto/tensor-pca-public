-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorGuerraLowerProofs
public import TensorPCA.FinitePriorScalarDomainProofs

/-! # Unconditional finite-prior Guerra lower asymptotics -/
@[expose] public section

namespace TensorPCA.FinitePriorGuerraAsymptoticProofs

open MeasureTheory ProbabilityTheory Set Filter FinitePriorChannelProofs
open FinitePriorGuerraLowerProofs FinitePriorScalarDomainProofs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The actual free-energy sequence eventually exceeds the entire compact
scalar variational value minus any positive error. -/
theorem finite_guerra_compact_eventual_lower (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 0 < k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      sSup (scalarPotential p a k gamma '' Icc (0:ℝ) 1)-epsilon ≤ freeEnergy p a N k gamma := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (zero_le_one : (0:ℝ) ≤ 1)) (continuous_scalarPotential p a k gamma).continuousOn
  have hg : IsGreatest (scalarPotential p a k gamma '' Icc (0:ℝ) 1) (scalarPotential p a k gamma m) :=
    ⟨⟨m,hm,rfl⟩,by rintro y ⟨q,hq,rfl⟩; exact hmax hq⟩
  rw [hg.isLUB.csSup_eq ⟨_,hg.1⟩]
  exact finite_guerra_eventual_lower p a hk hgamma hm.1 hepsilon

/-- The global nonnegative scalar variational value obeys the same genuine
Guerra lower asymptotic; compactness is proved from the prior second moment. -/
theorem finite_guerra_global_eventual_lower (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      sSup (scalarPotential p a k gamma '' Ici (0:ℝ))-epsilon ≤ freeEnergy p a N k gamma := by
  obtain ⟨m,hm,hmax⟩ := exists_global_scalarMaximizer p a hk hgamma
  have hg : IsGreatest (scalarPotential p a k gamma '' Ici (0:ℝ)) (scalarPotential p a k gamma m) :=
    ⟨⟨m,hm.1,rfl⟩,by rintro y ⟨q,hq,rfl⟩; exact hmax q hq⟩
  rw [hg.isLUB.csSup_eq ⟨_,hg.1⟩]
  exact finite_guerra_eventual_lower p a (by omega) hgamma hm.1 hepsilon


end TensorPCA.FinitePriorGuerraAsymptoticProofs
