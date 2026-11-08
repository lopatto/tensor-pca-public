-- SPDX-License-Identifier: Apache-2.0
/- Narrow source-preserving analytic port from immutable Apache-2.0 source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/CSTwoAtom.lean
Only the generic admissible-law and two-atom section is retained; the unrelated
degree-4/12 nonconvex example section and its import are omitted.
The literal two-atom law and its elementary lemmas are imported from the
existing attributed CSTwoAtom port, avoiding duplicate declarations.
Generic cutoff-law calculus only: no zero-field origin-contact or concrete
minDegree support theorem is imported. Namespaces/import paths are local. -/
module

public import TensorPCA.RetainedCountProofs.CSTwoAtom
public import TensorPCA.NonRSLowerProofs.FiniteCSVariation

@[expose] public section

namespace TensorPCA.RetainedCountProofs.CrisantiSommers

open MeasureTheory Set

/-- The manuscript's admissible measures, with their ordinary probability law.
The cutoff is a witness of compact support below one, not a parameter of the value. -/
structure Admissible where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  cutoff_exists : ∃ q, HasCutoff law q

instance (ζ : Admissible) : IsProbabilityMeasure ζ.law := ζ.probability

noncomputable def Admissible.cutoff (ζ : Admissible) : ℝ :=
  Classical.choose ζ.cutoff_exists

theorem Admissible.hasCutoff (ζ : Admissible) : HasCutoff ζ.law ζ.cutoff :=
  Classical.choose_spec ζ.cutoff_exists

/-- The ordinary functional with its proved independence of support cutoff. -/
noncomputable def Admissible.value (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ) : ℝ :=
  functional β η ζ.law ζ.cutoff

theorem Admissible.value_eq (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ)
    {q : ℝ} (hq : HasCutoff ζ.law q) :
    ζ.value β η = functional β η ζ.law q :=
  functional_cutoff_independent ζ.law β η ζ.hasCutoff hq

/-- Global minimization is over all compact-supported probability measures
below one, exactly the manuscript's variational class. -/
def Admissible.IsMinimizer (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ) : Prop :=
  ∀ μ : Admissible, ζ.value β η ≤ μ.value β η

theorem Admissible.minimizer_of_support_on_maximum (ζ : Admissible)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1)) (m : ℝ)
    (hmax : ∀ s ∈ Ico (0:ℝ) 1, firstVariation β η ζ.law s ≤ m)
    (hsupport : ∀ᵐ s ∂ζ.law, firstVariation β η ζ.law s = m) :
    ζ.IsMinimizer β η := by
  intro μ
  exact functional_minimal_of_firstVariation_maximum β η μ.law ζ.law
    μ.hasCutoff ζ.hasCutoff hη m hmax hsupport

noncomputable def twoAtomAdmissible {x Q : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (hQ : Q ∈ Ico (0:ℝ) 1) : Admissible :=
  ⟨twoAtom x Q,twoAtom_probability hx,⟨Q,twoAtom_hasCutoff hQ⟩⟩

end TensorPCA.RetainedCountProofs.CrisantiSommers

