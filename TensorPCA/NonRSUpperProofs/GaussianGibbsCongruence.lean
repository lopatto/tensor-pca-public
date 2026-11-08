-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed normalized-Gibbs congruence lemma from immutable source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GaussianGibbsTransport.lean
Its exact theorem and proof body are retained; unused transport lemmas omitted. -/
module
public import TensorPCA.NonRSUpperProofs.GaussianSpinKernels
@[expose] public section
noncomputable section
namespace TensorPCA.GaussianSpinInterpolation
open MeasureTheory Set
variable {V H H' : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']
/-- Actual field equality almost everywhere determines the normalized
Gibbs law, even if the fields use different coefficient spaces. -/
theorem gibbsMeasure_congr_field (ν : Measure V)
    (L : V → H →L[ℝ] ℝ) (w : H) (M : V → H' →L[ℝ] ℝ) (z : H')
    (heq : ∀ᵐ x ∂ν,L x w=M x z) : gibbsMeasure ν L w=gibbsMeasure ν M z := by
  have hm : moment ν (fun _ => 1) L w=moment ν (fun _ => 1) M z := by
    unfold moment
    apply integral_congr_ae
    exact heq.mono fun x hx => by simp only [weight,hx]
  unfold gibbsMeasure
  rw [hm]
  apply withDensity_congr_ae
  exact heq.mono fun x hx => by simp only [hx]

end TensorPCA.GaussianSpinInterpolation
