-- SPDX-License-Identifier: MIT
/-
MIT License

Copyright (c) 2026 P. M. Aronow and Patrick Lopatto

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Immutable original: pmaronow/aging-temp e28568e30a6ea1e20fce2b8e0a3a72da15759209,
formalization/SphericalAging/EuclideanNets.lean; retained by the pinned source
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
vendor/all-lean/SphericalAging/EuclideanNets.lean.
The local namespace/import prefix is changed to TensorPCA.RetainedCountProofs,
with explicit canonical tactic imports as needed. Mathematical bodies are
retained; local porting changes are Apache-2.0.
-/
module

public import TensorPCA.RetainedCountProofs.FiniteModel
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

/-! Finite unit-sphere nets with dimension-exponential cardinality, obtained
from maximal separated sets and the disjoint-ball Haar volume argument. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory Module
open scoped NNReal ENNReal

namespace TensorPCA.RetainedCountProofs.EuclideanNets
open FiniteModel

theorem compact_packingNumber_ne_top {E : Type*} [PseudoEMetricSpace E] {A : Set E}
    (hA : IsCompact A) {ε : ℝ≥0} (hε : 0 < ε) : packingNumber ε A ≠ ⊤ := by
  let δ : ℝ≥0 := ε/2
  have hδ : δ ≠ 0 := by dsimp only [δ]; positivity
  obtain ⟨C,_,hC,hcov⟩ := exists_finite_isCover_of_isCompact hδ hA
  have hh := packingNumber_two_mul_le_externalCoveringNumber δ A
  have h2 : 2*δ=ε := by dsimp only [δ]; ring
  rw [h2] at hh
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hC) (hh.trans hcov.externalCoveringNumber_le_encard)

theorem finite_separated_sphere_card {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (S : Finset (Vector N)) (hunit : ∀ x ∈ S, ‖x‖=1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) :
    (S.card : ℝ) ≤ (1+2/ε)^N := by
  let r := ε/2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hdisj : PairwiseDisjoint (↑S : Set (Vector N)) (fun x => ball x r) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    have hh := hsep x hx y hy hxy
    dsimp only [r]
    linarith
  have hsubset : (⋃ x ∈ S, ball x r) ⊆ ball (0 : Vector N) (1+r) := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp hz
    have hh := dist_triangle z x (0 : Vector N)
    simp only [dist_zero_right] at hh
    rw [hunit x hx] at hh
    change dist z 0 < 1+r
    rw [dist_zero_right]
    exact lt_of_le_of_lt hh (show dist z x+1 < 1+r by have hd := mem_ball.mp hzx; linarith)
  have hmeasure : ∑ x ∈ S, volume (ball x r) ≤ volume (ball (0 : Vector N) (1+r)) := by
    rw [← measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)]
    exact measure_mono hsubset
  have hball (x : Vector N) : volume (ball x r)=ENNReal.ofReal (r^N)*volume (ball (0 : Vector N) 1) := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin] using Measure.addHaar_ball_of_pos volume x hr
  have hbig : volume (ball (0 : Vector N) (1+r))=
      ENNReal.ofReal ((1+r)^N)*volume (ball (0 : Vector N) 1) := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin] using
      Measure.addHaar_ball_of_pos volume (0 : Vector N) (show 0 < 1+r by linarith)
  rw [hbig] at hmeasure
  simp only [hball,Finset.sum_const,nsmul_eq_mul] at hmeasure
  have hunitTop : volume (ball (0 : Vector N) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hunitPos : 0 < (volume (ball (0 : Vector N) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume _ (show (0 : ℝ) < 1 by norm_num)).ne' hunitTop
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunitTop) hmeasure
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal
    (pow_nonneg hr.le N),ENNReal.toReal_ofReal (pow_nonneg (by linarith : 0 ≤ 1+r) N)] at hreal
  have hc : (S.card : ℝ)*r^N ≤ (1+r)^N := by
    apply (mul_le_mul_iff_left₀ hunitPos).mp
    simpa only [mul_assoc] using hreal
  have heq : (1+r)^N=((1+2/ε)^N)*r^N := by
    rw [← mul_pow]
    congr 1
    dsimp only [r]
    field_simp
    ring
  rw [heq] at hc
  exact (mul_le_mul_iff_left₀ (pow_pos hr N)).mp hc

/-- An actual ε-net of the Euclidean unit sphere with the standard volume bound. -/
theorem unit_sphere_net (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Vector N),
      (∀ x ∈ S, ‖x‖=1) ∧
      (∀ x : Vector N, ‖x‖=1 → ∃ y ∈ S, dist x y ≤ ε) ∧
      (S.card : ℝ) ≤ (1+2/ε)^N := by
  let rad : ℝ≥0 := ⟨ε,hε.le⟩
  let A : Set (Vector N) := sphere 0 1
  have hpack : packingNumber rad A ≠ ⊤ :=
    compact_packingNumber_ne_top (isCompact_sphere 0 1) hε
  let C := maximalSeparatedSet rad A
  have hCA : C ⊆ A := maximalSeparatedSet_subset
  have hCS : IsSeparated rad C := isSeparated_maximalSeparatedSet
  have hCF : C.Finite := Set.encard_ne_top_iff.mp (by
    change (maximalSeparatedSet rad A).encard ≠ ⊤
    rw [encard_maximalSeparatedSet hpack]
    exact hpack)
  let S := hCF.toFinset
  have hunit : ∀ x ∈ S, ‖x‖=1 := by
    intro x hx
    have hh := hCA (hCF.mem_toFinset.mp hx)
    simpa only [A,mem_sphere,dist_zero_right] using hh
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y := by
    intro x hx y hy hxy
    have hh := hCS (hCF.mem_toFinset.mp hx) (hCF.mem_toFinset.mp hy) hxy
    dsimp only at hh
    rw [ENNReal.coe_nnreal_eq] at hh
    change ENNReal.ofReal ε < edist x y at hh
    rw [edist_dist] at hh
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp hh
  have hcov : IsCover rad A C := isCover_maximalSeparatedSet hpack
  refine ⟨S,hunit,?_,finite_separated_sphere_card hε S hunit hsep⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hcov (show x ∈ A by simpa only [A,mem_sphere,dist_zero_right] using hx)
  refine ⟨y,hCF.mem_toFinset.mpr hy,?_⟩
  change edist x y ≤ (rad : ℝ≥0∞) at hxy
  rw [ENNReal.coe_nnreal_eq] at hxy
  change edist x y ≤ ENNReal.ofReal ε at hxy
  exact (edist_le_ofReal hε.le).mp hxy


end TensorPCA.RetainedCountProofs.EuclideanNets
