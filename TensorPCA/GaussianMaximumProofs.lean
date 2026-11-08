-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import TensorPCA.EnvelopeProofs
public import TensorPCA.GaussianDensityProofs
public import Mathlib.Analysis.Calculus.Rademacher

/-! Uniqueness for finite-dimensional Gaussian linear maxima on compact sets.
The deterministic part is the differentiability of a compact support value. -/

@[expose] public section
namespace TensorPCA.GaussianMaximumProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def supportValue (K : Set E) (b : E → ℝ) (w : E) : ℝ :=
  sSup ((fun x ↦ inner ℝ x w+b x) '' K)

theorem supportValue_attained {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) (w : E) :
    ∃ x ∈ K, inner ℝ x w+b x = supportValue K b w ∧
      ∀ y ∈ K, inner ℝ y w+b y ≤ inner ℝ x w+b x := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    ((continuous_id.inner continuous_const).continuousOn.add hb)
  refine ⟨x, hx, ?_, hmax⟩
  symm
  exact (show IsGreatest ((fun x ↦ inner ℝ x w+b x) '' K) (inner ℝ x w+b x) from
    ⟨mem_image_of_mem _ hx, by rintro _ ⟨y, hy, rfl⟩; exact hmax hy⟩).csSup_eq

theorem le_supportValue {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) (w : E) {x : E} (hx : x ∈ K) :
    inner ℝ x w+b x ≤ supportValue K b w := by
  obtain ⟨y, _, hy, hmax⟩ := supportValue_attained hK hne hb w
  rw [← hy]
  exact hmax x hx

theorem supportValue_lipschitz {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) :
    ∃ M : ℝ≥0, LipschitzWith M (supportValue K b) := by
  obtain ⟨M, _, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨M.toNNReal, LipschitzWith.of_le_add_mul' M ?_⟩
  intro w z
  obtain ⟨x, hx, hmax, _⟩ := supportValue_attained hK hne hb w
  have hbase := le_supportValue hK hne hb z hx
  have hdif : inner ℝ x w-inner ℝ x z ≤ M*‖w-z‖ := calc
    _ = inner ℝ x (w-z) := (inner_sub_right _ _ _).symm
    _ ≤ ‖x‖*‖w-z‖ := real_inner_le_norm _ _
    _ ≤ M*‖w-z‖ := mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
  rw [dist_eq_norm]
  linarith

/-- At a differentiability point, every maximizing vector represents the
same derivative. This argument allows an arbitrary deterministic continuous shift. -/
theorem derivative_eq_of_maximizer {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) {w x : E} (hx : x ∈ K)
    (hxmax : inner ℝ x w+b x = supportValue K b w)
    {L : E →L[ℝ] ℝ} (hd : HasFDerivAt (supportValue K b) L w) :
    L = innerSL ℝ x := by
  have hmin : IsLocalMin (fun z : E ↦ supportValue K b z-inner ℝ x z-b x) w := by
    apply Filter.Eventually.of_forall
    intro z
    change supportValue K b w-inner ℝ x w-b x ≤
      supportValue K b z-inner ℝ x z-b x
    have hz := le_supportValue hK hne hb z hx
    linarith
  have hd' : HasFDerivAt (fun z : E ↦ supportValue K b z-inner ℝ x z-b x)
      (L-innerSL ℝ x) w := by
    simpa only [sub_zero, Pi.sub_apply, coe_innerSL_apply] using
      (hd.sub (innerSL ℝ x).hasFDerivAt).sub_const (b x)
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hd')

theorem maximizers_eq_of_differentiable {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {b : E → ℝ} (hb : ContinuousOn b K) {w x y : E}
    (hd : DifferentiableAt ℝ (supportValue K b) w)
    (hx : x ∈ K) (hxmax : inner ℝ x w+b x = supportValue K b w)
    (hy : y ∈ K) (hymax : inner ℝ y w+b y = supportValue K b w) : x = y := by
  have hdx := derivative_eq_of_maximizer hK hne hb hx hxmax hd.hasFDerivAt
  have hdy := derivative_eq_of_maximizer hK hne hb hy hymax hd.hasFDerivAt
  apply ext_inner_right ℝ
  intro v
  have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (hdx.symm.trans hdy)
  simpa only [innerSL_apply_apply] using h


variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A finite-dimensional compact linear maximum with continuous deterministic
shift has a unique optimizing vector for every absolutely continuous input law. -/
theorem ae_existsUnique_maximizer_of_absolutelyContinuous {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) {b : E → ℝ} (hb : ContinuousOn b K)
    {μ : Measure E} (hμ : μ ≪ (volume : Measure E)) :
    ∀ᵐ w ∂μ, ∃! x : E, x ∈ K ∧ inner ℝ x w+b x = supportValue K b w := by
  obtain ⟨M, hLip⟩ := supportValue_lipschitz hK hne hb
  have hd : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ (supportValue K b) w :=
    hLip.ae_differentiableAt
  filter_upwards [hμ.ae_le hd] with w hw
  obtain ⟨x, hx, hxmax, _⟩ := supportValue_attained hK hne hb w
  refine ⟨x, ⟨hx, hxmax⟩, ?_⟩
  intro y hy
  exact maximizers_eq_of_differentiable hK hne hb hw hy.1 hy.2 hx hxmax

theorem stdGaussian_ae_existsUnique_maximizer {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) {b : E → ℝ} (hb : ContinuousOn b K) :
    ∀ᵐ w ∂stdGaussian E,
      ∃! x : E, x ∈ K ∧ inner ℝ x w+b x = supportValue K b w :=
  ae_existsUnique_maximizer_of_absolutelyContinuous hK hne hb
    GaussianDensityProofs.stdGaussian_absolutelyContinuous_volume


/-- Every planted observation law has a Lebesgue density, since its independent
Gaussian noise remains absolutely continuous after each fixed signal translation. -/
theorem observationLaw_absolutelyContinuous_volume (N k : ℕ) (lam : ℝ) :
    Model.observationLaw N k lam ≪ (volume : Measure (Model.Tensor N k)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  rw [Model.observationLaw, Measure.map_apply (Model.measurable_observation N k lam) hA]
  apply Measure.measure_prod_null_of_ae_null
    (hA.preimage (Model.measurable_observation N k lam))
  apply Filter.Eventually.of_forall
  intro x
  apply GaussianDensityProofs.stdGaussian_absolutelyContinuous_volume
    (E := Model.Tensor N k)
  change volume ((fun w : Model.Tensor N k ↦
    (lam*Real.sqrt N) • Model.feature k x+w) ⁻¹' A) = 0
  rw [measure_preimage_add]
  exact hnull


/-- The fibers of the ordered unit tensor power are singletons for odd degree
and exactly antipodal pairs for even positive degree. -/
theorem feature_eq_iff_unit {N k : ℕ} (hk : k ≠ 0) {x y : Model.Vector N}
    (hx : x ∈ Model.unitSphere N) (hy : y ∈ Model.unitSphere N) :
    Model.feature k x = Model.feature k y ↔ x = y ∨ x = -y ∧ Even k := by
  constructor
  · intro hxy
    have hp : (inner ℝ x y)^k = 1 := by
      rw [← Geometry.feature_inner, hxy, real_inner_self_eq_norm_sq,
        Geometry.feature_unit_norm y hy, one_pow]
    rcases (pow_eq_one_iff_of_ne_zero hk).mp hp with hpos | ⟨hneg, heven⟩
    · exact Or.inl ((inner_eq_one_iff_of_norm_eq_one hx hy).mp hpos)
    · exact Or.inr ⟨(inner_eq_neg_one_iff_of_norm_eq_one hx hy).mp hneg, heven⟩
  · rintro (rfl | ⟨rfl, heven⟩)
    · rfl
    · rw [← neg_one_smul ℝ y, Geometry.feature_smul, heven.neg_one_pow, one_smul]


/-- Exact almost-sure classification of all actual likelihood maximizers. In
odd positive degree the second alternative is impossible; in even degree it is
the antipodal pair. The statement holds for each fixed deterministic strength. -/
theorem observationLaw_ae_maximizers {N k : ℕ} (hN : 0 < N) (hk : k ≠ 0)
    (lam : ℝ) :
    ∀ᵐ w ∂Model.observationLaw N k lam,
      ∃ x ∈ Model.unitSphere N, ∀ y ∈ Model.unitSphere N,
        (∀ z ∈ Model.unitSphere N, Model.score w z ≤ Model.score w y) ↔
          y = x ∨ y = -x ∧ Even k := by
  let K : Set (Model.Tensor N k) := Model.feature k '' Model.unitSphere N
  have hK : IsCompact K := (Geometry.unitSphere_isCompact N).image
    (Model.continuous_feature N k)
  have hne : K.Nonempty := (Geometry.unitSphere_nonempty hN).image _
  have hu := ae_existsUnique_maximizer_of_absolutelyContinuous hK hne
    (continuousOn_const (c := (0 : ℝ)))
    (observationLaw_absolutelyContinuous_volume N k lam)
  filter_upwards [hu] with w hw
  obtain ⟨T, hT, huniq⟩ := hw
  rcases hT.1 with ⟨x, hx, rfl⟩
  have hmax : ∀ z ∈ Model.unitSphere N, Model.score w z ≤ Model.score w x := by
    intro z hz
    have hle := le_supportValue hK hne (continuousOn_const (c := (0 : ℝ))) w
      (show Model.feature k z ∈ K from mem_image_of_mem _ hz)
    have heq := hT.2
    simpa only [Model.score, add_zero] using hle.trans_eq heq.symm
  refine ⟨x, hx, ?_⟩
  intro y hy
  constructor
  · intro hymax
    have hyvalue : inner ℝ (Model.feature k y) w+0 = supportValue K (fun _ ↦ 0) w := by
      apply le_antisymm
      · exact le_supportValue hK hne (continuousOn_const (c := (0 : ℝ))) w
          (mem_image_of_mem _ hy)
      · rw [← hT.2]
        simpa only [add_zero, Model.score] using hymax x hx
    have hfeat : Model.feature k y = Model.feature k x :=
      huniq _ ⟨mem_image_of_mem _ hy, hyvalue⟩
    exact (feature_eq_iff_unit hk hy hx).mp hfeat
  · intro hcases
    have hfeat := (feature_eq_iff_unit hk hy hx).mpr hcases
    intro z hz
    simpa only [Model.score, hfeat] using hmax z hz


theorem observationLaw_ae_unique_odd {N k : ℕ} (hN : 0 < N) (hk : k ≠ 0)
    (hodd : Odd k) (lam : ℝ) :
    ∀ᵐ w ∂Model.observationLaw N k lam, ∃! x : Model.Vector N,
      x ∈ Model.unitSphere N ∧
        ∀ z ∈ Model.unitSphere N, Model.score w z ≤ Model.score w x := by
  filter_upwards [observationLaw_ae_maximizers hN hk lam] with w hw
  obtain ⟨x, hx, hclass⟩ := hw
  refine ⟨x, ⟨hx, (hclass x hx).mpr (Or.inl rfl)⟩, ?_⟩
  intro y hy
  rcases (hclass y hy.1).mp hy.2 with heq | ⟨_, heven⟩
  · exact heq
  · exact False.elim ((Nat.not_even_iff_odd.mpr hodd) heven)

theorem observationLaw_ae_antipodal_even {N k : ℕ} (hN : 0 < N) (hk : k ≠ 0)
    (heven : Even k) (lam : ℝ) :
    ∀ᵐ w ∂Model.observationLaw N k lam,
      ∃ x ∈ Model.unitSphere N, x ≠ -x ∧ ∀ y ∈ Model.unitSphere N,
        (∀ z ∈ Model.unitSphere N, Model.score w z ≤ Model.score w y) ↔
          y = x ∨ y = -x := by
  filter_upwards [observationLaw_ae_maximizers hN hk lam] with w hw
  obtain ⟨x, hx, hclass⟩ := hw
  refine ⟨x, hx, ?_, ?_⟩
  · intro heq
    have hi := congrArg (fun z ↦ inner ℝ x z) heq
    rw [inner_neg_right, real_inner_self_eq_norm_sq, show ‖x‖ = 1 from hx] at hi
    norm_num at hi
  · intro y hy
    simpa only [heven, and_true] using hclass y hy

end
end TensorPCA.GaussianMaximumProofs
