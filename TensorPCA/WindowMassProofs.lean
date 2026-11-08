-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairGibbsProofs
public import TensorPCA.GaussianDensityProofs

/-! Strict positivity of every physical positive-width absolute-overlap window. -/
@[expose] public section
namespace TensorPCA.WindowMassProofs
open Set Filter MeasureTheory ProbabilityTheory PairGibbsProofs
open scoped Topology ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem volume_absolutelyContinuous_stdGaussian (N : ℕ) :
    (volume : Measure (Model.Vector N)) ≪ stdGaussian (Model.Vector N) := by
  rw [GaussianDensityProofs.stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous'
    GaussianDensityProofs.density_continuous.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (GaussianDensityProofs.density_pos x)).ne'))

theorem spherePrior_pos_of_open_unit {N : ℕ} {S : Set (Model.Vector N)}
    (hS : IsOpen S) {x : Model.Vector N} (hx : ‖x‖ = 1) (hxS : x ∈ S) :
    0 < Model.spherePrior N S := by
  letI : Measure.IsOpenPosMeasure (stdGaussian (Model.Vector N)) :=
    (volume_absolutelyContinuous_stdGaussian N).isOpenPosMeasure
  have hcont : ContinuousAt (Model.normalize (N := N)) x := by
    exact (continuous_norm.continuousAt.inv₀ (by rw [hx]; norm_num)).smul continuousAt_id
  have hfix : Model.normalize x = x := by simp only [Model.normalize, hx, inv_one, one_smul]
  rw [Model.spherePrior, Measure.map_apply (Model.measurable_normalize N) hS.measurableSet]
  exact Measure.measure_pos_of_mem_nhds _ (hcont.preimage_mem_nhds (hS.mem_nhds (hfix.symm ▸ hxS)))

theorem spherePrior_product_pos_of_open_unit {N : ℕ}
    {S : Set (Model.Vector N × Model.Vector N)} (hS : IsOpen S)
    {x y : Model.Vector N} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : (x,y) ∈ S) :
    0 < ((Model.spherePrior N).prod (Model.spherePrior N)) S := by
  obtain ⟨U,V,hU,hxU,hV,hyV,hsub⟩ := mem_nhds_prod_iff'.mp (hS.mem_nhds hxy)
  have hUpos := spherePrior_pos_of_open_unit hU hx hxU
  have hVpos := spherePrior_pos_of_open_unit hV hy hyV
  calc
    0 < Model.spherePrior N U*Model.spherePrior N V :=
      bot_lt_iff_ne_bot.mpr (mul_ne_zero hUpos.ne' hVpos.ne')
    _ = ((Model.spherePrior N).prod (Model.spherePrior N)) (U ×ˢ V) :=
      (Measure.prod_prod U V).symm
    _ ≤ _ := measure_mono hsub

theorem positiveWindowMass : Coupled.PositiveWindowMass := by
  intro N hN u hu eta heta
  obtain ⟨x,hx⟩ := Geometry.unitSphere_nonempty (by omega : 0 < N)
  obtain ⟨v,hv,heq⟩ := Geometry.sphereSlice_nonempty hN x hx u
    (by simpa only [abs_of_nonneg hu.1] using hu.2)
  apply spherePrior_product_pos_of_open_unit
    (isOpen_Ioo.preimage ((continuous_fst.inner continuous_snd : Continuous
      (fun xy : Model.Vector N × Model.Vector N ↦ inner ℝ xy.1 xy.2)).abs)) hv hx
  change |inner ℝ v x| ∈ Ioo (u-eta) (u+eta)
  rw [heq, abs_of_nonneg hu.1]
  constructor <;> linarith

end
end TensorPCA.WindowMassProofs
