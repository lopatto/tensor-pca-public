-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceLaw
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellLinearPartition
public import TensorPCA.RetainedCountProofs.GaussianShell

/-! Retained radial masses: finite strict positivity, and convergence of the bulk
radius-box mass and its unnormalized logarithm to one and zero.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityRetainedMass
open MeasureTheory ProbabilityTheory Set Filter
open FiniteCavityReferenceLaw FiniteCavityShellLinearPartition
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def radiusBox (N : ℕ) (e : ℝ) : Set ℝ := {r | r^2/(N : ℝ)∈Icc (1-e) (1+e)}

def radiusBoxMass (N : ℕ) (e : ℝ) : ℝ := (radiusLaw N).real (radiusBox N e)

def annulusMass (M : ℕ) (delta : ℝ) : ℝ := (stdGaussian (Model.Vector M)).real (gaussianAnnulus M delta)

theorem radiusBox_measurableSet (N : ℕ) (e : ℝ) : MeasurableSet (radiusBox N e) :=
  isClosed_Icc.measurableSet.preimage ((continuous_id.pow 2).div_const (N : ℝ)).measurable

theorem radiusBoxMass_eq_gaussian (N : ℕ) (e : ℝ) :
    radiusBoxMass N e=(stdGaussian (Model.Vector N)).real {x | ‖x‖^2/(N : ℝ)∈Icc (1-e) (1+e)} := by
  unfold radiusBoxMass radiusLaw Measure.real
  rw [Measure.map_apply measurable_norm (radiusBox_measurableSet N e)]
  rfl

theorem radiusBoxMass_le_one (N : ℕ) (e : ℝ) : radiusBoxMass N e≤1 := measureReal_le_one
theorem annulusMass_le_one (M : ℕ) (delta : ℝ) : annulusMass M delta≤1 := measureReal_le_one
theorem annulusMass_nonneg (M : ℕ) (delta : ℝ) : 0≤annulusMass M delta := ENNReal.toReal_nonneg

private theorem gaussian_open_pos (N : ℕ) : Measure.IsOpenPosMeasure (stdGaussian (Model.Vector N)) := by
  have hac : (volume : Measure (Model.Vector N))≪stdGaussian (Model.Vector N) := by
    rw [GaussianDensityProofs.stdGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous'
      GaussianDensityProofs.density_continuous.measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun x => (ENNReal.ofReal_pos.mpr (GaussianDensityProofs.density_pos x)).ne')
  exact hac.isOpenPosMeasure

theorem radiusBoxMass_pos {N : ℕ} (hN : 0<N) {e : ℝ} (he : 0<e) : 0<radiusBoxMass N e := by
  letI := gaussian_open_pos N
  obtain ⟨u,hu⟩ := Geometry.unitSphere_nonempty hN
  let x := Real.sqrt (N : ℝ) • u
  have hx : ‖x‖^2/(N : ℝ)=1 := by
    dsimp [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),show ‖u‖=1 from hu,
      mul_one,Real.sq_sqrt (Nat.cast_nonneg N),div_self (by positivity : (N : ℝ)≠0)]
  let U : Set (Model.Vector N) := {x | ‖x‖^2/(N : ℝ)∈Ioo (1-e) (1+e)}
  have hU : IsOpen U := isOpen_Ioo.preimage ((continuous_norm.pow 2).div_const (N : ℝ))
  have hxU : x∈U := by change ‖x‖^2/(N : ℝ)∈Ioo (1-e) (1+e); rw [hx]; constructor <;> linarith
  have hpos := hU.measure_pos (stdGaussian (Model.Vector N)) ⟨x,hxU⟩
  have hsub : U⊆{x : Model.Vector N | ‖x‖^2/(N : ℝ)∈Icc (1-e) (1+e)} :=
    fun _ hx => ⟨hx.1.le,hx.2.le⟩
  rw [radiusBoxMass_eq_gaussian]
  exact ENNReal.toReal_pos_iff.mpr ⟨hpos.trans_le (measure_mono hsub),measure_lt_top _ _⟩

theorem annulusMass_pos {M : ℕ} (hM : 0<M) {delta : ℝ} (hdelta : 0<delta) : 0<annulusMass M delta := by
  letI := gaussian_open_pos M
  obtain ⟨u,hu⟩ := Geometry.unitSphere_nonempty hM
  let x := Real.sqrt ((M : ℝ)*(1+delta/2)) • u
  have hx : ‖x‖^2=(M : ℝ)*(1+delta/2) := by
    dsimp [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),show ‖u‖=1 from hu,
      mul_one,Real.sq_sqrt (by positivity)]
  let U : Set (Model.Vector M) := {x | ‖x‖^2∈Ioo (M : ℝ) ((M : ℝ)*(1+delta))}
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_norm.pow 2)
  have hxU : x∈U := by
    change ‖x‖^2∈Ioo (M : ℝ) ((M : ℝ)*(1+delta))
    rw [hx]
    constructor <;> nlinarith only [mul_pos (Nat.cast_pos.mpr hM) hdelta]
  have hpos := hU.measure_pos (stdGaussian (Model.Vector M)) ⟨x,hxU⟩
  have hsub : U⊆gaussianAnnulus M delta := fun _ hx => ⟨hx.1.le,hx.2.le⟩
  exact ENNReal.toReal_pos_iff.mpr ⟨hpos.trans_le (measure_mono hsub),measure_lt_top _ _⟩

theorem exponential_dimension_decay {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)*c)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hc)

theorem radiusBoxMass_tendsto_one {e : ℝ} (he : 0<e) :
    Tendsto (fun N : ℕ => radiusBoxMass N e) atTop (𝓝 1) := by
  let d := min e (1/2 : ℝ)
  have hd : 0<d := lt_min he (by norm_num)
  have hdhalf : d≤1/2 := min_le_right _ _
  have hde : d≤e := min_le_left _ _
  have ha : 0<1-d := by linarith only [hdhalf]
  have ha1 : 1-d<1 := by linarith only [hd]
  have hb : 1<1+d := by linarith only [hd]
  have hA := exponential_dimension_decay (RetainedCountProofs.GaussianShell.rate_pos ha ha1.ne)
  have hB := exponential_dimension_decay (RetainedCountProofs.GaussianShell.rate_pos (by linarith only [hb]) hb.ne')
  have hLower : Tendsto (fun N : ℕ => 1-Real.exp (-(N : ℝ)*RetainedCountProofs.GaussianShell.rate (1-d))-
      Real.exp (-(N : ℝ)*RetainedCountProofs.GaussianShell.rate (1+d))) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hA).sub hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower tendsto_const_nhds _
    (.of_forall fun N => radiusBoxMass_le_one N e)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have H := RetainedCountProofs.GaussianShell.shell_mass_lower (E := Model.Vector N) ha ha1 hb
  simp only [finrank_euclideanSpace,Fintype.card_fin] at H
  rw [radiusBoxMass_eq_gaussian]
  apply H.trans (measureReal_mono _)
  intro x hx
  constructor
  · apply (le_div_iff₀ hn).2
    nlinarith only [hx.1,mul_le_mul_of_nonneg_right hde hn.le]
  · apply (div_le_iff₀ hn).2
    nlinarith only [hx.2,mul_le_mul_of_nonneg_right hde hn.le]

theorem log_radiusBoxMass_tendsto_zero {e : ℝ} (he : 0<e) :
    Tendsto (fun N : ℕ => Real.log (radiusBoxMass N e)) atTop (𝓝 0) := by
  simpa only [Real.log_one] using (radiusBoxMass_tendsto_one he).log one_ne_zero


end
end TensorPCA.NonRSLowerProofs.FiniteCavityRetainedMass
