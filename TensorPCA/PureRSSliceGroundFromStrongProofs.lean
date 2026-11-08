-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureLatitudeLowerMeanProofs
public import TensorPCA.PureLatitudeParametersProofs
public import TensorPCA.SliceGroundEndpointsProofs
public import TensorPCA.SliceGroundSymmetryProofs
public import TensorPCA.RetainedCountProofs.SphericalLatitudeWeakStrongFieldProofs

/-! The physical RS slice limit from an original-disorder exponential low-event bound, parameterized by the fixed-pure strict strong-field
probability family. Weak-boundary extension, lower mean,
finite upper mean, analytic RS value, signed symmetry and endpoints are proved
prerequisites. This conditional reduction is not an unconditional RS export. -/
@[expose] public section
namespace TensorPCA.PureRSSliceGroundFromStrongProofs
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open RetainedCountProofs SphericalModel SphericalGaussianJet SphericalLatitudeChartKacRice
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma rs_cutoff_pos (k : ℕ) (hk : 3 ≤ k) :
    0 < Real.sqrt (1-1/((k:ℝ)-1)) := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < (k:ℝ)-1 := by linarith
  have hfrac : 1/((k:ℝ)-1) < 1 := (div_lt_one hp).mpr (by linarith)
  exact Real.sqrt_pos.mpr (by linarith)

/-- The explicit strict probability family is a genuine intermediate claim
about the full original pure field. No physical mean or limit is a premise. -/
theorem sliceGroundLimit_rs_of_strong (k : ℕ) (hk : 3 ≤ k)
    (hStrong :
      let μ := FiniteMixture.pure k (by omega : 2 ≤ k) 1 zero_lt_one
      ∀ r : ℝ, r ∈ Ioo (0:ℝ) 1 →
        latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) 1) r <
          latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) 1) r →
        ∀ delta : ℝ, 0 < delta → ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ n : ℕ in atTop,
          ∀ w : Model.Vector (n+3), ‖w‖^2=(n+3:ℕ) →
          ∀ e : Model.Vector (n+2) →ₗᵢ[ℝ] Model.Vector (n+3), (∀ x, inner ℝ (e x) w=0) →
            disorderLaw (n+3) μ.maxDegree
              {J | ¬ ∃ y : Model.Vector (n+2), ‖y‖^2=(n+2:ℕ) ∧
                (n+3:ℕ)*(Real.sqrt (latitudeDerivativeVariance
                  (centerCoefficients (mixtureCoefficients μ) 1) r)-delta) <
                    field (centerCoefficients (mixtureCoefficients μ) 1) J (latitudeMap w e r y)} ≤
              2*ENNReal.ofReal (Real.exp (-eta*(n+3:ℕ))))
    (m : ℝ) (hm : m ∈ Icc (-1:ℝ) 1)
    (hlarge : Real.sqrt (1-1/((k:ℝ)-1)) ≤ |m|) :
    GroundState.SliceGroundLimit k m := by
  by_cases hend : m^2=1
  · exact SliceGroundEndpointsProofs.sliceGroundLimit_of_sq_eq_one k hend
  apply (SliceGroundSymmetryProofs.sliceGroundLimit_abs_iff k hm).mp
  have hq0 : 0 < |m| := (rs_cutoff_pos k hk).trans_le hlarge
  have hq1 : |m| < 1 := by
    have hle : |m| ≤ 1 := abs_le.mpr hm
    by_contra h
    have heq : |m|=1 := le_antisymm hle (le_of_not_gt h)
    apply hend
    nlinarith [sq_abs m]
  have hq : |m| ∈ Ioo (0:ℝ) 1 := ⟨hq0,hq1⟩
  have hqIcc : |m| ∈ Icc (-1:ℝ) 1 := ⟨by linarith,hq1.le⟩
  have hlargeQ : Real.sqrt (1-1/((k:ℝ)-1)) ≤ abs (abs m) := by
    simpa only [abs_abs] using hlarge
  let μ := FiniteMixture.pure k (by omega : 2 ≤ k) 1 zero_lt_one
  let g := Real.sqrt ((k:ℝ)*(1-|m|^2))
  have hpos : 0 < 1-|m|^2 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (show 0 < 1+|m| by linarith)]
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hg : 0 < g := by
    dsimp only [g]
    exact Real.sqrt_pos.mpr (mul_pos hkpos hpos)
  have hweak := PureLatitudeParametersProofs.pure_latitude_RS_criterion k hk hqIcc hlargeQ
  have hbad : ∀ delta : ℝ, 0 < delta → ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w : Model.Vector (n+3), ‖w‖^2=(n+3:ℕ) →
      ∀ e : Model.Vector (n+2) →ₗᵢ[ℝ] Model.Vector (n+3), (∀ x, inner ℝ (e x) w=0) →
        disorderLaw (n+3) μ.maxDegree
          {J | ∀ y : Model.Vector (n+2), ‖y‖^2=(n+2:ℕ) →
            field (centerCoefficients (mixtureCoefficients μ) 1) J (latitudeMap w e |m| y) ≤
              (n+3:ℕ)*(g-delta)} ≤ 3*ENNReal.ofReal (Real.exp (-eta*(n+3:ℕ))) := by
    intro delta hdelta
    obtain ⟨eta,heta,hbound⟩ := latitude_weakStrongField_maximum_lower_of_strong μ
      (Q := 1) zero_lt_one hStrong hq hweak hdelta
    refine ⟨eta,heta,?_⟩
    filter_upwards [hbound] with n hn
    intro w hw e he
    have hb := hn w hw e he
    rw [PureLatitudeParametersProofs.pure_latitudeDerivativeVariance] at hb
    apply (measure_mono ?_).trans hb
    intro J hJ hgood
    obtain ⟨y,hy,hyH⟩ := hgood
    exact not_lt_of_ge (hJ y hy) hyH
  have hlo (eps : ℝ) (heps : 0 < eps) : ∀ᶠ n : ℕ in atTop,
      g-eps ≤ GroundState.expectedSliceGround (n+1) k |m| :=
    PureLatitudeLowerMeanProofs.eventually_expectedSliceGround_lower_of_exponential_low
      k (by omega) hqIcc g hg hbad eps heps
  have hu (n : ℕ) : GroundState.expectedSliceGround (n+1) k |m| ≤ g :=
    GroundUpperProofs.expectedSliceGround_le (Nat.succ_pos n) hqIcc
  have hvalue : Scalar.variationalValue (Scalar.xiSlice k |m|) 0 = g :=
    GroundState.rsSlice_of_general RSVariationalProof.generalRSVariationalLaw
      VariationalProofs.slicePolynomialFacts k hk |m| hqIcc hlargeQ
  unfold GroundState.SliceGroundLimit
  rw [hvalue]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have heps : 0 < (g-a)/2 := by linarith
    filter_upwards [hlo ((g-a)/2) heps] with n hn
    linarith
  · intro b hb
    exact Eventually.of_forall fun n => (hu n).trans_lt hb

end
end TensorPCA.PureRSSliceGroundFromStrongProofs
