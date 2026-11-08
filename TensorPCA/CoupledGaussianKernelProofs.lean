-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.PairRegularityProofs
public import TensorPCA.CoupledInterpolationProofs
public import TensorPCA.WindowMassProofs
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Deriv

/-! Literal physical and common Gaussian kernels for the coupled interpolation.
The physical field retains the negative thermal sign. Signed-window estimates
below are not silently applied to the absolute-overlap window. -/

@[expose] public section
namespace TensorPCA.CoupledGaussianKernelProofs
open MeasureTheory ProbabilityTheory Set Filter PairRegularityProofs
open scoped Topology RealInnerProductSpace ENNReal BigOperators
noncomputable section

/-- Physical two-replica thermal linear field, including the actual strength. -/
def physicalLinear (N k : ℕ) (lam : ℝ) (xy : Model.Vector N × Model.Vector N) :
    Model.Tensor N k →L[ℝ] ℝ := lam • pairLinear N k xy

/-- Common auxiliary Gaussian vector acting on the sum of the two replicas. -/
def commonLinear (N : ℕ) (a : ℝ) (xy : Model.Vector N × Model.Vector N) :
    Model.Vector N →L[ℝ] ℝ := Real.sqrt ((N : ℝ)*a) • innerSL ℝ (xy.1+xy.2)

/-- The covariance computed in the actual canonical finite Gaussian coordinates. -/
def coordinateCovariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : EuclideanSpace ℝ ι →L[ℝ] ℝ) : ℝ :=
  ∑ i, A (EuclideanSpace.single i 1)*B (EuclideanSpace.single i 1)

/-- Exact coefficient vector of the physical field. -/
def physicalFeature (N k : ℕ) (lam : ℝ) (xy : Model.Vector N × Model.Vector N) :
    Model.Tensor N k := (-lam*Real.sqrt N) • (Model.feature k xy.1+Model.feature k xy.2)

theorem physicalLinear_eq_innerSL (N k : ℕ) (lam : ℝ) (xy : Model.Vector N × Model.Vector N) :
    physicalLinear N k lam xy = innerSL ℝ (physicalFeature N k lam xy) := by
  ext w
  simp only [physicalLinear, pairLinear, FreeEnergyProofs.thermalLinear,
    smul_apply, add_apply, innerSL_apply_apply,
    physicalFeature, real_inner_smul_left, inner_add_left, smul_eq_mul]
  ring

theorem commonLinear_eq_innerSL (N : ℕ) (a : ℝ) (xy : Model.Vector N × Model.Vector N) :
    commonLinear N a xy = innerSL ℝ (Real.sqrt ((N : ℝ)*a) • (xy.1+xy.2)) := by
  ext w
  simp only [commonLinear, smul_apply, innerSL_apply_apply,
    real_inner_smul_left, smul_eq_mul]

theorem coordinateCovariance_innerSL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : EuclideanSpace ℝ ι) :
    coordinateCovariance (innerSL ℝ x) (innerSL ℝ y) = inner ℝ x y := by
  simp only [coordinateCovariance, innerSL_apply_apply]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact ordered-tensor covariance of the actual physical pair field. -/
theorem physicalCovariance (N k : ℕ) (lam : ℝ)
    (xy zv : Model.Vector N × Model.Vector N) :
    coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam zv) =
      (N : ℝ)*lam^2*((inner ℝ xy.1 zv.1)^k+(inner ℝ xy.1 zv.2)^k+
        (inner ℝ xy.2 zv.1)^k+(inner ℝ xy.2 zv.2)^k) := by
  rw [physicalLinear_eq_innerSL, physicalLinear_eq_innerSL, coordinateCovariance_innerSL]
  simp only [physicalFeature, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, Geometry.feature_inner]
  calc
    _ = (Real.sqrt (N : ℝ))^2*lam^2*((inner ℝ xy.1 zv.1)^k+(inner ℝ xy.1 zv.2)^k+
      (inner ℝ xy.2 zv.1)^k+(inner ℝ xy.2 zv.2)^k) := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Exact canonical vector covariance of the common pair field. -/
theorem commonCovariance (N : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (xy zv : Model.Vector N × Model.Vector N) :
    coordinateCovariance (commonLinear N a xy) (commonLinear N a zv) =
      (N : ℝ)*a*(inner ℝ xy.1 zv.1+inner ℝ xy.1 zv.2+
        inner ℝ xy.2 zv.1+inner ℝ xy.2 zv.2) := by
  rw [commonLinear_eq_innerSL, commonLinear_eq_innerSL, coordinateCovariance_innerSL]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right]
  calc
    _ = (Real.sqrt ((N : ℝ)*a))^2*(inner ℝ xy.1 zv.1+inner ℝ xy.1 zv.2+
      inner ℝ xy.2 zv.1+inner ℝ xy.2 zv.2) := by ring
    _ = _ := by rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) ha)]

/-- Pointwise physical norm bound on the actual product unit sphere. -/
theorem physicalLinear_norm_le (N k : ℕ) (lam : ℝ)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1) :
    ‖physicalLinear N k lam xy‖ ≤ 2*|lam| *Real.sqrt N := by
  rw [physicalLinear_eq_innerSL, innerSL_apply_norm, physicalFeature, norm_smul,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (|lam| *Real.sqrt N)*(‖Model.feature k xy.1‖+‖Model.feature k xy.2‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [Geometry.feature_unit_norm _ hx, Geometry.feature_unit_norm _ hy]; ring

/-- Pointwise common-field norm bound on the actual product unit sphere. -/
theorem commonLinear_norm_le (N : ℕ) (a : ℝ)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1) :
    ‖commonLinear N a xy‖ ≤ 2*Real.sqrt ((N : ℝ)*a) := by
  rw [commonLinear_eq_innerSL, innerSL_apply_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt ((N : ℝ)*a)*(‖xy.1‖+‖xy.2‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ = _ := by rw [hx,hy]; ring

/-- Even powers lie above every actual real tangent, including negative
cross-overlaps. -/
theorem even_power_tangent (k : ℕ) (heven : Even k) (u r : ℝ) :
    (k : ℝ)*u^(k-1)*(r-u) ≤ r^k-u^k := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ ↦ x^k) := heven.convexOn_pow
  have hd := hasDerivAt_pow k u
  rcases lt_trichotomy u r with hlt | rfl | hlt
  · have H := hconv.le_slope_of_hasDerivAt (mem_univ u) (mem_univ r) hlt hd
    rw [slope_def_field] at H
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp H
  · simp
  · have H := hconv.slope_le_of_hasDerivAt (mem_univ r) (mem_univ u) hlt hd
    rw [slope_def_field] at H
    have hh := (div_le_iff₀ (sub_pos.mpr hlt)).mp H
    nlinarith

/-- The exact theta identity, rather than a hidden covariance normalization. -/
theorem theta_eq_tangent_constant {k : ℕ} (hk : 1 ≤ k) (lam u : ℝ) :
    Coupled.theta k lam u = Coupled.xiPrime k lam u*u-lam^2*u^k := by
  have hu : u^(k-1)*u = u^k := by rw [← pow_succ, Nat.sub_add_cancel hk]
  calc
    _ = lam^2*((k : ℝ)*u^k-u^k) := by unfold Coupled.theta; ring
    _ = lam^2*((k : ℝ)*(u^(k-1)*u)-u^k) := by rw [hu]
    _ = _ := by unfold Coupled.xiPrime; ring

/-- The actual pure-spin Bregman remainder is nonnegative on all real overlaps. -/
theorem scalar_covariance_tangent_le {k : ℕ} (hk : 1 ≤ k) (heven : Even k) (lam u r : ℝ) :
    Coupled.xiPrime k lam u*r-lam^2*r^k ≤ Coupled.theta k lam u := by
  rw [theta_eq_tangent_constant hk lam u]
  have H := mul_le_mul_of_nonneg_left (even_power_tangent k heven u r) (sq_nonneg lam)
  unfold Coupled.xiPrime
  nlinarith only [H]

/-- Even physical Gaussian covariance is nonnegative for arbitrary spin pairs. -/
theorem physicalCovariance_nonneg (N k : ℕ) (heven : Even k) (lam : ℝ)
    (xy zv : Model.Vector N × Model.Vector N) :
    0 ≤ coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam zv) := by
  rw [physicalCovariance]
  apply mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg lam))
  exact add_nonneg (add_nonneg (add_nonneg (heven.pow_nonneg _) (heven.pow_nonneg _))
    (heven.pow_nonneg _)) (heven.pow_nonneg _)

/-- Genuine cross-kernel comparison from convexity of the physical even power. -/
theorem common_sub_physical_le (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (heven : Even k)
    (lam : ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (xy zv : Model.Vector N × Model.Vector N) :
    coordinateCovariance (commonLinear N (Coupled.xiPrime k lam u) xy)
      (commonLinear N (Coupled.xiPrime k lam u) zv)-
      coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam zv) ≤
        4*(N : ℝ)*Coupled.theta k lam u := by
  have ha := (CoupledInterpolationProofs.trial_auxiliary_variances k lam u hu).1
  rw [commonCovariance N ha, physicalCovariance]
  have h11 := scalar_covariance_tangent_le (by omega : 1 ≤ k) heven lam u (inner ℝ xy.1 zv.1)
  have h12 := scalar_covariance_tangent_le (by omega : 1 ≤ k) heven lam u (inner ℝ xy.1 zv.2)
  have h21 := scalar_covariance_tangent_le (by omega : 1 ≤ k) heven lam u (inner ℝ xy.2 zv.1)
  have h22 := scalar_covariance_tangent_le (by omega : 1 ≤ k) heven lam u (inner ℝ xy.2 zv.2)
  have H := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h11 h12) h21) h22)
    (Nat.cast_nonneg (α := ℝ) N)
  nlinarith only [H]

theorem physicalLinear_continuous (N k : ℕ) (lam : ℝ) : Continuous (physicalLinear N k lam) :=
  (pairLinear_continuous N k).const_smul lam

theorem commonLinear_continuous (N : ℕ) (a : ℝ) : Continuous (commonLinear N a) :=
  ((innerSL ℝ).continuous.comp (continuous_fst.add continuous_snd)).const_smul (Real.sqrt ((N : ℝ)*a))

theorem physicalLinear_apply (N k : ℕ) (lam : ℝ) (xy : Model.Vector N × Model.Vector N)
    (w : Model.Tensor N k) :
    physicalLinear N k lam xy w = -lam*(Model.hamiltonian w xy.1+Model.hamiltonian w xy.2) := by
  calc
    _ = pairLinear N k xy (lam • w) := by simp only [physicalLinear, smul_apply, map_smul, smul_eq_mul]
    _ = _ := pairLinear_apply N k lam xy w

/-- Actual diagonal physical covariance on unit pairs. -/
theorem physicalCovariance_diagonal (N k : ℕ) (lam : ℝ)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1) :
    coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam xy) =
      2*(N : ℝ)*lam^2*(1+(inner ℝ xy.1 xy.2)^k) := by
  rw [physicalCovariance]
  simp only [real_inner_self_eq_norm_sq, hx, hy, one_pow, real_inner_comm xy.2 xy.1]
  ring

/-- Actual diagonal common covariance on unit pairs. -/
theorem commonCovariance_diagonal (N : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1) :
    coordinateCovariance (commonLinear N a xy) (commonLinear N a xy) =
      2*(N : ℝ)*a*(1+inner ℝ xy.1 xy.2) := by
  rw [commonCovariance N ha]
  simp only [real_inner_self_eq_norm_sq, hx, hy, one_pow, real_inner_comm xy.2 xy.1]
  ring

/-- The exact elementary power Lipschitz estimate on [-1,1]. -/
theorem abs_pow_sub_pow_unit_le (k : ℕ) {r u : ℝ} (hr : |r| ≤ 1) (hu : |u| ≤ 1) :
    |r^k-u^k| ≤ (k : ℝ)*|r-u| := by
  have hmax : max |r| |u| ≤ 1 := max_le hr hu
  have hp : max |r| |u|^(k-1) ≤ 1 := pow_le_one₀ ((abs_nonneg r).trans (le_max_left _ _)) hmax
  exact (abs_pow_sub_pow_le (a := r) (b := u) (n := k)).trans
    ((mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg k))).trans_eq (by ring))

/-- Explicit scalar covariance error at a signed overlap r close to u. -/
theorem scalar_covariance_error_le {k : ℕ} (hk : 1 ≤ k) (lam : ℝ)
    {u r : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hr : |r| ≤ 1) :
    |Coupled.xiPrime k lam u*r-lam^2*r^k-Coupled.theta k lam u| ≤
      2*Coupled.xiPrime k lam 1*|r-u| := by
  have ha := CoupledInterpolationProofs.trial_auxiliary_variances k lam u hu
  have hp := abs_pow_sub_pow_unit_le k hr (by rw [abs_of_nonneg hu.1]; exact hu.2)
  have hd : Coupled.xiPrime k lam 1 = (k : ℝ)*lam^2 := by simp only [Coupled.xiPrime, one_pow, mul_one]
  rw [theta_eq_tangent_constant hk lam u]
  have heq : Coupled.xiPrime k lam u*r-lam^2*r^k-(Coupled.xiPrime k lam u*u-lam^2*u^k) =
      Coupled.xiPrime k lam u*(r-u)-lam^2*(r^k-u^k) := by ring
  rw [heq]
  calc
    _ ≤ |Coupled.xiPrime k lam u*(r-u)|+|lam^2*(r^k-u^k)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (Coupled.xiPrime k lam u*(r-u)) 0 (lam^2*(r^k-u^k))
    _ = Coupled.xiPrime k lam u*|r-u|+lam^2*|r^k-u^k| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha.1, abs_of_nonneg (sq_nonneg lam)]
    _ ≤ Coupled.xiPrime k lam 1*|r-u|+lam^2*((k : ℝ)*|r-u|) :=
      add_le_add (mul_le_mul_of_nonneg_right ha.2 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hp (sq_nonneg lam))
    _ = _ := by rw [hd]; ring

/-- The signed overlap window used by the actual common field. -/
def signedPairWindow (N : ℕ) (u eta : ℝ) : Set (Model.Vector N × Model.Vector N) :=
  {xy | |inner ℝ xy.1 xy.2-u| < eta}

theorem isOpen_signedPairWindow (N : ℕ) (u eta : ℝ) : IsOpen (signedPairWindow N u eta) := by
  apply isOpen_lt _ continuous_const
  exact (((continuous_fst.inner continuous_snd).sub continuous_const).abs :
    Continuous (fun xy : Model.Vector N × Model.Vector N ↦ |inner ℝ xy.1 xy.2-u|))

/-- Every positive-width signed physical window has genuine positive mass in
N≥2. This is separate from the frozen absolute-overlap window. -/
theorem signedPairWindow_mass_pos {N : ℕ} (hN : 2 ≤ N) {u eta : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (heta : 0 < eta) :
    0 < ((Model.spherePrior N).prod (Model.spherePrior N)) (signedPairWindow N u eta) := by
  obtain ⟨x,hx⟩ := Geometry.unitSphere_nonempty (by omega : 0 < N)
  obtain ⟨v,hv,heq⟩ := Geometry.sphereSlice_nonempty hN x hx u (by rw [abs_of_nonneg hu.1]; exact hu.2)
  apply WindowMassProofs.spherePrior_product_pos_of_open_unit (isOpen_signedPairWindow N u eta) hv hx
  change |inner ℝ v x-u| < eta
  rw [heq, sub_self, abs_zero]
  exact heta

/-- Explicit signed-window diagonal bound for the actual interpolation kernels. -/
theorem signed_window_diagonal_lower (N : ℕ) {k : ℕ} (hk : 2 ≤ k)
    (lam : ℝ) {u eta : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (xy : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1)
    (hwin : xy ∈ signedPairWindow N u eta) :
    2*(N : ℝ)*(Coupled.theta k lam 1+Coupled.theta k lam u)-
      4*(N : ℝ)*Coupled.xiPrime k lam 1*eta ≤
      coordinateCovariance (commonLinear N (Coupled.xiPrime k lam u) xy)
        (commonLinear N (Coupled.xiPrime k lam u) xy)-
      coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam xy)+
        2*(N : ℝ)*(Coupled.xiPrime k lam 1-Coupled.xiPrime k lam u) := by
  have ha := CoupledInterpolationProofs.trial_auxiliary_variances k lam u hu
  have hd : 0 ≤ Coupled.xiPrime k lam 1 := ha.1.trans ha.2
  have hr : |inner ℝ xy.1 xy.2| ≤ 1 := by simpa only [hx,hy,one_mul] using abs_real_inner_le_norm xy.1 xy.2
  have herror := (scalar_covariance_error_le (by omega : 1 ≤ k) lam hu hr).trans
    (mul_le_mul_of_nonneg_left (show |inner ℝ xy.1 xy.2-u| ≤ eta from hwin.le)
      (mul_nonneg (by norm_num) hd))
  have hlo := (abs_le.mp herror).1
  have ht1 := theta_eq_tangent_constant (by omega : 1 ≤ k) lam 1
  simp only [one_pow, mul_one] at ht1
  rw [commonCovariance_diagonal N ha.1 xy hx hy, physicalCovariance_diagonal N k lam xy hx hy, ht1]
  have H := mul_le_mul_of_nonneg_left hlo (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg N))
  nlinarith only [H]

/-- The complete pointwise trace lower bound used by the true angular
interpolation derivative. Independent physical replicas contribute nonnegatively. -/
theorem signed_window_trace_lower (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (heven : Even k)
    (lam : ℝ) {u eta p : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (1/2 : ℝ) 1)
    (xy zv ab cd : Model.Vector N × Model.Vector N) (hx : ‖xy.1‖ = 1) (hy : ‖xy.2‖ = 1)
    (hwin : xy ∈ signedPairWindow N u eta) :
    2*(N : ℝ)*(Coupled.theta k lam 1+(2*p-1)*Coupled.theta k lam u)-
      4*(N : ℝ)*Coupled.xiPrime k lam 1*eta ≤
      coordinateCovariance (commonLinear N (Coupled.xiPrime k lam u) xy)
        (commonLinear N (Coupled.xiPrime k lam u) xy)-
      coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam xy)-
      (1-p)*(coordinateCovariance (commonLinear N (Coupled.xiPrime k lam u) xy)
        (commonLinear N (Coupled.xiPrime k lam u) zv)-
        coordinateCovariance (physicalLinear N k lam xy) (physicalLinear N k lam zv))+
      p*coordinateCovariance (physicalLinear N k lam ab) (physicalLinear N k lam cd)+
        2*(N : ℝ)*(Coupled.xiPrime k lam 1-Coupled.xiPrime k lam u) := by
  have hdiag := signed_window_diagonal_lower N hk lam hu xy hx hy hwin
  have hcross := mul_le_mul_of_nonneg_left (common_sub_physical_le N hk heven lam hu xy zv)
    (sub_nonneg.mpr hp.2)
  have hphys : 0 ≤ p*coordinateCovariance (physicalLinear N k lam ab) (physicalLinear N k lam cd) :=
    mul_nonneg (by linarith [hp.1]) (physicalCovariance_nonneg N k heven lam ab cd)
  nlinarith only [hdiag,hcross,hphys]

end
end TensorPCA.CoupledGaussianKernelProofs
