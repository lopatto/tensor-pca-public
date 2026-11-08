-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianMomentProofs
public import TensorPCA.CoupledMatrixProofs
public import Mathlib.MeasureTheory.Integral.Prod

/-! Gaussian endpoint integrals for the coupled trial. Positive precision
is the only quadratic integrability restriction; quadratic coefficients may
have either sign. -/
@[expose] public section
namespace TensorPCA.CoupledGaussianIntegralProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def scaledStdGaussian (N : ℕ) (b : ℝ) : Measure (Model.Vector N) :=
  (stdGaussian (Model.Vector N)).map (fun g => (Real.sqrt b)⁻¹ • g)

instance scaledStdGaussian_probability (N : ℕ) (b : ℝ) :
    IsProbabilityMeasure (scaledStdGaussian N b) := by
  unfold scaledStdGaussian
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

theorem scaled_quadratic_identity (N : ℕ) {b c : ℝ} (hb : 0 < b)
    (v x : Model.Vector N) :
    inner ℝ v ((Real.sqrt b)⁻¹ • x)+c/2*‖(Real.sqrt b)⁻¹ • x‖^2 =
      inner ℝ ((Real.sqrt b)⁻¹ • v) x-((b-c)/b-1)/2*‖x‖^2 := by
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hss : ((Real.sqrt b)⁻¹)^2 = b⁻¹ := by
    rw [inv_pow,Real.sq_sqrt hb.le]
  rw [real_inner_smul_right,real_inner_smul_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hss]
  field_simp
  ring

theorem scaled_integrable_exp_quadratic (N : ℕ) {b c : ℝ} (hb : 0 < b)
    (hc : c < b) (v : Model.Vector N) :
    Integrable (fun x => Real.exp (inner ℝ v x+c/2*‖x‖^2)) (scaledStdGaussian N b) := by
  have hf : AEStronglyMeasurable (fun x : Model.Vector N =>
      Real.exp (inner ℝ v x+c/2*‖x‖^2)) (scaledStdGaussian N b) := by fun_prop
  unfold scaledStdGaussian at hf ⊢
  apply (integrable_map_measure hf
    (show AEMeasurable (fun x : Model.Vector N => (Real.sqrt b)⁻¹ • x)
      (stdGaussian (Model.Vector N)) by fun_prop)).2
  have hi := GaussianMomentProofs.integrable_exp_quadratic (E := Model.Vector N)
    (div_pos (sub_pos.mpr hc) hb) ((Real.sqrt b)⁻¹ • v)
  change Integrable (fun x : Model.Vector N => Real.exp
    (inner ℝ v ((Real.sqrt b)⁻¹ • x)+c/2*‖(Real.sqrt b)⁻¹ • x‖^2)) _
  simp_rw [scaled_quadratic_identity N hb]
  exact hi

theorem scaled_integral_exp_quadratic (N : ℕ) {b c : ℝ} (hb : 0 < b)
    (hc : c < b) (v : Model.Vector N) :
    (∫ x, Real.exp (inner ℝ v x+c/2*‖x‖^2) ∂scaledStdGaussian N b) =
      ((b-c)/b)^(-((N : ℝ)/2))*Real.exp (‖v‖^2/(2*(b-c))) := by
  rw [scaledStdGaussian,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [scaled_quadratic_identity N hb]
  rw [GaussianMomentProofs.integral_exp_quadratic (div_pos (sub_pos.mpr hc) hb)]
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hss : ((Real.sqrt b)⁻¹)^2 = b⁻¹ := by rw [inv_pow,Real.sq_sqrt hb.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hss]
  congr 2
  field_simp

def pairWeight (N : ℕ) (c L : ℝ) (v : Model.Vector N)
    (xy : Model.Vector N × Model.Vector N) : ℝ :=
  Real.exp (inner ℝ v (xy.1+xy.2)+c/2*(‖xy.1‖^2+‖xy.2‖^2)+L*inner ℝ xy.1 xy.2)

def pairMoment (N : ℕ) (b c L : ℝ) (v : Model.Vector N) : ℝ :=
  ∫ xy, pairWeight N c L v xy ∂(scaledStdGaussian N b).prod (scaledStdGaussian N b)

theorem pairWeight_factor (N : ℕ) (c L : ℝ) (v x y : Model.Vector N) :
    pairWeight N c L v (x,y) =
      Real.exp (inner ℝ v x+c/2*‖x‖^2)*
        Real.exp (inner ℝ (v+L • x) y+c/2*‖y‖^2) := by
  rw [← Real.exp_add]
  unfold pairWeight
  congr 1
  rw [inner_add_right,inner_add_left,real_inner_smul_left]
  ring

theorem pairWeight_inner_integrable (N : ℕ) {b c : ℝ} (hb : 0 < b)
    (hc : c < b) (L : ℝ) (v x : Model.Vector N) :
    Integrable (fun y => pairWeight N c L v (x,y)) (scaledStdGaussian N b) := by
  simp_rw [pairWeight_factor]
  exact (scaled_integrable_exp_quadratic N hb hc (v+L • x)).const_mul _

theorem pairWeight_inner_integral (N : ℕ) {b c : ℝ} (hb : 0 < b)
    (hc : c < b) (L : ℝ) (v x : Model.Vector N) :
    (∫ y, pairWeight N c L v (x,y) ∂scaledStdGaussian N b) =
      ((b-c)/b)^(-((N : ℝ)/2))*
        Real.exp (inner ℝ v x+c/2*‖x‖^2+‖v+L • x‖^2/(2*(b-c))) := by
  simp_rw [pairWeight_factor]
  rw [integral_const_mul,scaled_integral_exp_quadratic N hb hc]
  simp_rw [Real.exp_add]
  ring

theorem pairWeight_outer_exponent (N : ℕ) {b c : ℝ} (hc : c < b)
    (L : ℝ) (v x : Model.Vector N) :
    inner ℝ v x+c/2*‖x‖^2+‖v+L • x‖^2/(2*(b-c)) =
      ‖v‖^2/(2*(b-c))+inner ℝ ((1+L/(b-c)) • v) x+
        (c+L^2/(b-c))/2*‖x‖^2 := by
  rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_right,real_inner_smul_left]
  field_simp [(sub_pos.mpr hc).ne']
  ring

theorem effective_quadratic_lt {b c L : ℝ} (hL : 0 ≤ L) (hmargin : 0 < b-c-L) :
    c+L^2/(b-c) < b := by
  have hP : 0 < b-c := by linarith
  have hmul : L^2 < (b-c)^2 := by nlinarith
  have H : L^2/(b-c) < b-c := (div_lt_iff₀ hP).mpr (by nlinarith [hmul])
  linarith

theorem pairWeight_inner_integral_factor (N : ℕ) {b c : ℝ} (hb : 0 < b)
    (hc : c < b) (L : ℝ) (v x : Model.Vector N) :
    (∫ y, pairWeight N c L v (x,y) ∂scaledStdGaussian N b) =
      (((b-c)/b)^(-((N : ℝ)/2))*Real.exp (‖v‖^2/(2*(b-c))))*
        Real.exp (inner ℝ ((1+L/(b-c)) • v) x+(c+L^2/(b-c))/2*‖x‖^2) := by
  rw [pairWeight_inner_integral N hb hc,pairWeight_outer_exponent N hc]
  simp_rw [Real.exp_add]
  ring

theorem pairWeight_integrable (N : ℕ) {b c L : ℝ} (hb : 0 < b) (hL : 0 ≤ L)
    (hmargin : 0 < b-c-L) (v : Model.Vector N) :
    Integrable (pairWeight N c L v) ((scaledStdGaussian N b).prod (scaledStdGaussian N b)) := by
  have hc : c < b := by linarith
  have hC := effective_quadratic_lt hL hmargin
  have hm : AEStronglyMeasurable (pairWeight N c L v)
      ((scaledStdGaussian N b).prod (scaledStdGaussian N b)) := by
    unfold pairWeight
    fun_prop
  apply (integrable_prod_iff hm).2
  refine ⟨Eventually.of_forall (fun x => pairWeight_inner_integrable N hb hc L v x),?_⟩
  have hn (xy : Model.Vector N × Model.Vector N) : ‖pairWeight N c L v xy‖ = pairWeight N c L v xy := by
    rw [Real.norm_eq_abs,abs_of_pos]
    exact Real.exp_pos _
  simp_rw [hn,pairWeight_inner_integral_factor N hb hc]
  exact (scaled_integrable_exp_quadratic N hb hC ((1+L/(b-c)) • v)).const_mul _

theorem pairMoment_eq_sequential (N : ℕ) {b c L : ℝ} (hb : 0 < b) (hL : 0 ≤ L)
    (hmargin : 0 < b-c-L) (v : Model.Vector N) :
    pairMoment N b c L v =
      ((b-c)/b)^(-((N : ℝ)/2))*
        ((b-(c+L^2/(b-c)))/b)^(-((N : ℝ)/2))*
          Real.exp (‖v‖^2/(2*(b-c))+
            ‖(1+L/(b-c)) • v‖^2/(2*(b-(c+L^2/(b-c))))) := by
  have hc : c < b := by linarith
  rw [pairMoment,integral_prod _ (pairWeight_integrable N hb hL hmargin v)]
  simp_rw [pairWeight_inner_integral_factor N hb hc]
  rw [integral_const_mul,scaled_integral_exp_quadratic N hb (effective_quadratic_lt hL hmargin)]
  rw [Real.exp_add]
  ring

theorem pairMoment_eq (N : ℕ) {b c L : ℝ} (hb : 0 < b) (hL : 0 ≤ L)
    (hmargin : 0 < b-c-L) (v : Model.Vector N) :
    pairMoment N b c L v =
      b^N/((b-c)^2-L^2)^((N : ℝ)/2)*Real.exp (‖v‖^2/(b-c-L)) := by
  have hc : c < b := by linarith
  have hP : 0 < b-c := sub_pos.mpr hc
  have hQ : 0 < b-c+L := by linarith
  have hC : 0 < b-(c+L^2/(b-c)) := sub_pos.mpr (effective_quadratic_lt hL hmargin)
  have hdet : 0 < (b-c)^2-L^2 := by nlinarith [mul_pos hmargin hQ]
  have hA : 0 < (b-c)/b := div_pos hP hb
  have hB : 0 < (b-(c+L^2/(b-c)))/b := div_pos hC hb
  have hprod : (b-c)/b*((b-(c+L^2/(b-c)))/b) = ((b-c)^2-L^2)/b^2 := by
    field_simp
    ring
  have hlog : Real.log ((b-c)/b)+Real.log ((b-(c+L^2/(b-c)))/b) =
      Real.log ((b-c)^2-L^2)-2*Real.log b := by
    rw [← Real.log_mul hA.ne' hB.ne',hprod,
      Real.log_div hdet.ne' (sq_pos_of_pos hb).ne',Real.log_pow]
    norm_num
  have hfac : ((b-c)/b)^(-((N : ℝ)/2))*
      ((b-(c+L^2/(b-c)))/b)^(-((N : ℝ)/2)) =
      b^N/((b-c)^2-L^2)^((N : ℝ)/2) := by
    rw [← Real.rpow_natCast b N,Real.rpow_def_of_pos hb,Real.rpow_def_of_pos hdet,
      Real.rpow_def_of_pos hA,Real.rpow_def_of_pos hB,← Real.exp_add,← Real.exp_sub]
    congr 1
    nlinarith [hlog]
  have hexp : ‖v‖^2/(2*(b-c))+
      ‖(1+L/(b-c)) • v‖^2/(2*(b-(c+L^2/(b-c)))) = ‖v‖^2/(b-c-L) := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    have hCeq : b-(c+L^2/(b-c)) = ((b-c)^2-L^2)/(b-c) := by
      field_simp
      ring
    rw [hCeq]
    field_simp [hP.ne',hdet.ne',hmargin.ne']
    ring
  rw [pairMoment_eq_sequential N hb hL hmargin,hfac,hexp]

def endpointMoment (N : ℕ) (a d L : ℝ) (g : Model.Vector N) : ℝ :=
  pairMoment N (1+d) (d-a) L (Real.sqrt a • g)

def endpointPrefactor (N : ℕ) (a d L : ℝ) : ℝ :=
  (1+d)^N/(CoupledMatrixProofs.A3 a L).det^((N : ℝ)/2)

theorem endpointMoment_eq_integral (N : ℕ) (a d L : ℝ) (g : Model.Vector N) :
    endpointMoment N a d L g = ∫ xy : Model.Vector N × Model.Vector N,
      Real.exp (Real.sqrt a*inner ℝ g (xy.1+xy.2)+
        (d-a)/2*(‖xy.1‖^2+‖xy.2‖^2)+L*inner ℝ xy.1 xy.2)
      ∂(scaledStdGaussian N (1+d)).prod (scaledStdGaussian N (1+d)) := by
  unfold endpointMoment pairMoment pairWeight
  simp only [real_inner_smul_left]

theorem endpointPrefactor_pos (N : ℕ) {a d L : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hP : 0 < 1+a-L) : 0 < endpointPrefactor N a d L := by
  unfold endpointPrefactor
  rw [CoupledMatrixProofs.A3_det]
  exact div_pos (pow_pos (by linarith) _)
    (Real.rpow_pos_of_pos (mul_pos hP (by linarith)) _)

theorem endpointMoment_eq (N : ℕ) {a d L : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hP : 0 < 1+a-L) (g : Model.Vector N) :
    endpointMoment N a d L g =
      endpointPrefactor N a d L*Real.exp (a*‖g‖^2/(1+a-L)) := by
  rw [endpointMoment,pairMoment_eq N (by linarith : 0 < 1+d) hL (by linarith)]
  have he : 1+d-(d-a) = 1+a := by ring
  rw [he]
  unfold endpointPrefactor
  rw [CoupledMatrixProofs.A3_det]
  have hdet : (1+a)^2-L^2 = (1+a-L)*(1+a+L) := by ring
  rw [hdet,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt ha]

theorem endpointMoment_integrable (N : ℕ) {a d L : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hP : 0 < 1+a-L) (g : Model.Vector N) :
    Integrable (pairWeight N (d-a) L (Real.sqrt a • g))
      ((scaledStdGaussian N (1+d)).prod (scaledStdGaussian N (1+d))) :=
  pairWeight_integrable N (by linarith) hL (by linarith) _

theorem endpointMoment_pos (N : ℕ) {a d L : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hP : 0 < 1+a-L) (g : Model.Vector N) :
    0 < endpointMoment N a d L g := by
  rw [endpointMoment_eq N ha hd hL hP]
  exact mul_pos (endpointPrefactor_pos N ha hd hL hP) (Real.exp_pos _)

theorem endpoint_outer_factor (N : ℕ) {a d L : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hP : 0 < 1+a-L) (p : ℝ) (g : Model.Vector N) :
    Real.exp (p*Real.log (endpointMoment N a d L g)) =
      (endpointPrefactor N a d L)^p*Real.exp ((p*a/(1+a-L))*‖g‖^2) := by
  rw [endpointMoment_eq N ha hd hL hP,
    Real.log_mul (endpointPrefactor_pos N ha hd hL hP).ne' (Real.exp_ne_zero _),
    Real.log_exp,Real.rpow_def_of_pos (endpointPrefactor_pos N ha hd hL hP)]
  rw [← Real.exp_add]
  congr 1
  ring

theorem endpoint_outer_integrable (N : ℕ) {a d L m : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L) :
    Integrable (fun g => Real.exp ((m/2)*Real.log (endpointMoment N a d L g)))
      (stdGaussian (Model.Vector N)) := by
  have hP : 0 < 1+a-L := by nlinarith
  have ht : (m/2)*a/(1+a-L) < 1/2 := (div_lt_iff₀ hP).mpr (by nlinarith)
  simp_rw [endpoint_outer_factor N ha hd hL hP]
  exact (GaussianMomentProofs.integrable_exp_norm_sq (E := Model.Vector N) ht).const_mul _

theorem endpoint_outer_integral (N : ℕ) {a d L m : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L) :
    (∫ g, Real.exp ((m/2)*Real.log (endpointMoment N a d L g))
      ∂stdGaussian (Model.Vector N)) =
      (endpointPrefactor N a d L)^(m/2)*
        ((1+a-L)/(1+(1-m)*a-L))^((N : ℝ)/2) := by
  have hP : 0 < 1+a-L := by nlinarith
  have ht : (m/2)*a/(1+a-L) < 1/2 := (div_lt_iff₀ hP).mpr (by nlinarith)
  simp_rw [endpoint_outer_factor N ha hd hL hP]
  rw [integral_const_mul,GaussianMomentProofs.integral_exp_norm_sq ht]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  have he : 1-2*((m/2)*a/(1+a-L)) = (1+(1-m)*a-L)/(1+a-L) := by
    field_simp
    ring
  rw [he,Real.rpow_neg_eq_inv_rpow,inv_div]

theorem endpoint_outer_log_normalized {N : ℕ} (hN : 0 < N)
    {a d L m : ℝ} (ha : 0 ≤ a) (hd : a ≤ d)
    (hL : 0 ≤ L) (hm : 1 ≤ m) (hmargin : 0 < 1+(1-m)*a-L) :
    Real.log (∫ g, Real.exp ((m/2)*Real.log (endpointMoment N a d L g))
      ∂stdGaussian (Model.Vector N))/(m/2)/(N : ℝ) =
      Real.log (1+d)-(1/2 : ℝ)*Real.log (CoupledMatrixProofs.A3 a L).det+
        (1/m)*Real.log ((1+a-L)/(1+(1-m)*a-L)) := by
  have hb : 0 < 1+d := by linarith
  have hP : 0 < 1+a-L := by nlinarith
  have hdet : 0 < (CoupledMatrixProofs.A3 a L).det := by
    rw [CoupledMatrixProofs.A3_det]
    exact mul_pos hP (by linarith)
  have hK := endpointPrefactor_pos N ha hd hL hP
  have hratio := div_pos hP hmargin
  have hm0 : m ≠ 0 := by linarith
  have hN0 : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  rw [endpoint_outer_integral N ha hd hL hm hmargin,
    Real.log_mul (Real.rpow_pos_of_pos hK _).ne' (Real.rpow_pos_of_pos hratio _).ne',
    Real.log_rpow hK,Real.log_rpow hratio,endpointPrefactor,
    Real.log_div (pow_pos hb N).ne' (Real.rpow_pos_of_pos hdet _).ne',
    Real.log_pow,Real.log_rpow hdet]
  field_simp


end
end TensorPCA.CoupledGaussianIntegralProofs
