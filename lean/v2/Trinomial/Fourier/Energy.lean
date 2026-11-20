import Trinomial.Fourier.Angular
import Trinomial.Fourier.IntegrationByParts
import Trinomial.Fourier.Weights

/-! # Angular energy and the six constant terms in Proposition 4 -/

noncomputable section
namespace Trinomial.Fourier

open Finset Polynomial MeasureTheory AddCircle

/-- Evaluation of the density by the six even return moments. -/
theorem density_moment (x : ℝ) :
    moment (energyDensity (X^2) (C x)) = (211*x^3+38*x^2-107*x+542)/4 := by
  let coeffs : ℕ → ℝ
    | 0 => 1168*x^3+768*x^2
    | 1 => -616*x^3-1360*x^2
    | 2 => 81*x^3+568*x^2-784*x+2304
    | 3 => -69*x^2+424*x-560
    | 4 => -57*x-184
    | _ => 45
  have mon (c : ℝ) (i : ℕ) : moment (C c*X^(2*i)) = c*(2*i).choose i := by
    rw [moment,map_mul,walk_C,← LaurentPolynomial.smul_eq_C_mul]
    change c * moment (X^(2*i)) = _
    rw [even_moment]
  have add (p q : ℝ[X]) : moment (p+q) = moment p + moment q := by simp [moment]
  have expan : energyDensity (X^2) (C x) = ∑ i ∈ range 6, C (coeffs i/8)*X^(2*i) := by
    apply Polynomial.funext
    intro z
    norm_num [coeffs,sum_range_succ,energyDensity,Polynomial.algebraMap_eq,Polynomial.eval_finset_sum]
    ring
  rw [expan,show moment (∑ i ∈ range 6, C (coeffs i/8)*X^(2*i)) =
      ∑ i ∈ range 6, moment (C (coeffs i/8)*X^(2*i)) by
    induction (range 6 : Finset ℕ) using Finset.induction_on with
    | empty => simp [moment]
    | insert a s ha ih => simp [ha,add,ih]]
  simp only [mon,sum_range_succ,sum_range_zero,sum_empty,zero_add]
  norm_num [coeffs,Nat.choose]
  ring

theorem mean_energy_density (R : ℝ) :
    (∫ θ : Angle, energyDensity (b θ^2) (R^2) ∂haar) =
      (211*(R^2)^3+38*(R^2)^2-107*R^2+542)/4 := by
  have e (θ : Angle) : energyDensity (b θ^2) (R^2) = (energyDensity (X^2) (C (R^2))).eval (b θ) := by
    simp [energyDensity,Polynomial.algebraMap_eq]
  simp_rw [e]
  rw [average_eval,density_moment]

private theorem column_bound (R : ℝ) (hp : 0 < R) (s : ℤ) (ds : Finset ℤ) :
    ∑ d ∈ ds, ellAt s * (ellAt s^2+16+(d:ℝ)^2) * ‖kernel R hp d s‖^2 ≤
      ∫ θ : Angle, localEnergy R s (b θ) ∂haar := by
  let a := ellAt s
  let f := column R hp s
  let g := angularDerivative R hp s
  have ha : 0 < a := by cases s <;> apply ell_pos
  have hv := bessel f ds
  have hd := (sum_le_sum (fun d (_ : d ∈ ds) => weighted_mode R hp s d)).trans (bessel g ds)
  have combine := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ a^2+16)) hd) ha.le
  apply le_trans _ (combine.trans_eq _)
  · simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply sum_le_sum
    intro d _
    change a*(a^2+16+(d:ℝ)^2)*‖kernel R hp d s‖^2 ≤
      a*((a^2+16)*‖kernel R hp d s‖^2+(d:ℝ)^2*‖kernel R hp d s‖^2)
    exact le_of_eq (by ring)
  · rw [← integral_const_mul,← integral_add,← integral_const_mul]
    · apply integral_congr_ae
      filter_upwards with θ
      simp only [a,f,g,column,angularDerivative,ContinuousMap.coe_mk,Complex.norm_real,
        Real.norm_eq_abs,sq_abs,mul_pow,velocity_sq,localEnergy,w]
      ring
    · exact integrable_circle (continuous_const.mul (f.continuous.norm.pow 2))
    · exact integrable_circle (g.continuous.norm.pow 2)

/-- The bound on every finite rectangle of angular frequencies and paired columns. -/
theorem energy_bound (R : ℝ) (hR : 1 ≤ R) (n : ℕ) (ds : Finset ℤ) :
    let k := kernel R (lt_of_lt_of_le zero_lt_one hR)
    ∑ j ∈ range n, ∑ d ∈ ds, weight j d*(‖k d (.ofNat j)‖^2+‖k d (.negSucc j)‖^2) ≤ 171*R^6 := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let e (s : ℤ) (θ : Angle) := localEnergy R s (b θ)
  have ce (s : ℤ) : Continuous (e s) := (original_cont R hp s).comp b_cont
  have rows (j : ℕ) : ∑ d ∈ ds, weight j d * (‖kernel R hp d (.ofNat j)‖^2+
      ‖kernel R hp d (.negSucc j)‖^2) ≤ ∫ θ, (e (.ofNat j) θ + e (.negSucc j) θ) ∂haar := by
    rw [integral_add (integrable_circle (ce _)) (integrable_circle (ce _))]
    simp only [mul_add,sum_add_distrib]
    exact add_le_add (column_bound R hp (.ofNat j) ds) (column_bound R hp (.negSucc j) ds)
  apply (sum_le_sum (fun j (_ : j ∈ range n) => rows j)).trans
  apply (integrated_energy R hp n).trans
  rw [mean_energy_density]
  have hx : 1 ≤ R^2 := by nlinarith [sq_nonneg (R-1)]
  have hx2 := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ R^2)
  have hx3 := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ (R^2)^2)
  nlinarith

end Trinomial.Fourier
