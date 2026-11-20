import Trinomial.Fourier.ConstantTerm
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Angular Fourier coefficients on the circle with period 2π -/

noncomputable section
namespace Trinomial.Fourier

open MeasureTheory AddCircle Real Polynomial
open scoped ComplexConjugate Topology

abbrev period : ℝ := 2 * Real.pi
abbrev Angle := AddCircle period
instance : Fact (0 < period) := ⟨by unfold period; positivity⟩
abbrev haar : Measure Angle := haarAddCircle

def b (θ : Angle) : ℝ := 2 * (fourier 1 θ).re
def velocity (θ : Angle) : ℝ := -2 * (fourier 1 θ).im

@[fun_prop] theorem b_cont : Continuous b :=
  continuous_const.mul (Complex.continuous_re.comp (fourier 1).continuous)
theorem velocity_cont : Continuous velocity :=
  continuous_const.mul (Complex.continuous_im.comp (fourier 1).continuous)

theorem wave_coe (θ : ℝ) : fourier 1 (θ : Angle) = Complex.exp ((θ:ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

theorem b_coe (θ : ℝ) : b (θ : Angle) = 2 * Real.cos θ := by
  rw [b,wave_coe,Complex.exp_ofReal_mul_I_re]

theorem velocity_coe (θ : ℝ) : velocity (θ : Angle) = -2 * Real.sin θ := by
  rw [velocity,wave_coe,Complex.exp_ofReal_mul_I_im]

theorem b_deriv (θ : ℝ) : HasDerivAt (fun t : ℝ => b (t : Angle)) (velocity (θ : Angle)) θ := by
  simp only [b_coe,velocity_coe]
  convert (Real.hasDerivAt_cos θ).const_mul 2 using 1; ring

theorem velocity_sq (θ : Angle) : velocity θ ^ 2 = 4 - b θ ^ 2 := by
  induction θ using QuotientAddGroup.induction_on with
  | _ t =>
    change velocity (t : Angle)^2 = 4 - b (t : Angle)^2
    rw [velocity_coe,b_coe]
    nlinarith [Real.cos_sq_add_sin_sq t]

theorem b_range (θ : Angle) : b θ ∈ Set.Icc (-2 : ℝ) 2 := by
  induction θ using QuotientAddGroup.induction_on with
  | _ t =>
    change b (t : Angle) ∈ _
    rw [b_coe]; exact ⟨by linarith [Real.neg_one_le_cos t], by linarith [Real.cos_le_one t]⟩

theorem b_char (θ : Angle) : (b θ : ℂ) = fourier 1 θ + fourier (-1) θ := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [b]; ring

theorem b_translate (θ : Angle) : b (θ + (Real.pi : Angle)) = -b θ := by
  have h := fourier_add_half_inv_index (by decide : (1:ℤ) ≠ 0) (Fact.out : 0 < period) θ
  have hz : period / 2 / (1:ℤ) = Real.pi := by unfold period; norm_num
  rw [hz] at h
  simp [b,h]

theorem char_translate (d : ℤ) (θ φ : Angle) :
    fourier d (θ + φ) = fourier d θ * fourier d φ := by
  simp only [fourier_apply,smul_add,toCircle_add,Circle.coe_mul]

theorem integrable_circle {E : Type*} [NormedAddCommGroup E] {f : Angle → E}
    (hf : Continuous f) : Integrable f haar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem coeff_add {f g : Angle → ℂ} (hf : Continuous f) (hg : Continuous g) (d : ℤ) :
    fourierCoeff (fun t => f t + g t) d = fourierCoeff f d + fourierCoeff g d := by
  simp only [fourierCoeff,smul_eq_mul,mul_add]
  exact integral_add (integrable_circle ((fourier _).continuous.mul hf))
    (integrable_circle ((fourier _).continuous.mul hg))

theorem coeff_shift (f : Angle → ℂ) (i d : ℤ) :
    fourierCoeff (fun t => fourier i t * f t) d = fourierCoeff f (d-i) := by
  simp only [fourierCoeff,smul_eq_mul,← mul_assoc,← fourier_add,neg_sub]
  rw [add_comm,sub_eq_add_neg]

theorem coeff_b_mul {f : Angle → ℂ} (hf : Continuous f) (d : ℤ) :
    fourierCoeff (fun t => (b t : ℂ) * f t) d =
      fourierCoeff f (d-1) + fourierCoeff f (d+1) := by
  simp_rw [b_char,add_mul]
  rw [coeff_add ((fourier 1).continuous.mul hf) ((fourier (-1)).continuous.mul hf),coeff_shift,coeff_shift]
  simp

theorem coeff_const (c : ℂ) (d : ℤ) :
    fourierCoeff (fun _ : Angle => c) d = if d = 0 then c else 0 := by
  simp only [fourierCoeff,smul_eq_mul,integral_mul_const]
  split_ifs with h
  · subst d; simp [fourier_zero]
  · rw [integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index (neg_ne_zero.mpr h)
      (Fact.out : 0 < period)),zero_mul]

/-- For polynomials this Fourier coefficient is the coefficient of the finite Laurent expansion. -/
theorem coeff_eval (p : ℝ[X]) (d : ℤ) :
    fourierCoeff (fun t : Angle => Complex.ofReal (p.eval (b t))) d = (walk p d : ℂ) := by
  induction p using Polynomial.induction_on generalizing d with
  | C c =>
    simp only [eval_C,walk_C,LaurentPolynomial.C_apply,coeff_const]
    split_ifs <;> simp_all
  | add p q hp hq =>
    simp only [eval_add,Complex.ofReal_add,map_add,add_coeff]
    rw [coeff_add (f := fun t => Complex.ofReal (p.eval (b t))) (g := fun t => Complex.ofReal (q.eval (b t)))
      (Complex.continuous_ofReal.comp (p.continuous.comp b_cont))
      (Complex.continuous_ofReal.comp (q.continuous.comp b_cont)),hp,hq]
  | monomial n c ih =>
    let q := C c * X^n
    rw [pow_succ,← mul_assoc]
    change fourierCoeff (fun t : Angle => Complex.ofReal ((q*X).eval (b t))) d = _
    change _ = ((walk (q*X)) d : ℂ)
    rw [map_mul,walk_X]
    simp only [eval_mul,eval_X,Complex.ofReal_mul]
    rw [mul_comm (walk q) J,shift]
    simp_rw [mul_comm ((q.eval _ : ℝ) : ℂ)]
    rw [coeff_b_mul (f := fun t => Complex.ofReal (q.eval (b t))) (Complex.continuous_ofReal.comp (q.continuous.comp b_cont))]
    rw [show fourierCoeff (fun t => Complex.ofReal (q.eval (b t))) (d-1) = _ from ih (d-1),
      show fourierCoeff (fun t => Complex.ofReal (q.eval (b t))) (d+1) = _ from ih (d+1)]
    simp [q]

theorem average_eval (p : ℝ[X]) : ∫ θ : Angle, p.eval (b θ) ∂haar = moment p := by
  have h := coeff_eval p 0
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul] at h
  apply Complex.ofReal_injective
  exact (integral_ofReal (𝕜 := ℂ) (μ := haar) (f := fun t => p.eval (b t))).symm.trans h


instance angle_punctured (θ : Angle) : (𝓝[≠] θ).NeBot := by
  haveI : Nontrivial Angle := ⟨⟨0,(Real.pi : Angle),by
    intro eq
    have hb := b_translate (0 : Angle)
    rw [zero_add,← eq] at hb
    norm_num [b,fourier_eval_zero] at hb⟩⟩
  apply mem_closure_iff_nhdsWithin_neBot.mp
  exact (dense_compl_singleton_iff_not_open.mpr (fun ho =>
    (isClopen_iff.mp ⟨isClosed_singleton,ho⟩).elim (Set.singleton_ne_empty θ) (Set.singleton_ne_univ θ))) θ

private theorem level_finite (c : ℝ) : Set.Finite {θ : Angle | b θ = c} := by
  let p : ℂ[X] := X^2-C (c:ℂ)*X+1
  have hn : p ≠ 0 := by
    intro eq
    have h := congrArg (Polynomial.eval 0) eq
    simp [p] at h
  have inj : Function.Injective (fourier 1 : Angle → ℂ) := by
    intro x y h
    apply AddCircle.injective_toCircle (Fact.out : 0 < period).ne'
    exact Subtype.ext (by simpa only [fourier_one] using h)
  apply ((Polynomial.finite_setOf_isRoot hn).preimage inj.injOn).subset
  intro θ h
  change p.eval (fourier 1 θ) = 0
  have hb := b_char θ
  rw [show b θ = c from h] at hb
  have he : fourier (-1) θ * fourier 1 θ = 1 := by rw [← fourier_add]; exact fourier_zero
  simp only [p,eval_add,eval_sub,eval_pow,eval_X,eval_C,eval_mul,eval_one,hb]
  linear_combination -he

theorem off_switch_ae (R : ℝ) : ∀ᵐ θ : Angle ∂haar, b θ^2 ≠ R^2 := by
  apply ae_iff.mpr
  apply measure_mono_null _ (((level_finite R).union (level_finite (-R))).measure_zero haar)
  intro θ h
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (not_not.mp h)

end Trinomial.Fourier
