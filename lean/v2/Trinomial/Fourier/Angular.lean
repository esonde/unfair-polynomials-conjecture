import Trinomial.Fourier.Circle
import Trinomial.Fourier.Profiles
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Field.Power

/-! # The angular profiles, their Fourier recurrence, parity and derivative estimate -/

noncomputable section
namespace Trinomial.Fourier

open MeasureTheory AddCircle Real Polynomial ContinuousMap

def column (R : ℝ) (hp : 0 < R) (s : ℤ) : C(Angle, ℂ) :=
  ⟨fun θ => Complex.ofReal (branch R s (b θ)),
    Complex.continuous_ofReal.comp ((branch_cont R hp s).comp b_cont)⟩

def angularDerivative (R : ℝ) (hp : 0 < R) (s : ℤ) : C(Angle, ℂ) :=
  ⟨fun θ => Complex.ofReal (dbranch R s (b θ) * velocity θ),
    Complex.continuous_ofReal.comp (((dbranch_cont R hp s).comp b_cont).mul velocity_cont)⟩

theorem column_deriv (R : ℝ) (hp : 0 < R) (s : ℤ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => column R hp s (u : Angle)) (angularDerivative R hp s (t : Angle)) t :=
  ((branch_hasDerivAt R hp s _).comp t (b_deriv t)).ofReal_comp

def kernel (R : ℝ) (hp : 0 < R) (d s : ℤ) : ℂ := fourierCoeff (column R hp s) d

theorem kernel_equation (R : ℝ) (hp : 0 < R) (d s : ℤ) :
    kernel R hp (d-1) s + kernel R hp (d+1) s + R*kernel R hp d (s-1) =
      if s=0 then (walk (numerator R) d : ℂ) else 0 := by
  have point (θ : Angle) :
      (b θ : ℂ)*column R hp s θ + R*column R hp (s-1) θ =
        if s=0 then Complex.ofReal ((numerator R).eval (b θ)) else 0 := by
    have he := congrArg Complex.ofReal (scalar R hp s (b θ))
    split_ifs at he ⊢ <;> simpa [column,numerator,w,base] using he
  have eq := congrArg (fun f : Angle → ℂ => fourierCoeff f d) (funext point)
  dsimp only at eq
  rw [coeff_add (f := fun θ => (b θ : ℂ)*column R hp s θ)
    (g := fun θ => (R:ℂ)*column R hp (s-1) θ) ((Complex.continuous_ofReal.comp b_cont).mul (column R hp s).continuous)
    (continuous_const.mul (column R hp (s-1)).continuous),coeff_b_mul (column R hp s).continuous,
    fourierCoeff.const_mul] at eq
  unfold kernel
  rw [eq]
  split_ifs <;> simp_all only [if_true,if_false,coeff_eval,coeff_const,ite_self]

private theorem half_turn (R : ℝ) (hp : 0 < R) (d s : ℤ) (hne : kernel R hp d s ≠ 0) :
    fourier (-d) (Real.pi : Angle) * (signAt s : ℂ) = 1 := by
  let φ : Angle := (Real.pi : ℝ)
  let F (θ : Angle) := fourier (-d) θ * column R hp s θ
  have h := integral_add_right_eq_self (μ := haar) F φ
  have tr (θ : Angle) : F (θ+φ) = (fourier (-d) φ * (signAt s : ℂ)) * F θ := by
    change fourier (-d) (θ+φ) * Complex.ofReal (branch R s (b (θ+(Real.pi : Angle)))) =
      _ * (fourier (-d) θ * Complex.ofReal (branch R s (b θ)))
    rw [char_translate,b_translate,reflected_branch,Complex.ofReal_mul]
    ring
  simp_rw [tr] at h
  rw [integral_const_mul] at h
  exact mul_right_cancel₀ hne (h.trans (one_mul _).symm)

/-- A nonzero angular mode has exactly the parity needed to come from an integer row. -/
theorem kernel_row_frequency (R : ℝ) (hp : 0 < R) (d s : ℤ) (hne : kernel R hp d s ≠ 0) :
    ∃ n : ℤ, d = 2*n+s-5 := by
  have phase (i : ℤ) : fourier i (Real.pi : Angle) = (-1:ℂ)^i := by
    rw [fourier_coe_apply,← Complex.exp_pi_mul_I,← Complex.exp_int_mul]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]; ring
  have sg : (signAt s : ℂ) = (-1:ℂ)^(s+1) := by
    cases s with
    | ofNat j => simp [signAt,pow_succ,zpow_add₀]
    | negSucc j =>
      rw [show Int.negSucc j+1 = -(j:ℤ) by omega,zpow_neg,← inv_zpow]
      simp [signAt]
  have h := half_turn R hp d s hne
  rw [phase,sg,← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0)] at h
  rcases Int.even_or_odd (-d+(s+1)) with he|ho
  · obtain ⟨k,hk⟩ := he
    exact ⟨3-k,by omega⟩
  · rw [ho.neg_one_zpow] at h; norm_num at h

theorem complementary (R : ℝ) (hp : 0 < R) (j : ℕ) (d : ℤ) :
    kernel R hp d (.ofNat j) = 0 ∨ kernel R hp d (.negSucc j) = 0 := by
  classical
  by_contra! h
  obtain ⟨p,ep⟩ := kernel_row_frequency R hp d _ h.1
  obtain ⟨q,eq⟩ := kernel_row_frequency R hp d _ h.2
  change d = 2*p+(j:ℤ)-5 at ep
  rw [show Int.negSucc j = -(j:ℤ)-1 by omega] at eq
  have impossible : 2*(p-q+(j:ℤ)) = -1 := by linarith
  exact absurd (congrArg (fun z : ℤ => z % 2) impossible) (by simp)

/-- Parseval on the normalized Haar circle, in the finite-sum form needed for Cauchy–Schwarz. -/
theorem bessel (f : C(Angle, ℂ)) (ds : Finset ℤ) :
    ∑ d ∈ ds, ‖fourierCoeff f d‖^2 ≤ ∫ θ : Angle, ‖f θ‖^2 ∂haar := by
  let v := toLp (E := ℂ) 2 haar ℂ f
  have hs := (lp.memℓp (fourierBasis.repr v)).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hs' : Summable (fun d : ℤ => ‖fourierCoeff v d‖^2) := by
    simpa [fourierBasis_repr] using hs
  have le := hs'.sum_le_tsum ds (fun _ _ => sq_nonneg _)
  rw [tsum_sq_fourierCoeff] at le
  simp only [v,fourierCoeff_toLp] at le
  apply le.trans_eq
  apply integral_congr_ae
  filter_upwards [coeFn_toLp haar (p := 2) (𝕜 := ℂ) f] with θ h
  rw [h]

private theorem coeff_interval (f : C(Angle, ℂ)) (d : ℤ) :
    fourierCoeffOn (Fact.out : 0 < period) (fun t : ℝ => f (t : Angle)) d = fourierCoeff f d := by
  rw [fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral _ _ 0]
  simp

set_option maxHeartbeats 1500000 in
/-- The zero frequency contributes zero to the derivative weight. -/
theorem weighted_mode (R : ℝ) (hp : 0 < R) (s d : ℤ) :
    (d:ℝ)^2 * ‖kernel R hp d s‖^2 ≤ ‖fourierCoeff (angularDerivative R hp s) d‖^2 := by
  by_cases hd : d = 0
  · subst d; simp
  let f := column R hp s
  let g := angularDerivative R hp s
  have h := fourierCoeffOn_of_hasDerivAt (f := fun t : ℝ => f (t : Angle))
    (f' := fun t : ℝ => g (t : Angle)) (Fact.out : 0 < period) hd
    (fun t _ => column_deriv R hp s t)
    ((g.continuous.comp (AddCircle.continuous_mk' period)).intervalIntegrable 0 period)
  rw [coeff_interval f,coeff_interval g] at h
  dsimp only at h
  rw [AddCircle.coe_period] at h
  simp only [AddCircle.coe_zero,sub_self,mul_zero,sub_zero,zero_sub] at h
  have hn : (d:ℂ) ≠ 0 := by exact_mod_cast hd
  have hp' : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have id : (d:ℂ)*Complex.I * kernel R hp d s = fourierCoeff g d := by
    unfold kernel
    rw [h]
    dsimp only [period]
    push_cast
    field_simp
    ring
  have nn := congrArg norm id
  simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_intCast] at nn
  rw [← nn,mul_pow,sq_abs]

end Trinomial.Fourier
