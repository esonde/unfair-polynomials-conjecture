import Trinomial.Fourier.KernelNorm
import Trinomial.Fourier.Series
import Trinomial.Fourier.Specialize

/-! # Proposition 4 in the original two torus variables -/

noncomputable section
namespace Trinomial.Fourier

open AddCircle Polynomial Finset MeasureTheory

def doubledIndex (i : Lattice) : Lattice := (2*i.1+i.2-5,i.2)

private theorem index_injective : Function.Injective doubledIndex := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
  dsimp at h₁ h₂
  exact Prod.ext (by dsimp; omega) h₂

def phase (lam : ℂ) := lam / (‖lam‖ : ℂ)

private theorem phase_norm {lam : ℂ} (hp : 0 < ‖lam‖) : ‖phase lam‖ = 1 := by
  simp [phase,norm_div,abs_of_pos hp,hp.ne']

private theorem radius_phase {lam : ℂ} (hp : 0 < ‖lam‖) : (‖lam‖:ℂ)*phase lam = lam := by
  dsimp [phase]; field_simp [Complex.ofReal_ne_zero.mpr hp.ne']

/-- Undo the row-frequency doubling, the monomial shift, and the rotation of the second circle. -/
def coefficients (lam : ℂ) (hp : 0 < ‖lam‖) (i : Lattice) :=
  -(phase lam ^ i.2) * kernel ‖lam‖ hp (doubledIndex i).1 i.2

theorem coefficient_bound {lam : ℂ} (hR : 1 ≤ ‖lam‖) :
    let a := coefficients lam (lt_of_lt_of_le zero_lt_one hR)
    Summable (fun i => ‖a i‖) ∧ ∑' i, ‖a i‖ < 25*‖lam‖^3 := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let k (i : Lattice) := ‖kernel ‖lam‖ hp i.1 i.2‖
  have eq (i : Lattice) : ‖coefficients lam hp i‖ = k (doubledIndex i) := by
    simp [coefficients,k,doubledIndex,norm_mul,norm_zpow,phase_norm hp]
  dsimp only
  simp_rw [eq]
  have hs : Summable k := (kernel_norm ‖lam‖ hR).1
  have support : Function.support k ⊆ Set.range doubledIndex := by
    rintro ⟨d,s⟩ h
    obtain ⟨n,hn⟩ := kernel_row_frequency ‖lam‖ hp d s (fun eq => h (by simp [k,eq]))
    exact ⟨(n,s),Prod.ext hn.symm rfl⟩
  exact ⟨hs.comp_injective index_injective,(index_injective.tsum_eq support).trans_lt (kernel_norm _ hR).2⟩

def polynomialArray (P : ℂ[X]) (i : Lattice) := if i.2 = 0 then coeffZ P i.1 else 0

private theorem doubled_one (n : ℤ) : doubled (1 : ℂ[X]) n = if n=0 then 1 else 0 := by
  simp only [doubled,coeffZ,Polynomial.coeff_one]
  split_ifs <;> first | rfl | omega

private theorem mask_mode (R : ℝ) (p : ℤ) :
    -(walk (numerator R) (2*p-6) : ℂ) = coeffZ (mask (R^2-1) X) p := by
  have h := numerator_test R 1 p 1
  simp only [Nat.cast_one,mul_one,one_mul,pow_one,doubled_one] at h
  rw [tsum_eq_single (2*p-6) (fun d hd => by rw [if_neg (by omega),mul_zero])] at h
  simp only [sub_self,if_pos,mul_one] at h
  exact neg_eq_iff_eq_neg.mpr h

/-- The Fourier coefficient form of KF=P, including the phase of a complex λ. -/
theorem coefficient_equation (lam : ℂ) (hp : 0 < ‖lam‖) (i : Lattice) :
    let a := coefficients lam hp
    a i + a (i-(1,0)) + lam*a (i-(0,1)) = polynomialArray (mask (‖lam‖^2-1) X) i := by
  obtain ⟨p,s⟩ := i
  let d := 2*p+s-6
  have rec := kernel_equation ‖lam‖ hp d s
  let η := phase lam
  have hn : η ≠ 0 := by intro eq; have h := phase_norm hp; change ‖η‖ = 1 at h; simp [eq] at h
  have phase_step : lam*η^(s-1) = (‖lam‖:ℂ)*η^s := by
    conv_lhs => rw [← radius_phase hp]
    change _ * η * η^(s-1) = _ * _
    rw [mul_assoc,← zpow_one_add₀ hn,show 1+(s-1)=s by omega]
  dsimp only [coefficients,doubledIndex,Prod.fst_sub,Prod.snd_sub,sub_zero,polynomialArray]
  simp only [sub_zero]
  rw [show 2*p+s-5 = d+1 by dsimp [d]; omega,
      show 2*(p-1)+s-5 = d-1 by dsimp [d]; omega,
      show 2*p+(s-1)-5 = d by dsimp [d]; omega]
  change -(η^s)*_ + -(η^s)*_ + lam*(-(η^(s-1))*_) = _
  simp only [← mul_assoc,mul_neg,phase_step]
  by_cases hs : s=0
  · subst s
    simp only [zpow_zero,neg_one_mul,if_true] at rec ⊢
    have maskEq := mask_mode ‖lam‖ p
    rw [show d = 2*p-6 by dsimp [d]; ring] at rec ⊢
    rw [← maskEq,← rec]
    ring
  · rw [if_neg hs] at rec ⊢
    linear_combination -(η^s)*rec

def axis (n : ℕ) : Lattice := ((n:ℤ),0)

private theorem axis_inj : Function.Injective axis := by
  intro m n h
  have e : (m:ℤ) = n := congrArg Prod.fst h
  exact_mod_cast e

theorem polynomial_pairing (P : ℂ[X]) (f : Lattice → ℂ) :
    ∑' i, polynomialArray P i * f i = ∑ n ∈ P.support, P.coeff n * f (axis n) := by
  classical
  rw [tsum_eq_sum (s := P.support.image axis)]
  · rw [sum_image (fun _ _ _ _ h => axis_inj h)]
    simp [axis,polynomialArray]
  · rintro ⟨p,s⟩ hi
    by_cases hs : s=0
    · subst s
      by_cases hp : 0 ≤ p
      · lift p to ℕ using hp
        have hn : p ∉ P.support := fun h => hi (mem_image_of_mem axis h)
        have hz : P.coeff p = 0 := by simpa [Polynomial.mem_support_iff] using hn
        simp [polynomialArray,hz]
      · simp [polynomialArray,coeffZ,hp]
    · simp [polynomialArray,hs]

theorem synthesis_polynomial (P : ℂ[X]) (t : Torus) :
    synthesis (polynomialArray P) t = P.eval (fourier 1 t.1) := by
  rw [synthesis,polynomial_pairing,Polynomial.eval_eq_sum,Polynomial.sum_def]
  apply sum_congr rfl
  intro n _
  have pow (k : ℕ) : fourier (k:ℤ) t.1 = (fourier 1 t.1)^k := by
    induction k with
    | zero => simp [fourier_zero]
    | succ k ih => rw [Nat.cast_succ,fourier_add,ih,pow_succ]
  simp [axis,character,fourier_zero,pow]

def F (lam : ℂ) (t : Torus) := 1 + fourier 1 t.1 + lam*fourier 1 t.2
def P (lam : ℂ) (t : Torus) :=
  let y := fourier 1 t.1
  ((1-y)*((1+y)^2-(‖lam‖:ℂ)^2*y))^2

theorem P_eq_eval (lam : ℂ) (t : Torus) : P lam t = (mask (‖lam‖^2-1) X).eval (fourier 1 t.1) := by
  simp [P,mask]; ring

/-- Division in ℂ gives value zero at every zero of F. -/
def quotient (lam : ℂ) (t : Torus) := P lam t / F lam t

private theorem synthesis_mul (lam : ℂ) (hR : 1 ≤ ‖lam‖) (t : Torus) :
    let a := coefficients lam (lt_of_lt_of_le zero_lt_one hR)
    F lam t * synthesis a t = P lam t := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let a := coefficients lam hp
  have hn : Summable fun i => ‖a i‖ := (coefficient_bound hR).1
  have summ (v : Lattice) : Summable (fun i => a (i-v)*character i t) := by
    apply (hn.comp_injective (show Function.Injective (fun i : Lattice => i-v) from fun _ _ h => sub_left_inj.mp h)).of_norm_bounded
    intro i; simp [Function.comp_def,norm_mul]
  have s0 : Summable (fun i => a i * character i t) := by simpa using summ 0
  have eq := congrArg (fun f => synthesis f t) (funext (coefficient_equation lam hp))
  dsimp only at eq
  rw [synthesis_polynomial] at eq
  unfold synthesis at eq
  simp only [add_mul,mul_assoc] at eq
  rw [Summable.tsum_add (s0.add (summ (1,0))) ((summ (0,1)).mul_left lam),
    Summable.tsum_add s0 (summ (1,0)),tsum_mul_left] at eq
  change synthesis a t + synthesis (fun i => a (i-(1,0))) t +
    lam*synthesis (fun i => a (i-(0,1))) t = _ at eq
  rw [synthesis_shift,synthesis_shift] at eq
  simp only [character,fourier_zero,mul_one,one_mul] at eq
  change (1+fourier 1 t.1+lam*fourier 1 t.2)*synthesis a t = _
  rw [P_eq_eval]
  convert eq using 1; ring


theorem synthesis_eq_quotient (lam : ℂ) (hR : 1 ≤ ‖lam‖) :
    synthesis (coefficients lam (lt_of_lt_of_le zero_lt_one hR)) = quotient lam := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let a := coefficients lam hp
  have hc : Continuous (synthesis a) := synthesis_cont (coefficient_bound hR).1
  funext t
  by_cases h : F lam t = 0
  · have hz : P lam t = 0 := by simpa only [h,zero_mul] using (synthesis_mul lam hR t).symm
    have hn : lam ≠ 0 := norm_pos_iff.mp hp
    have hc' : Continuous (fun φ => synthesis a (t.1,φ)) :=
      hc.comp (continuous_const.prodMk continuous_id)
    have vanishes : ∀ φ ∈ ({t.2}ᶜ : Set Angle), synthesis a (t.1,φ) = 0 := by
      intro φ hφ
      have nz : F lam (t.1,φ) ≠ 0 := by
        intro he
        have eq : fourier 1 φ = fourier 1 t.2 := by
          apply mul_left_cancel₀ hn
          exact add_left_cancel (he.trans h.symm)
        apply hφ
        apply AddCircle.injective_toCircle (Fact.out : 0 < period).ne'
        exact Subtype.ext (by simpa only [fourier_one] using eq)
      have prod := synthesis_mul lam hR (t.1,φ)
      change F lam (t.1,φ)*synthesis a (t.1,φ) = P lam t at prod
      rw [hz] at prod
      exact (mul_eq_zero.mp prod).resolve_left nz
    have he := closure_minimal (t := {φ | synthesis a (t.1,φ) = 0}) vanishes
      (isClosed_eq hc' continuous_const) (dense_compl_singleton t.2 t.2)
    simpa only [quotient,h,div_zero] using he
  · apply (eq_div_iff h).mpr
    rw [mul_comm]
    exact synthesis_mul lam hR t

/-- The original row n and column s select angular mode 2n+s−5.
The phase accounts for a complex middle coefficient. -/
theorem quotient_coefficient (lam : ℂ) (hR : 1 ≤ ‖lam‖) (i : Lattice) :
    torusCoeff (quotient lam) i = coefficients lam (lt_of_lt_of_le zero_lt_one hR) i := by
  rw [← synthesis_eq_quotient lam hR,coeff_synthesis (coefficient_bound hR).1]

theorem quotient_mul (lam : ℂ) (hR : 1 ≤ ‖lam‖) (t : Torus) : quotient lam t * F lam t = P lam t := by
  rw [← synthesis_eq_quotient lam hR,mul_comm]
  exact synthesis_mul lam hR t

/-- Proposition 4. The quotient takes the value zero on the zero set of F. Both
Fourier indices refer to the original product torus, with normalized Haar measure. -/
theorem fourier_bound (lam : ℂ) (hR : 1 ≤ ‖lam‖) (_ : ‖lam‖ ≤ 2) :
    Continuous (quotient lam) ∧ Summable (fun i => ‖torusCoeff (quotient lam) i‖) ∧
      ∑' i, ‖torusCoeff (quotient lam) i‖ < 25*‖lam‖^3 := by
  rw [← synthesis_eq_quotient lam hR]
  have h := coefficient_bound hR
  simp_rw [coeff_synthesis h.1]
  exact ⟨synthesis_cont h.1,h⟩

end Trinomial.Fourier
