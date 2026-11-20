module

public import Uniform.Walks.Branches
public import Uniform.Filter
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section

/-! # Substituting the walk variable into the polynomial filter -/

noncomputable section
namespace Uniform.Walks

open Finset Polynomial
open LaurentPolynomial (T)

/-- Coefficients after replacing X by X², including at negative indices. -/
def doubled (P : ℂ[X]) (n : ℤ) : ℂ := if n % 2 = 0 then coeffZ P (n/2) else 0

@[simp] theorem doubled_even (P : ℂ[X]) (n : ℤ) : doubled P (2*n) = coeffZ P n := by
  simp [doubled]

theorem doubled_recurrence (r m : ℕ) (lam : ℂ) (P : ℂ[X]) (n : ℤ) :
    doubled (tri r m lam * P) n = doubled P n + doubled P (n-2*m) + lam*doubled P (n-2*r) := by
  by_cases he : n % 2 = 0
  · have hm : (n-2*(m:ℤ)) % 2 = 0 := by omega
    have hr : (n-2*(r:ℤ)) % 2 = 0 := by omega
    simp only [doubled,he,hr,hm,if_true,recurrence]
    rw [show (n-2*(m:ℤ))/2 = n/2-m by omega,show (n-2*(r:ℤ))/2 = n/2-r by omega]
  · simp [doubled,he,show (n-2*(m:ℤ)) % 2 ≠ 0 by omega,show (n-2*(r:ℤ)) % 2 ≠ 0 by omega]

/-- Pair a finitely supported Laurent polynomial with a complex sequence. -/
def test (f : ℤ → ℂ) : Laurent →ₗ[ℝ] ℂ :=
  (Finsupp.lsum ℝ (fun d => LinearMap.toSpanSingleton ℝ ℂ (f d))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℝ)).toLinearMap

theorem test_tsum (p : Laurent) (f : ℤ → ℂ) :
    ∑' d, (p.coeff d : ℂ)*f d = test f p := by
  rw [tsum_eq_sum (s := p.coeff.support) (fun d hd => by rw [Finsupp.notMem_support_iff.mp hd]; simp)]
  rfl

private theorem test_power (f : ℤ → ℂ) (n : ℕ) :
    test f (walk (X^n)) = ∑ i ∈ range (n+1), (n.choose i : ℂ)*f ((i:ℤ) - (n-i : ℕ)) := by
  rw [map_pow,walk_X,J,add_pow,map_sum]
  apply sum_congr rfl
  intro i _
  rw [LaurentPolynomial.T_pow,LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]
  change test f (T _ * LaurentPolynomial.C (n.choose i : ℝ)) = _
  rw [mul_comm,← LaurentPolynomial.single_eq_C_mul_T]
  dsimp only [test]
  change (AddMonoidAlgebra.single _ (n.choose i : ℝ)).coeff.sum (fun d c => (c:ℂ)*f d) = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
  push_cast
  congr 2
  ring

/-- The constant-term test against the numerator is the negative of the seven-term mask. -/
theorem numerator_test (R : ℝ) (m : ℕ) (N : ℤ) (P : ℂ[X]) :
    ∑' d, (((walk (numerator R)).coeff d : ℝ) : ℂ) * doubled P (2*N-6*m-m*d) =
      -coeffZ (mask (R^2-1) (X^m)*P) N := by
  let f (d : ℤ) := doubled P (2*N-6*m-m*d)
  let x := R^2
  have expansion : numerator R =
      C (4*x^2)*X^(0:ℕ) + C (-8*x-x^2)*X^2 + C (4+2*x)*X^4 - X^6 := by
    simp only [numerator,x,map_sub,map_neg,map_add,map_mul,map_pow,map_ofNat]
    ring
  have mon (c : ℝ) (i : ℕ) : test f (walk (C c*X^i)) = (c:ℂ)*test f (walk (X^i)) := by
    rw [map_mul,walk_C]
    rw [← LaurentPolynomial.smul_eq_C_mul,map_smul]
    rfl
  rw [test_tsum,expansion]
  change test f _ = _
  rw [map_sub walk,map_sub (test f),map_add walk,map_add (test f),map_add walk,map_add (test f),mon,mon,mon]
  simp only [test_power]
  have cf := mask_coeff (R^2-1) m P 0 N
  simp only [Int.zero_mul,zero_add] at cf
  rw [cf]
  have shift (d : ℤ) : f (2*d-6) = coeffZ P (N-d*m) := by
    unfold f
    rw [show 2*N-6*(m:ℤ)-m*(2*d-6) = 2*(N-d*m) by ring,doubled_even]
  have at_even (i : ℤ) : f (2*i) = coeffZ P (N-(i+3)*m) := by
    convert shift (i+3) using 2
    ring
  norm_num [sum_range_succ,filterAt,Nat.choose,x]
  have e₀ := at_even (-3)
  have e₁ := at_even (-2)
  have e₂ := at_even (-1)
  have e₃ := at_even 0
  have e₄ := at_even 1
  have e₅ := at_even 2
  have e₆ := at_even 3
  norm_num at e₀ e₁ e₂ e₃ e₄ e₅ e₆
  simp only [e₀,e₁,e₂,e₃,e₄,e₅,e₆]
  ring_nf

end Uniform.Walks
