module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Finite Laurent polynomials under the substitution b = T + T⁻¹ -/

noncomputable section
namespace Trinomial.Fourier

open Polynomial
open LaurentPolynomial (T invert)

abbrev Laurent := LaurentPolynomial ℝ
def J : Laurent := T 1 + T (-1)
def walk : ℝ[X] →ₐ[ℝ] Laurent := aeval J
def moment (p : ℝ[X]) : ℝ := (walk p).coeff 0

@[simp] theorem walk_X : walk X = J := aeval_X _
@[simp] theorem walk_C (a : ℝ) : walk (C a) = LaurentPolynomial.C a := aeval_C ..

@[simp] theorem add_coeff (p q : Laurent) (i : ℤ) : (p+q).coeff i = p.coeff i+q.coeff i := rfl
@[simp] theorem sub_coeff (p q : Laurent) (i : ℤ) : (p-q).coeff i = p.coeff i-q.coeff i := rfl

theorem shift (P : Laurent) (d : ℤ) : (J*P).coeff d = P.coeff (d-1)+P.coeff (d+1) := by
  simp only [J, add_mul, add_coeff,LaurentPolynomial.T,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1 <;> congr 1 <;> omega

end Trinomial.Fourier
