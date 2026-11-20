import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! # Finite Laurent polynomials under the substitution b = T + T⁻¹ -/

noncomputable section
namespace Trinomial.Fourier

open Polynomial
open LaurentPolynomial (T invert)

abbrev Laurent := LaurentPolynomial ℝ
def J : Laurent := T 1 + T (-1)
def walk : ℝ[X] →ₐ[ℝ] Laurent := aeval J
def moment (p : ℝ[X]) : ℝ := walk p 0

@[simp] theorem walk_X : walk X = J := aeval_X _
@[simp] theorem walk_C (a : ℝ) : walk (C a) = LaurentPolynomial.C a := aeval_C ..

@[simp] theorem add_coeff (p q : Laurent) (i : ℤ) : (p+q) i = p i+q i := rfl
@[simp] theorem sub_coeff (p q : Laurent) (i : ℤ) : (p-q) i = p i-q i := rfl

theorem shift (P : Laurent) (d : ℤ) : (J*P) d = P (d-1)+P (d+1) := by
  simp only [J, add_mul, add_coeff,LaurentPolynomial.T,AddMonoidAlgebra.single_mul_apply,one_mul]
  congr 1 <;> congr 1 <;> omega

end Trinomial.Fourier
