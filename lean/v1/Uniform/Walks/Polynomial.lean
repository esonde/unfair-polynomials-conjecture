module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Laurent coefficients of polynomial walks (Appendix A.1) -/

noncomputable section
namespace Uniform.Walks

open Polynomial
open LaurentPolynomial (T invert)

abbrev Laurent := LaurentPolynomial ℝ
def J : Laurent := T 1 + T (-1)
def H : Laurent := T 1 - T (-1)
def walk : ℝ[X] →ₐ[ℝ] Laurent := aeval J
def moment (p : ℝ[X]) : ℝ := (walk p).coeff 0

@[simp] theorem walk_X : walk X = J := aeval_X _
@[simp] theorem walk_C (a : ℝ) : walk (C a) = LaurentPolynomial.C a := aeval_C ..

@[simp] theorem add_coeff (p q : Laurent) (i : ℤ) : (p+q).coeff i = p.coeff i+q.coeff i := rfl
@[simp] theorem sub_coeff (p q : Laurent) (i : ℤ) : (p-q).coeff i = p.coeff i-q.coeff i := rfl

theorem shift (P : Laurent) (d : ℤ) : (J*P).coeff d = P.coeff (d-1)+P.coeff (d+1) := by
  simp only [J, add_mul, add_coeff,LaurentPolynomial.T,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1 <;> congr 1 <;> omega

theorem difference (P : Laurent) (d : ℤ) : (H*P).coeff d = P.coeff (d-1)-P.coeff (d+1) := by
  simp only [H, sub_mul, sub_coeff,LaurentPolynomial.T,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1 <;> congr 1 <;> omega

@[simp] theorem invert_walk (p : ℝ[X]) : invert (walk p) = walk p := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | monomial n a h =>
    simp [J,add_comm]

theorem constant_term (p q : Laurent) : (p*q).coeff 0 = ∑ d ∈ p.coeff.support, p.coeff d*q.coeff (-d) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp [Finsupp.sum]

theorem sum_squares (p : Laurent) : ∑' d, (p.coeff d)^2 = (p*invert p).coeff 0 := by
  rw [constant_term,tsum_eq_sum (s := p.coeff.support) (fun d hd => by rw [Finsupp.notMem_support_iff.mp hd]; norm_num)]
  simp [sq]

theorem energy (p : ℝ[X]) : ∑' d, ((walk p).coeff d)^2 = moment (p^2) := by
  rw [sum_squares,invert_walk,moment,map_pow,sq]

/-- The logarithmic derivative in the walk variable, coefficient by coefficient. -/
theorem weighted_coeff (p : ℝ[X]) (d : ℤ) :
    (d : ℝ)*(walk p).coeff d = (H*walk p.derivative).coeff d := by
  induction p using Polynomial.induction_on generalizing d with
  | C a =>
    simp only [walk_C, LaurentPolynomial.C_apply, derivative_C, map_zero, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    split_ifs with hd <;> simp_all
  | add p q hp hq =>
    simp only [map_add,derivative_add,mul_add,add_coeff,hp,hq]
  | monomial n a ih =>
    let p := C a*X^n
    rw [pow_succ, ← mul_assoc]
    change (d : ℝ)*(walk (p*X)).coeff d = (H*walk (p*X).derivative).coeff d
    have commute' : H*(walk p.derivative*J) = J*(H*walk p.derivative) := by ring
    rw [derivative_mul,derivative_X,mul_one,map_add,map_mul walk p X,map_mul walk p.derivative X,walk_X,
      mul_comm (walk p) J,shift,mul_add H,commute',add_coeff,shift,difference (walk p) d]
    have left := ih (d-1)
    have right := ih (d+1)
    change ((d-1 : ℤ) : ℝ)*(walk p).coeff (d-1) = _ at left
    change ((d+1 : ℤ) : ℝ)*(walk p).coeff (d+1) = _ at right
    push_cast at left right
    linear_combination left + right

theorem step_product : (T 1 : Laurent)*T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; norm_num

private theorem H_square : H^2 = J^2-4 := by
  unfold H J
  linear_combination -4 * step_product

theorem difference_energy (p : ℝ[X]) :
    ∑' d : ℤ, ((H*walk p).coeff d)^2 = moment ((4-X^2)*p^2) := by
  rw [sum_squares,moment]
  simp only [map_mul,map_sub,map_pow,map_ofNat,walk_X,invert_walk]
  have hinv : invert H = -H := by simp [H]
  rw [hinv]
  have h : (H*walk p)*(-H*walk p) = -H^2*(walk p)^2 := by ring
  rw [h,H_square]; ring_nf

theorem weighted_energy (p : ℝ[X]) :
    ∑' d : ℤ, ((d : ℝ)*(walk p).coeff d)^2 = moment ((4-X^2)*p.derivative^2) := by
  simp_rw [weighted_coeff]
  exact difference_energy _

end Uniform.Walks
