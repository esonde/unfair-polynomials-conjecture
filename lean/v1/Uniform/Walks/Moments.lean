module

public import Uniform.Walks.Polynomial
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-! # Return counts and reflection of the walk coefficients -/

noncomputable section
namespace Uniform.Walks

open Polynomial
open LaurentPolynomial (T)

private theorem sum_coeff {ι : Type*} (s : Finset ι) (f : ι → Laurent) (d : ℤ) :
    (∑ i ∈ s, f i).coeff d = ∑ i ∈ s, (f i).coeff d := by
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

theorem walk_count (n : ℕ) (d : ℤ) :
    (walk (X^n)).coeff d = ∑ i ∈ Finset.range (n+1),
      if (i : ℤ) - (n-i : ℕ) = d then ((n.choose i : ℕ) : ℝ) else 0 := by
  rw [map_pow,walk_X,J,add_pow,sum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LaurentPolynomial.T_pow,LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]
  have shift : (i : ℤ)*1+↑(n-i)*(-1) = (i : ℤ)-↑(n-i) := by ring
  rw [shift]
  change (T _ * LaurentPolynomial.C (n.choose i : ℝ) : Laurent).coeff d = _
  rw [mul_comm,← LaurentPolynomial.single_eq_C_mul_T,AddMonoidAlgebra.coeff_single_apply]

theorem even_moment (n : ℕ) : moment (X^(2*n)) = (2*n).choose n := by
  rw [moment,walk_count,Finset.sum_eq_single n]
  · rw [if_pos (by omega)]
  · intro i hi ne
    have := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

theorem odd_moment (n : ℕ) : moment (X^(2*n+1)) = 0 := by
  rw [moment,walk_count]
  apply Finset.sum_eq_zero
  intro i hi
  have := Finset.mem_range.mp hi
  rw [if_neg (by omega)]

/-- Substitution of -X in a polynomial multiplies its d-th walk coefficient by (-1)^d. -/
theorem reflect_coeff (p : ℝ[X]) (d : ℤ) :
    (walk (p.comp (-X))).coeff d = (-1 : ℝ)^d * (walk p).coeff d := by
  induction p using Polynomial.induction_on generalizing d with
  | C a =>
    simp only [C_comp,walk_C,LaurentPolynomial.C_apply]
    split_ifs with h <;> simp_all
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a ih =>
    let p := C a*X^n
    rw [pow_succ,← mul_assoc,mul_comp,X_comp,map_mul walk _ (-X),map_neg,walk_X,
      mul_neg,mul_comm _ J,map_mul walk _ X,walk_X,mul_comm _ J]
    change -((J*walk (p.comp (-X))).coeff d) = (-1 : ℝ)^d * ((J*walk p).coeff d)
    rw [shift,shift, ih (d-1), ih (d+1),zpow_sub₀ (by norm_num : (-1:ℝ) ≠ 0),
      zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0)]
    simp [p]; ring

end Uniform.Walks
