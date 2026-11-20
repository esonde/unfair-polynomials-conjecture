import Trinomial.Fourier.Laurent
import Mathlib.Data.Nat.Choose.Sum

/-! # Constant terms of even powers of T + T⁻¹ -/

noncomputable section
namespace Trinomial.Fourier

open Polynomial
open LaurentPolynomial (T)

private theorem sum_coeff {ι : Type*} (s : Finset ι) (f : ι → Laurent) (d : ℤ) :
    (∑ i ∈ s, f i) d = ∑ i ∈ s, f i d :=
  map_sum (Finsupp.applyAddHom d : (ℤ →₀ ℝ) →+ ℝ) f s

theorem walk_count (n : ℕ) (d : ℤ) :
    walk (X^n) d = ∑ i ∈ Finset.range (n+1),
      if (i : ℤ) - (n-i : ℕ) = d then ((n.choose i : ℕ) : ℝ) else 0 := by
  rw [map_pow,walk_X,J,add_pow,sum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LaurentPolynomial.T_pow,LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]
  have shift : (i : ℤ)*1+↑(n-i)*(-1) = (i : ℤ)-↑(n-i) := by ring
  rw [shift]
  change (T _ * LaurentPolynomial.C (n.choose i : ℝ) : Laurent) d = _
  rw [mul_comm,← LaurentPolynomial.single_eq_C_mul_T,Finsupp.single_apply]

theorem even_moment (n : ℕ) : moment (X^(2*n)) = (2*n).choose n := by
  rw [moment,walk_count,Finset.sum_eq_single n]
  · rw [if_pos (by omega)]
  · intro i hi ne
    have := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

end Trinomial.Fourier
