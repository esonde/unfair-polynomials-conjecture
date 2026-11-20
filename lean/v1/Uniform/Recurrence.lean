module

public import Uniform.Polynomial

@[expose] public section

/-! # The coefficient recurrence at integer indices -/

namespace Uniform

open Polynomial

variable {R : Type*} [CommRing R]

/-- Coefficients indexed by integers, with zero extension to negative indices. -/
def coeffZ (P : R[X]) (n : ℤ) : R := if 0 ≤ n then P.coeff n.toNat else 0

@[simp] theorem coeffZ_natCast (P : R[X]) (n : ℕ) : coeffZ P n = P.coeff n := by
  simp [coeffZ]

theorem coeffZ_of_neg (P : R[X]) {n : ℤ} (hn : n < 0) : coeffZ P n = 0 := by
  simp [coeffZ, not_le_of_gt hn]

theorem IsBinary.coeffZ {P : R[X]} (h : IsBinary P) (n : ℤ) :
    coeffZ P n = 0 ∨ coeffZ P n = 1 := by
  unfold Uniform.coeffZ
  split
  · exact h _
  · exact Or.inl rfl

theorem coeffZ_add (P Q : R[X]) (n : ℤ) :
    coeffZ (P+Q) n = coeffZ P n + coeffZ Q n := by
  simp only [coeffZ, coeff_add]
  split <;> simp

theorem coeffZ_C_mul (c : R) (P : R[X]) (n : ℤ) :
    coeffZ (C c * P) n = c * coeffZ P n := by
  simp only [coeffZ, coeff_C_mul]
  split <;> simp

theorem coeffZ_X_pow_mul (P : R[X]) (j : ℕ) (n : ℤ) :
    coeffZ (X ^ j * P) n = coeffZ P (n-j) := by
  simp only [coeffZ, coeff_X_pow_mul']
  split_ifs <;> first | rfl | (congr 1; omega)

noncomputable def tri (r m : ℕ) (a : R) : R[X] := trinomial 0 r m 1 a 1

theorem tri_eq (r m : ℕ) (a : R) : tri r m a = 1 + C a * X^r + X^m := by
  simp [tri, trinomial_def]

theorem recurrence (r m : ℕ) (a : R) (B : R[X]) (n : ℤ) :
    coeffZ (tri r m a * B) n = coeffZ B n + coeffZ B (n-m) + a * coeffZ B (n-r) := by
  rw [tri_eq, add_mul, add_mul, one_mul, mul_assoc]
  simp only [coeffZ_add, coeffZ_X_pow_mul, coeffZ_C_mul]
  abel

theorem tri_binary_one (r m : ℕ) (hr : 0 < r) (hm : r < m) : IsBinary (tri r m (1 : R)) := by
  intro n
  rw [tri_eq, coeff_add, coeff_add, C_1, one_mul, coeff_one, coeff_X_pow, coeff_X_pow]
  split_ifs <;> first | omega | simp

theorem not_equally_spaced {r : ℕ} {a : ℝ} {B : ℝ[X]} (hr : 0 < r)
    (ha : 0 < a) (ha' : a < 1) (hb : NonnegativeCoeffs B) (h₀ : B.coeff 0 = 1)
    (hc : IsBinary (tri r (2*r) a * B)) : False := by
  have row₁ := recurrence r (2*r) a B (r : ℤ)
  have row₂ := recurrence r (2*r) a B ((2*r : ℕ) : ℤ)
  have hn : (r : ℤ) - ↑(2*r) < 0 := by omega
  have hd : ((2*r : ℕ) : ℤ) - r = r := by omega
  simp only [coeffZ_natCast, coeffZ_of_neg B hn, sub_self, show coeffZ B 0 = 1 from h₀,
    add_zero, mul_one] at row₁
  simp only [coeffZ_natCast, sub_self, show coeffZ B 0 = 1 from h₀, hd] at row₂
  have hpos : 0 < B.coeff r := by rcases hc r with h | h <;> linarith [hb r]
  have := hc.coeff_le_one (2*r)
  linarith [hb (2*r), mul_pos ha hpos]

end Uniform
