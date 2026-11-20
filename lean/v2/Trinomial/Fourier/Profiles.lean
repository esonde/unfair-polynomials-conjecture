module

public import Trinomial.Fourier.Branches
public import Trinomial.Fourier.ColumnMoments

@[expose] public section

/-! # Angular profiles, their half-integer weights and their parity -/

noncomputable section
namespace Trinomial.Fourier

def ellAt : ℤ → ℝ
  | .ofNat j => ell j
  | .negSucc j => ell j

def localEnergy (R : ℝ) (s : ℤ) (u : ℝ) : ℝ :=
  ellAt s*((ellAt s^2+16)*branch R s u^2+w u*dbranch R s u^2)

def signAt : ℤ → ℝ
  | .ofNat j => (-1)^(j+1)
  | .negSucc j => (-1)^j

theorem reflected_branch (R : ℝ) (s : ℤ) (u : ℝ) :
    branch R s (-u) = signAt s * branch R s u := by
  have height_even : height R s (-u) = height R s u := by
    cases s <;> simp [height]
  have w_even : w (-u) = w u := by simp [w]
  unfold branch g cut
  rw [height_even, w_even]
  by_cases h : 0 < height R s u
  · rw [if_pos h, if_pos h]
    cases s with
    | ofNat j =>
      simp only [raw, base, ratioTerm, neg_sq, signAt]
      rw [neg_pow u (j+1), div_mul_eq_div_div]
      have inv_sign : ((-1 : ℝ)^(j+1))⁻¹ = (-1)^(j+1) := by
        rw [← inv_pow]
        norm_num
      simp only [div_eq_mul_inv, inv_sign]
      ring
    | negSucc j =>
      simp only [raw, base, ratioTerm, neg_sq, neg_neg, signAt]
      rw [neg_pow]
      have hs : ((-1 : ℝ)^j)^2 = 1 := by rw [sq, ← mul_pow]; norm_num
      linear_combination -(w u * (u^2-R^2)^2 * u^j/R^(j+1)) * hs
  · simp [h]

end Trinomial.Fourier
