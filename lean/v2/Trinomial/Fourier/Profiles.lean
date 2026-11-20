import Trinomial.Fourier.Branches
import Trinomial.Fourier.ColumnMoments

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
  cases s with
  | ofNat j =>
    simp only [branch,g,cut,height,neg_sq,signAt]
    split_ifs
    · simp only [raw,base,ratioTerm,neg_sq,w]
      rw [show (-u)^(j+1) = (-1)^(j+1)*u^(j+1) by rw [← mul_pow,neg_one_mul],div_mul_eq_div_div]
      have h : ((-1:ℝ)^(j+1))⁻¹ = (-1:ℝ)^(j+1) := by rw [← inv_pow]; norm_num
      simp only [div_eq_mul_inv,h]; ring
    · ring
  | negSucc j =>
    simp only [branch,g,cut,height,neg_sq,signAt]
    split_ifs
    · simp only [raw,base,ratioTerm,neg_sq,w]
      rw [show (-u)^j = (-1)^j*u^j by rw [← mul_pow,neg_one_mul]]
      rw [neg_neg]
      have hs : ((-1:ℝ)^j)^2 = 1 := by rw [sq,← mul_pow]; norm_num
      linear_combination -((4-u^2) * (u^2-R^2)^2 * u^j/R^(j+1)) * hs
    · ring

end Trinomial.Fourier
