import Trinomial.Recurrence
import Mathlib.Analysis.Complex.Basic

/-! # The polynomial filter and the coefficient bound of Section 3 -/

noncomputable section
namespace Trinomial

open Polynomial

def mask (t : ℝ) (Y : ℂ[X]) : ℂ[X] := (1-Y)^2*((1+Y)^2-C (1+(t : ℂ))*Y)^2

def GlobalBound : Prop := ∀ (r m : ℕ) (lam : ℂ) (B : ℂ[X]), 0 < r → r < m → 1 ≤ ‖lam‖ → ‖lam‖ ≤ 2 →
  IsBinary (tri r m lam * B) → ∀ N : ℤ,
    ‖coeffZ ((1-X^r)*mask (‖lam‖^2-1) (X^m)*B) N‖ < 25*‖lam‖^3

/-- Convolution by the seven coefficients of the mask. -/
def filterAt (t : ℝ) (f : ℤ → ℂ) (j : ℤ) : ℂ :=
  let s : ℂ := t
  f j - 2*s*f (j-1) + (s^2+2*s)*f (j-2) - 2*(1+s^2)*f (j-3) +
    (s^2+2*s)*f (j-4) - 2*s*f (j-5) + f (j-6)

theorem filterAt_sub (t : ℝ) (f g : ℤ → ℂ) (j : ℤ) :
    filterAt t f j - filterAt t g j = filterAt t (fun i => f i-g i) j := by
  unfold filterAt; ring

theorem coeffZ_sub {K : Type*} [CommRing K] (P Q : K[X]) (n : ℤ) :
    coeffZ (P-Q) n = coeffZ P n - coeffZ Q n := by
  unfold coeffZ; split <;> simp

theorem mask_coeff (t : ℝ) (m : ℕ) (B : ℂ[X]) (i l : ℤ) :
    coeffZ (mask t (X^m)*B) (i*m+l) = filterAt t (fun j => coeffZ B (j*m+l)) i := by
  let s : ℂ := t
  have expand : mask t (X^m)*B =
      B - C (2*s)*(X^m*B) + C (s^2+2*s)*(X^(m*2)*B) - C (2*(1+s^2))*(X^(m*3)*B) +
      C (s^2+2*s)*(X^(m*4)*B) - C (2*s)*(X^(m*5)*B) + X^(m*6)*B := by
    simp only [mask, pow_mul, map_add,map_mul,map_one,map_pow, map_ofNat, s]
    ring
  rw [expand]
  simp only [coeffZ_add,coeffZ_sub,coeffZ_C_mul,coeffZ_X_pow_mul,filterAt,Nat.cast_mul,Nat.cast_ofNat,s]
  ring_nf

end Trinomial
