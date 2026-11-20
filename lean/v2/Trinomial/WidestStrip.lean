import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The contradiction at a widest strip (Section 4)
The bounds on the filtered differences are written after multiplication by the positive
factor R^k. This keeps every exponent natural. -/

namespace Trinomial

/-- Quadratic coefficient of the filtered row polynomial. -/
def quad (t : ℝ) : ℕ → ℝ
  | 0 => t^2 + 2*t
  | k+1 => quad t k + (k+1) + 2*t

/-- Negative of its cubic coefficient. -/
def cubic (t : ℝ) : ℕ → ℝ
  | 0 => 2*(1+t^2)
  | k+1 => cubic t k + quad t (k+1)

theorem strip_growth {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 5 ≤ k) :
    14*(1+t) ≤ quad t k ∧ (36+6*t+14*(k-5))*(1+t) ≤ cubic t k := by
  induction k, hk using Nat.le_induction with
  | base =>
    constructor <;> norm_num [quad, cubic] <;> nlinarith [sq_nonneg (t-1)]
  | succ k hk ih =>
    have hq : 14*(1+t) ≤ quad t (k+1) := by rw [quad]; linarith [ih.1, Nat.cast_nonneg (α := ℝ) k]
    refine ⟨hq, ?_⟩
    rw [cubic, Nat.cast_succ]
    linarith [ih.2]

private theorem incompatible {k t u z : ℝ} (hk : 5 ≤ k) (ht : 0 ≤ t) (ht₃ : t ≤ 3)
    (hu : 1 < u) (huz : u*z = 26)
    (h₁ : (k+2*t)*u ≤ 27*(1+t)) (h₂ : 14 ≤ u+z)
    (h₃ : 36+6*t+14*(k-5) ≤ (2*k+2*t)*u+z) : False := by
  have hu₁₀ : u < 10 := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ k+2*t by linarith)]
  have hz₁₀ : 10 < z := by
    by_contra! hz
    nlinarith [mul_nonneg (sub_nonneg.mpr hu₁₀.le) (sub_nonneg.mpr hz)]
  have hu₃ : u < 3 := by nlinarith [mul_pos (sub_pos.mpr hz₁₀) (show 0 < u by linarith)]
  have hbudget : 10*u+z < 36 := by nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hz₁₀)]
  nlinarith [mul_nonneg (show 0 ≤ k-5+t by linarith) (sub_nonneg.mpr hu₃.le)]

/-- No width at least five can satisfy both the inherited bounds from the preceding
strip and the three global bounds on its final filtered differences. -/
theorem widest_strip_impossible {k : ℕ} {R : ℝ} {U V : ℂ} (hk : 5 ≤ k)
    (hR : 1 < R) (hR₂ : R ≤ 2) (hU : ‖U‖ ≤ R^k) (hV : ‖V‖ ≤ k*R^k)
    (h₁ : (k+2*(R^2-1))*R^k ≤ 27*R^4)
    (h₂ : ‖(quad (R^2-1) k : ℂ)+U‖ * R^k ≤ 26*R^4)
    (h₃ : ‖-(cubic (R^2-1) k : ℂ)-(k+2*((R^2-1 : ℝ) : ℂ))*U+V‖ * R^k ≤ 26*R^4) :
    False := by
  let t := R^2-1
  let u := R^(k-2)
  let z := 26/u
  have hr : 0 < R := by linarith
  have ht : 0 ≤ t := by dsimp [t]; nlinarith [mul_pos (sub_pos.mpr hR) hr]
  have ht₃ : t ≤ 3 := by dsimp [t]; nlinarith [mul_nonneg (sub_nonneg.mpr hR₂) (show 0 ≤ 2+R by linarith)]
  have hu : 1 < u := one_lt_pow₀ hR (by omega)
  have hu₀ : 0 < u := by linarith
  have huz : u*z = 26 := by dsimp [z]; field_simp
  have hs : R^k = u*R^2 := by rw [← Nat.sub_add_cancel (show 2 ≤ k by omega), pow_add]
  have hs₀ : R^2 = 1+t := by dsimp [t]; ring
  have hsq : 0 < R^2 := sq_pos_of_pos hr
  have hscale (p : ℝ) (h : p*R^k ≤ 26*R^4) : p ≤ z*R^2 := by
    apply le_of_mul_le_mul_right (a := u*R^2) _ (mul_pos hu₀ hsq)
    rw [← hs]
    calc
      _ ≤ 26*R^4 := h
      _ = z*R^2*R^k := by rw [hs, ← huz]; ring
  obtain ⟨g₂,g₃⟩ := strip_growth ht hk
  have qa : quad t k ≤ ‖(quad t k : ℂ)+U‖ + ‖U‖ := by
    calc
      _ ≤ ‖(quad t k : ℂ)‖ := by simpa [Real.norm_eq_abs] using le_abs_self (quad t k)
      _ = ‖((quad t k : ℂ)+U)-U‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le ..
  let e : ℂ := -(cubic t k : ℂ)-(k+2*(t : ℂ))*U+V
  have kc : 0 ≤ (k : ℝ)+2*t := by positivity
  have normK : ‖((k : ℂ)+2*(t : ℂ))‖ = (k : ℝ)+2*t := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg kc]
  have lc : cubic t k ≤ ‖e‖ + (((k : ℝ)+2*t)*‖U‖+‖V‖) := by
    have de : (cubic t k : ℂ) = -e + (-((k : ℂ)+2*(t : ℂ))*U+V) := by dsimp [e]; ring
    calc
      _ ≤ ‖(cubic t k : ℂ)‖ := by simpa [Real.norm_eq_abs] using le_abs_self (cubic t k)
      _ = _ := congrArg _ de
      _ ≤ _ := (norm_add_le ..).trans (add_le_add (by rw [norm_neg]) ((norm_add_le ..).trans
        (by rw [norm_mul, norm_neg, normK])))
  apply incompatible (k := k) (t := t) (u := u) (z := z) (by exact_mod_cast hk) ht ht₃ hu huz
  · apply le_of_mul_le_mul_right (a := R^2) _ hsq
    calc
      _ = (k+2*t)*R^k := by rw [hs]; ring
      _ ≤ 27*R^4 := h₁
      _ = _ := by rw [← hs₀]; ring
  · apply le_of_mul_le_mul_right (a := R^2) _ hsq
    calc
      _ ≤ quad t k := hs₀ ▸ g₂
      _ ≤ _ := qa
      _ ≤ _ := add_le_add (hscale _ h₂) hU
      _ = _ := by rw [hs]; ring
  · apply le_of_mul_le_mul_right (a := R^2) _ hsq
    calc
      _ ≤ cubic t k := hs₀ ▸ g₃
      _ ≤ _ := lc
      _ ≤ _ := add_le_add (hscale _ h₃) (add_le_add (mul_le_mul_of_nonneg_left hU kc) hV)
      _ = _ := by rw [hs]; ring

end Trinomial
