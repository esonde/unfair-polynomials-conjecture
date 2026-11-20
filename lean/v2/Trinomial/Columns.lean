module

public import Trinomial.Conjugate
public import Mathlib.Data.Int.LeastGreatest

@[expose] public section

/-! # Lowest positive entries and drops (Section 1) -/

noncomputable section
namespace Trinomial.FractionalCase

def entry (c : FractionalCase) (i l : ℤ) := coeffZ c.B (i*c.m+l*c.r)
def digit (c : FractionalCase) (i l : ℤ) := coeffZ (tri c.r c.m c.a*c.B) (i*c.m+l*c.r)

theorem entry_nonneg (c : FractionalCase) (i l : ℤ) : 0 ≤ c.entry i l := c.nonnegative.coeffZ _

theorem entry_le_one (c : FractionalCase) (i l : ℤ) : c.entry i l ≤ 1 := by
  have hm : (tri c.r c.m c.a).Monic := Polynomial.trinomial_monic c.r_pos (by linarith [c.oriented])
  have hn : NonnegativeCoeffs (tri c.r c.m c.a) := by
    intro n
    rw [tri_eq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
    split_ifs <;> have := c.a_pos <;> positivity
  unfold entry coeffZ
  split
  · exact factor_coeff_le_one c.nonnegative hn hm (mul_comm (tri c.r c.m c.a) c.B ▸ c.binary) _
  · norm_num

theorem array (c : FractionalCase) (i l : ℤ) :
    c.digit i l = c.entry i l + c.entry (i-1) l + c.a*c.entry i (l-1) := by
  unfold digit entry
  rw [recurrence]
  congr 2 <;> congr 1 <;> ring

theorem binary_digit (c : FractionalCase) (i l : ℤ) : c.digit i l = 0 ∨ c.digit i l = 1 :=
  c.binary.coeffZ _

theorem entry_period (c : FractionalCase) (i l q : ℤ) :
    c.entry i (l+q*c.m) = c.entry (i+q*c.r) l := by
  unfold entry
  congr 1; ring

private theorem next_positive (c : FractionalCase) (i l : ℤ) (hp : 0 < c.entry i l) :
    0 < c.entry i (l+1) ∨ 0 < c.entry (i-1) (l+1) := by
  by_contra! h
  have h₁ := le_antisymm h.1 (c.entry_nonneg ..)
  have h₂ := le_antisymm h.2 (c.entry_nonneg ..)
  have he := c.array i (l+1)
  rw [h₁, h₂, add_sub_cancel_right, zero_add, zero_add] at he
  have hlo := mul_pos c.a_pos hp
  have hhi := mul_le_mul_of_nonneg_left (c.entry_le_one i l) c.a_pos.le
  rcases c.binary_digit i (l+1) with hh | hh <;> linarith [c.a_lt_one]

theorem exists_positive (c : FractionalCase) (l : ℤ) : ∃ i, 0 < c.entry i l := by
  have posNat (k : ℕ) : ∃ i, 0 < c.entry i k := by
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      simp [entry, coeffZ, c.constant_one]
    | succ k ih =>
      obtain ⟨i,hi⟩ := ih
      rcases c.next_positive i k hi with h | h
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
  have hm : (0 : ℤ) < c.m := by exact_mod_cast (show 0 < c.m by linarith [c.oriented])
  obtain ⟨i,hi⟩ := posNat (l % c.m).toNat
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne')] at hi
  refine ⟨i-l/c.m*c.r, ?_⟩
  unfold entry at hi ⊢
  have he : (i-l/c.m*c.r)*c.m+l*c.r = i*c.m+(l%c.m)*c.r := by
    linear_combination -(c.r : ℤ) * Int.emod_add_ediv_mul l (c.m : ℤ)
  rwa [he]

theorem exists_bottom (c : FractionalCase) (l : ℤ) :
    ∃ s, 0 < c.entry s l ∧ ∀ i, 0 < c.entry i l → s ≤ i := by
  apply Int.exists_least_of_bdd _ (c.exists_positive l)
  refine ⟨min 0 (-(l*c.r)), fun i hi => ?_⟩
  have hexp : 0 ≤ i*c.m+l*c.r := by
    by_contra! hh
    rw [entry, coeffZ_of_neg _ hh] at hi
    exact (lt_irrefl _ hi)
  by_cases h : 0 ≤ i
  · exact (min_le_left ..).trans h
  · apply (min_le_right ..).trans
    have hm : (1 : ℤ) ≤ c.m := by exact_mod_cast (show 1 ≤ c.m by linarith [c.oriented])
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (sub_nonneg.mpr hm)]

def bottom (c : FractionalCase) (l : ℤ) := (exists_bottom c l).choose

theorem bottom_pos (c : FractionalCase) (l : ℤ) : 0 < c.entry (c.bottom l) l :=
  (exists_bottom c l).choose_spec.1

theorem bottom_le (c : FractionalCase) {i l : ℤ} (h : 0 < c.entry i l) : c.bottom l ≤ i :=
  (exists_bottom c l).choose_spec.2 i h

theorem below (c : FractionalCase) {i l : ℤ} (h : i < c.bottom l) : c.entry i l = 0 := by
  exact le_antisymm (not_lt.mp fun hp => (not_le_of_gt h) (c.bottom_le hp)) (c.entry_nonneg ..)

theorem bottom_step (c : FractionalCase) (l : ℤ) : c.bottom (l+1) ≤ c.bottom l := by
  rcases c.next_positive _ _ (c.bottom_pos l) with h | h <;> have := c.bottom_le h <;> omega

theorem bottom_period (c : FractionalCase) (l q : ℤ) :
    c.bottom (l+q*c.m) = c.bottom l - q*c.r := by
  apply le_antisymm
  · apply c.bottom_le
    rw [c.entry_period, sub_add_cancel]
    exact c.bottom_pos l
  · have h := c.bottom_pos (l+q*c.m)
    rw [c.entry_period] at h
    have := c.bottom_le h
    omega

/-- Below the previous bottom, the new entries form a binary word. -/
theorem word_binary (c : FractionalCase) {i l : ℤ} (hi : i < c.bottom (l-1)) :
    c.entry i l = 0 ∨ c.entry i l = 1 := by
  by_cases hs : c.bottom l ≤ i
  · refine Int.leInduction (motive := fun j _ => j < c.bottom (l-1) →
      c.entry j l = 0 ∨ c.entry j l = 1) ?_ ?_ i hs hi
    · intro hi
      have h := c.array (c.bottom l) l
      rw [c.below (by omega : c.bottom l-1 < c.bottom l), c.below hi, mul_zero, add_zero, add_zero] at h
      rw [← h]; apply c.binary_digit
    · intro i hs ih hi
      have h := c.array (i+1) l
      rw [add_sub_cancel_right, c.below hi, mul_zero, add_zero] at h
      rcases ih (by omega) with p | p <;> rcases c.binary_digit (i+1) l with q | q <;>
        first | left; linarith [c.entry_nonneg (i+1) l] | right; linarith
  · exact Or.inl (c.below (lt_of_not_ge hs))

theorem word_no_adjacent (c : FractionalCase) {i l : ℤ} (hi : i+1 < c.bottom (l-1)) :
    ¬(c.entry i l = 1 ∧ c.entry (i+1) l = 1) := by
  rintro ⟨h₀,h₁⟩
  have e := c.array (i+1) l
  rw [add_sub_cancel_right,c.below hi,h₀,mul_zero,add_zero] at e
  rcases c.binary_digit (i+1) l with h|h <;> linarith

theorem word_top_zero (c : FractionalCase) (l : ℤ) :
    c.entry (c.bottom (l-1)-1) l = 0 := by
  rcases c.word_binary (l := l) (i := c.bottom (l-1)-1) (by omega) with h | h
  · exact h
  · have he := c.array (c.bottom (l-1)) l
    rw [h] at he
    have hp := mul_pos c.a_pos (c.bottom_pos (l-1))
    rcases c.binary_digit (c.bottom (l-1)) l with h | h <;>
      linarith [c.entry_nonneg (c.bottom (l-1)) l]

theorem drop_depth (c : FractionalCase) {l : ℤ} (h : c.bottom l < c.bottom (l-1)) :
    c.bottom l + 2 ≤ c.bottom (l-1) := by
  by_contra! hh
  have he : c.bottom (l-1)-1 = c.bottom l := by omega
  have := c.word_top_zero l
  rw [he] at this
  linarith [c.bottom_pos l]

/-- Over a period starting in any column, the depths of the strict drops sum to r. -/
theorem sum_drop_depths (c : FractionalCase) (l : ℤ) :
    ∑ j ∈ (Finset.range c.m).filter (fun j : ℕ => c.bottom (l+j+1) < c.bottom (l+j)),
      (c.bottom (l+j) - c.bottom (l+j+1)) = c.r := by
  rw [Finset.sum_filter]
  have depth (j : ℕ) : (if c.bottom (l+j+1) < c.bottom (l+j) then
      c.bottom (l+j) - c.bottom (l+j+1) else 0) = c.bottom (l+j) - c.bottom (l+j+1) := by
    split_ifs with h
    · rfl
    · have := c.bottom_step (l+j)
      omega
  simp_rw [depth]
  have telescopes := Finset.sum_range_sub' (fun j : ℕ => c.bottom (l+j)) c.m
  simp only [Nat.cast_succ, ← add_assoc, Nat.cast_zero, add_zero] at telescopes
  rw [telescopes]
  have period := c.bottom_period l 1
  simp only [one_mul] at period
  omega

end Trinomial.FractionalCase
