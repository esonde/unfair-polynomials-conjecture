module

public import Uniform.Strips

@[expose] public section

/-! # The forced four rows of a strip (Section 2) -/

noncomputable section
namespace Uniform

variable {K : Type*} [CommRing K]

def firstRow (a : K) : ℕ → K
  | 0 => 1
  | k+1 => 1-a*firstRow a k

def secondRow (a : K) : ℕ → K
  | 0 => 0
  | k+1 => a*(firstRow a k-secondRow a k)

theorem row_increments (a : K) (k : ℕ) :
    firstRow a (k+1) = firstRow a k + (-a)^(k+1) ∧
    secondRow a (k+1) = secondRow a k - (k+1)*(-a)^(k+1) := by
  induction k with
  | zero => simp [firstRow, secondRow]; ring
  | succ k ih =>
    constructor
    · rw [firstRow, ih.1, pow_succ (-a) (k+1)]
      have h : 1-a*firstRow a k = firstRow a k + (-a)^(k+1) := ih.1
      linear_combination h
    · rw [secondRow, ih.1, ih.2, pow_succ (-a) (k+1), Nat.cast_succ]
      have h : a*(firstRow a k-secondRow a k) = secondRow a k - (k+1)*(-a)^(k+1) := ih.2
      linear_combination h

theorem row_sums (a : K) (k : ℕ) :
    firstRow a k = ∑ i ∈ Finset.range (k+1), (-a)^i ∧
    secondRow a k = -∑ i ∈ Finset.range (k+1), (i : K)*(-a)^i := by
  induction k with
  | zero => simp [firstRow, secondRow]
  | succ k ih =>
    simp only [Finset.sum_range_succ _ (k+1), (row_increments a k).1, (row_increments a k).2,
      ih.1, ih.2, Nat.cast_succ]
    exact ⟨trivial, by abel⟩

theorem row_endpoints (a : K) (k : ℕ) :
    (1+a)*firstRow a k = 1+a*(-a)^k ∧
    (1+a)*secondRow a k + firstRow a k-1 = k*(-a)^(k+1) := by
  induction k with
  | zero => simp [firstRow, secondRow]
  | succ k ih =>
    rw [(row_increments a k).1, (row_increments a k).2, pow_succ (-a) (k+1),
      pow_succ (-a) k, Nat.cast_succ]
    constructor
    · linear_combination ih.1
    · linear_combination ih.2

namespace FractionalCase.Strip

variable {c : FractionalCase}

def b (S : Strip c) (j : ℤ) (k : ℕ) := c.entry (c.bottom S.start+j) (S.start+k)
def d (S : Strip c) (j : ℤ) (k : ℕ) := c.digit (c.bottom S.start+j) (S.start+k)

theorem d_binary (S : Strip c) (j : ℤ) (k : ℕ) : S.d j k = 0 ∨ S.d j k = 1 := c.binary_digit ..

theorem row (S : Strip c) (j : ℤ) (k : ℕ) :
    S.d j (k+1) = S.b j (k+1)+S.b (j-1) (k+1)+c.a*S.b j k := by
  unfold d b
  rw [c.array]
  simp only [Nat.cast_succ]
  rw [show S.start+(k+1)-1 = S.start+k by omega, show c.bottom S.start+j-1 = c.bottom S.start+(j-1) by omega]

theorem negative_before (S : Strip c) {j : ℤ} {k : ℕ} (hj : j < 0) (hk : k < S.width) :
    S.b j k = 0 := c.below (by rw [S.flat _ hk]; omega)

theorem bottom_previous (S : Strip c) :
    c.bottom (S.start+S.width-1) = c.bottom S.start := by
  have he : S.start+S.width-1 = S.start+↑(S.width-1) := by have := S.positive; omega
  rw [he, S.flat _ (by have := S.positive; omega)]

theorem lower_neighbor (S : Strip c) {k : ℕ} (hk : k ≤ S.width) : S.b (-1) k = 0 := by
  rcases hk.lt_or_eq with h | rfl
  · exact S.negative_before (by decide) h
  · have he := c.word_top_zero (S.start+S.width)
    rw [S.bottom_previous] at he
    exact he

theorem initial (S : Strip c) : S.b 0 0 = 1 ∧ S.b 1 0 = 0 := by
  have hd := c.drop_depth S.drop
  have one := (c.word_binary (l := S.start) (i := c.bottom S.start) S.drop).resolve_left
    (c.bottom_pos _).ne'
  have eq := c.array (c.bottom S.start+1) S.start
  rw [add_sub_cancel_right, one, c.below (by omega : c.bottom S.start+1 < c.bottom (S.start-1)),
    mul_zero, add_zero] at eq
  have hz : c.entry (c.bottom S.start+1) S.start = 0 := by
    rcases c.binary_digit (c.bottom S.start+1) S.start with h | h <;>
      linarith [c.entry_nonneg (c.bottom S.start+1) S.start]
  simpa [b] using And.intro one hz

theorem two_rows (S : Strip c) {k : ℕ} (hk : k ≤ S.width) :
    S.b 0 k = firstRow c.a k ∧ S.b 1 k = secondRow c.a k ∧ 0 < S.b 0 k := by
  induction k with
  | zero => exact ⟨S.initial.1, S.initial.2, S.initial.1 ▸ zero_lt_one⟩
  | succ k ih =>
    obtain ⟨hp,hq,pp⟩ := ih (by omega)
    have r₀ := S.row 0 k
    have r₁ := S.row 1 k
    norm_num only at r₀ r₁
    rw [S.lower_neighbor hk, add_zero] at r₀
    have d₀ : S.d 0 (k+1) = 1 := by
      apply (S.d_binary ..).resolve_left
      have nn : 0 ≤ S.b 0 (k+1) := c.entry_nonneg ..
      linarith [mul_pos c.a_pos pp]
    have eq₀ : S.b 0 (k+1) = 1-c.a*S.b 0 k := by linarith
    have pos₀ : 0 < S.b 0 (k+1) := by
      have hle : S.b 0 k ≤ 1 := c.entry_le_one ..
      linarith [mul_le_mul_of_nonneg_left hle c.a_pos.le, c.a_lt_one]
    have d₁ : S.d 1 (k+1) = 1 := by
      apply (S.d_binary ..).resolve_left
      have nn : 0 ≤ S.b 1 (k+1) := c.entry_nonneg ..
      have prev : 0 ≤ S.b 1 k := c.entry_nonneg ..
      linarith [mul_nonneg c.a_pos.le prev]
    exact ⟨by rw [firstRow, ← hp, eq₀], by rw [secondRow, ← hp, ← hq]; linarith, pos₀⟩

theorem middle_lt_half (c : FractionalCase) : c.a < 1/2 := by
  obtain ⟨S, _, _, _, hw⟩ := c.widest
  have eq := (S.two_rows (k := 2) (by omega)).2.1
  have nn : 0 ≤ S.b 1 2 := c.entry_nonneg ..
  norm_num [firstRow, secondRow] at eq
  have le : c.a ≤ 1/2 := by
    by_contra! h
    nlinarith [mul_pos c.a_pos (show 0 < 2*c.a-1 by linarith)]
  apply lt_of_le_of_ne le
  intro half
  obtain ⟨σ,hs,_⟩ := c.conjugate_annulus
  have gen_eq : (2 : c.field)*c.gen = 1 := by
    apply (algebraMap c.field ℝ).injective
    change (2 : ℝ)*c.a = 1
    rw [half]; norm_num
  have eqσ := congrArg σ gen_eq
  simp only [map_mul, map_ofNat, map_one] at eqσ
  have hn := congrArg norm eqσ
  rw [norm_mul, norm_one, Complex.norm_ofNat] at hn
  linarith

/-- All four product digits are one, including at the last column of the strip. -/
theorem four_digits (S : Strip c) {k : ℕ} (hk : k+1 ≤ S.width) :
    S.d 0 (k+1) = 1 ∧ S.d 1 (k+1) = 1 ∧ S.d 2 (k+1) = 1 ∧ S.d 3 (k+1) = 1 := by
  have half := middle_lt_half c
  have p_bounds (i : ℕ) (hi : i ≤ S.width) : 1-c.a ≤ S.b 0 i ∧ S.b 0 i ≤ 1 := by
    refine ⟨?_, c.entry_le_one ..⟩
    cases i with
    | zero => rw [S.initial.1]; linarith [c.a_pos]
    | succ i =>
      rw [(S.two_rows hi).1, firstRow, ← (S.two_rows (k := i) (by omega)).1]
      have h : S.b 0 i ≤ 1 := c.entry_le_one ..
      linarith [mul_le_mul_of_nonneg_left h c.a_pos.le]
  have q_bounds (i : ℕ) (hi : i ≤ S.width) : S.b 1 i ≤ c.a ∧ (0 < i → 0 < S.b 1 i) := by
    induction i with
    | zero => simp [S.initial.2, c.a_pos.le]
    | succ i ih =>
      have h := (ih (by omega)).1
      have ⟨pl,pu⟩ := p_bounds i (by omega)
      have ql : 0 ≤ S.b 1 i := c.entry_nonneg ..
      rw [(S.two_rows hi).2.1, secondRow, ← (S.two_rows (k := i) (by omega)).1,
        ← (S.two_rows (k := i) (by omega)).2.1]
      exact ⟨by linarith [mul_le_mul_of_nonneg_left (show S.b 0 i-S.b 1 i ≤ 1 by linarith) c.a_pos.le],
        fun _ => mul_pos c.a_pos (by linarith)⟩
  have digit_one (j : ℤ) (pos : 0 < S.b j (k+1) + S.b (j-1) (k+1) + c.a*S.b j k) :
      S.d j (k+1) = 1 := by
    apply (S.d_binary ..).resolve_left
    rw [S.row]; exact pos.ne'
  have nn (j : ℤ) (i : ℕ) : 0 ≤ S.b j i := c.entry_nonneg ..
  have pa (j : ℤ) : 0 ≤ c.a*S.b j k := mul_nonneg c.a_pos.le (nn ..)
  have hp := (S.two_rows hk).2.2
  obtain ⟨hq,qp⟩ := q_bounds (k+1) hk
  have qp' := qp (by omega)
  have d₂ : S.d 2 (k+1) = 1 := digit_one 2 (by norm_num; linarith [nn 2 (k+1), pa 2])
  have eq₂ := S.row 2 k
  norm_num only at eq₂
  have uq : S.b 2 k ≤ 1 := c.entry_le_one ..
  have pos₂ : 0 < S.b 2 (k+1) := by linarith [mul_le_mul_of_nonneg_left uq c.a_pos.le]
  exact ⟨digit_one 0 (by linarith [nn (0-1) (k+1), pa 0]),
    digit_one 1 (by norm_num; linarith [pa 1]), d₂,
    digit_one 3 (by norm_num; linarith [nn 3 (k+1), pa 3])⟩

end FractionalCase.Strip
end Uniform
