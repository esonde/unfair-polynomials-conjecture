module

public import Trinomial.Columns

@[expose] public section

/-! # Existence and size of a widest strip -/

namespace Trinomial.FractionalCase

theorem bottom_antitone (c : FractionalCase) : Antitone c.bottom := by
  intro i j hij
  exact Int.leInduction (motive := fun n _ => c.bottom n ≤ c.bottom i) le_rfl
    (fun n _ ih => (c.bottom_step n).trans ih) j hij

private theorem plateau_lt_period (c : FractionalCase) {l : ℤ} {n : ℕ}
    (h : c.bottom (l+n) = c.bottom l) : n < c.m := by
  by_contra! hn
  have hp := c.bottom_period l 1
  simp only [one_mul] at hp
  have := c.bottom_antitone (show l+(c.m : ℤ) ≤ l+n by omega)
  have := c.r_pos
  omega

/-- Both drops belong to the strip. Its final column may acquire new rows below the
old bottom. -/
structure Strip (c : FractionalCase) where
  start : ℤ
  width : ℕ
  positive : 0 < width
  drop : c.bottom start < c.bottom (start-1)
  flat : ∀ k : ℕ, k < width → c.bottom (start+k) = c.bottom start
  next_drop : c.bottom (start+width) < c.bottom start

private theorem falls_by_two (c : FractionalCase) (l : ℤ) (n : ℕ) :
    c.bottom (l+n) = c.bottom l ∨ c.bottom (l+n)+2 ≤ c.bottom l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc]
    have h := c.bottom_step (l+n)
    rcases h.eq_or_lt with h | h
    · rwa [h]
    · have hh : c.bottom (l+n+1) < c.bottom (l+n+1-1) := by simpa using h
      have hh' := c.drop_depth hh
      simp only [add_sub_cancel_right] at hh'
      have := c.bottom_antitone (show l ≤ l+n by omega)
      right; omega

/-- A whole period contains a drop, so its total depth cannot be one. -/
theorem two_le_r (c : FractionalCase) : 2 ≤ c.r := by
  have hp := c.bottom_period 0 1
  simp only [one_mul] at hp
  have hr := c.r_pos
  rcases c.falls_by_two 0 c.m with h | h <;> omega

/-- The widest strip and its predecessor, with the quantitative bound of Section 1. -/
theorem widest_with_ratio (c : FractionalCase) : ∃ S P : Strip c,
    P.start + P.width = S.start ∧ P.width ≤ S.width ∧ (∀ T : Strip c, T.width ≤ S.width) ∧ 2*c.m ≤ S.width*c.r := by
  classical
  let flat (n : ℕ) := ∃ l : ℤ, c.bottom (l+n) = c.bottom l
  let L := Nat.findGreatest flat c.m
  have h0 : flat 0 := ⟨0, by simp⟩
  obtain ⟨l,hl⟩ : flat L := Nat.findGreatest_spec (Nat.zero_le _) h0
  have maxFlat {n : ℕ} {i : ℤ} (hi : c.bottom (i+n) = c.bottom i) : n ≤ L :=
    Nat.le_findGreatest (c.plateau_lt_period hi).le (show flat n from ⟨i,hi⟩)
  have hleft : c.bottom l < c.bottom (l-1) := by
    have hs := c.bottom_antitone (show l-1 ≤ l by omega)
    apply lt_of_le_of_ne hs
    intro he
    have e : c.bottom (l-1+↑(L+1)) = c.bottom (l-1) := by
      rw [show l-1+↑(L+1) = l+L by omega, hl, he]
    have := maxFlat e; omega
  have hright : c.bottom (l+↑(L+1)) < c.bottom l := by
    have hs := c.bottom_antitone (show l ≤ l+↑(L+1) by omega)
    exact lt_of_le_of_ne hs (fun e => (Nat.not_succ_le_self L) (maxFlat e))
  -- The period ends at a drop. Record the last drop in each prefix;
  -- consecutive drops are separated by at most L+1 steps.
  let drops (n : ℕ) := (Finset.range n).filter (fun j : ℕ => c.bottom (l+j+1) < c.bottom (l+j))
  have spacing (n : ℕ) : ∃ q : ℕ, q ≤ n ∧ c.bottom (l+n) = c.bottom (l+q) ∧
      q ≤ (L+1)*(drops n).card := by
    induction n with
    | zero => exact ⟨0,le_rfl,rfl,Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨q,hqn,hflat,hcount⟩ := ih
      have hlen : n-q ≤ L := maxFlat (i := l+q) (by
        rw [Nat.cast_sub hqn,show l+q+(n-q:ℤ)=l+n by ring]; exact hflat)
      by_cases fall : c.bottom (l+n+1) < c.bottom (l+n)
      · refine ⟨n+1,le_rfl,rfl,?_⟩
        have count : (drops (n+1)).card = (drops n).card+1 := by
          simp [drops,Finset.range_add_one,fall,Finset.filter_insert]
        rw [count,Nat.mul_add,Nat.mul_one]
        omega
      · have flatStep := le_antisymm (c.bottom_step (l+n)) (le_of_not_gt fall)
        refine ⟨q,by omega,?_,?_⟩
        · simpa only [Nat.cast_succ,← add_assoc] using flatStep.trans hflat
        · simpa [drops,Finset.range_add_one,Finset.filter_insert,fall] using hcount
  have cover : c.m ≤ (L+1)*(drops c.m).card := by
    obtain ⟨q,hq,hflat,hcount⟩ := spacing c.m
    have prev := c.bottom_period (l-1) 1
    have last := c.bottom_period l 1
    simp only [one_mul] at prev last
    by_contra! fail
    have hqm : q < c.m := lt_of_le_of_lt hcount fail
    have le := c.bottom_antitone (show l+(q:ℤ) ≤ l-1+c.m by omega)
    omega
  have depth : 2*(drops c.m).card ≤ c.r := by
    have le : ∑ j ∈ drops c.m, (2:ℤ) ≤ ∑ j ∈ drops c.m, (c.bottom (l+j)-c.bottom (l+j+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      have hd := c.drop_depth (l := l+j+1) (by simpa using h)
      simp only [add_sub_cancel_right] at hd
      omega
    rw [c.sum_drop_depths l] at le
    exact_mod_cast (show 2*((drops c.m).card:ℤ) ≤ c.r by simpa [mul_comm] using le)
  have ratio : 2*c.m ≤ (L+1)*c.r := calc
    2*c.m ≤ 2*((L+1)*(drops c.m).card) := Nat.mul_le_mul_left _ cover
    _ = (L+1)*(2*(drops c.m).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ depth
  let S : Strip c := ⟨l,L+1,by omega,hleft,fun k hk => le_antisymm
    (c.bottom_antitone (by omega)) (hl ▸ c.bottom_antitone (show l+k ≤ l+L by omega)), hright⟩
  let back (n : ℕ) := c.bottom (l-1-n) = c.bottom (l-1)
  let J := Nat.findGreatest back c.m
  have prev : back J := Nat.findGreatest_spec (Nat.zero_le _) (show back 0 by simp [back])
  have prevEq {n : ℕ} (h : back n) : c.bottom (l-1-n+n) = c.bottom (l-1-n) := by
    rw [sub_add_cancel]; exact h.symm
  have prevMax {n : ℕ} (h : back n) : n ≤ J :=
    Nat.le_findGreatest (c.plateau_lt_period (prevEq h)).le h
  let b : ℤ := l-1-J
  have pb : c.bottom b = c.bottom (l-1) := prev
  have pd : c.bottom b < c.bottom (b-1) := by
    apply lt_of_le_of_ne (c.bottom_antitone (by omega))
    intro he
    have h : back (J+1) := by
      unfold back
      rw [show l-1-↑(J+1) = b-1 by dsimp [b]; omega, ← he, pb]
    have := prevMax h; omega
  have endEq : b+↑(J+1) = l := by dsimp [b]; omega
  let P : Strip c := ⟨b,J+1,by omega,pd,fun k hk => le_antisymm
    (c.bottom_antitone (by omega)) (pb ▸ c.bottom_antitone (show b+k ≤ l-1 by dsimp [b]; omega)),
    by rw [endEq, pb]; exact hleft⟩
  have widest (T : Strip c) : T.width ≤ S.width := by
    have positive := T.positive
    have bound := maxFlat (T.flat (T.width-1) (by omega))
    change T.width ≤ L+1
    omega
  exact ⟨S,P,endEq,Nat.succ_le_succ (maxFlat (prevEq prev)),widest,ratio⟩

theorem widest (c : FractionalCase) : ∃ S P : Strip c,
    P.start + P.width = S.start ∧ P.width ≤ S.width ∧ 5 ≤ S.width := by
  obtain ⟨S, P, adjacent, maximal, _, ratio⟩ := c.widest_with_ratio
  refine ⟨S, P, adjacent, maximal, ?_⟩
  by_contra! h
  have := Nat.mul_le_mul_right c.r (show S.width ≤ 4 by omega)
  have := c.oriented
  omega

end Trinomial.FractionalCase
