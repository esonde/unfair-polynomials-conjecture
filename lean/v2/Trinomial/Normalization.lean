import Trinomial.Recurrence

/-! # Reduction to a fractional coefficient and oriented exponents -/

namespace Trinomial

open Polynomial

theorem binary_shift_iff {P : ℝ[X]} (s : ℕ) : IsBinary (P * X^s) ↔ IsBinary P := by
  constructor
  · intro h i
    simpa only [coeff_mul_X_pow] using h (i+s)
  · intro h i
    rw [coeff_mul_X_pow']
    split
    · apply h
    · exact Or.inl rfl

theorem binary_mirror_iff (P : ℝ[X]) : IsBinary P.mirror ↔ IsBinary P := by
  have forward (Q : ℝ[X]) (h : IsBinary Q) : IsBinary Q.mirror := fun n => by
    rw [coeff_mirror]; apply h
  exact ⟨fun h => P.mirror_mirror ▸ forward _ h, forward _⟩

theorem trailing_eq_one {A B : ℝ[X]} (hma : A.Monic) (hmb : B.Monic)
    (ha : NonnegativeCoeffs A) (hb : NonnegativeCoeffs B) (hc : IsBinary (A*B)) :
    A.trailingCoeff = 1 ∧ B.trailingCoeff = 1 := by
  have ht := hc (A.natTrailingDegree+B.natTrailingDegree)
  rw [coeff_mul_natTrailingDegree_add_natTrailingDegree] at ht
  have hp := ht.resolve_left (mul_ne_zero (trailingCoeff_eq_zero.not.mpr hma.ne_zero)
    (trailingCoeff_eq_zero.not.mpr hmb.ne_zero))
  have ua : A.trailingCoeff ≤ 1 := factor_coeff_le_one ha hb hmb hc _
  have ub : B.trailingCoeff ≤ 1 := factor_coeff_le_one hb ha hma (mul_comm A B ▸ hc) _
  have pa : 0 ≤ A.trailingCoeff := ha _
  have pb : 0 ≤ B.trailingCoeff := hb _
  constructor
  · nlinarith [mul_nonneg pa (sub_nonneg.mpr ub)]
  · nlinarith [mul_nonneg pb (sub_nonneg.mpr ua)]

/-- The data used by the local and global parts of the contradiction. -/
structure FractionalCase where
  r : ℕ
  m : ℕ
  r_pos : 0 < r
  oriented : 2*r < m
  a : ℝ
  a_pos : 0 < a
  a_lt_one : a < 1
  B : ℝ[X]
  monic : B.Monic
  nonnegative : NonnegativeCoeffs B
  constant_one : B.coeff 0 = 1
  binary : IsBinary (tri r m a * B)

private theorem orient {r m : ℕ} {a : ℝ} {B : ℝ[X]} (hr : 0 < r) (hm : r < m)
    (ha : 0 < a) (ha' : a < 1) (hB : B.Monic) (hn : NonnegativeCoeffs B)
    (h₀ : B.coeff 0 = 1) (hc : IsBinary (tri r m a * B)) : Nonempty FractionalCase := by
  by_cases h : 2*r < m
  · exact ⟨⟨r, m, hr, h, a, ha, ha', B, hB, hn, h₀, hc⟩⟩
  have hne : m ≠ 2*r := fun e => not_equally_spaced hr ha ha' hn h₀ (e ▸ hc)
  have ht : B.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by change B.coeff 0 ≠ 0; rw [h₀]; norm_num)
  have hmB : B.mirror.Monic := by
    rw [Monic, mirror_leadingCoeff, trailingCoeff, ht, h₀]
  have hrev := (binary_mirror_iff _).2 hc
  rw [mirror_mul_of_domain, tri, trinomial_mirror hr hm one_ne_zero one_ne_zero, Nat.add_zero] at hrev
  refine ⟨⟨m-r, m, by omega, by omega, a, ha, ha', B.mirror, hmB,
    fun i => by rw [coeff_mirror]; apply hn, ?_, hrev⟩⟩
  rw [coeff_mirror, ht, Nat.add_zero, revAt_le (Nat.zero_le _), Nat.sub_zero, hB.coeff_natDegree]

/-- Removing the initial powers of X preserves all relevant hypotheses, including the
cardinality condition on the trinomial. A nonbinary middle coefficient yields a fractional case. -/
theorem theorem_of_no_fractional_case (exclude : FractionalCase → False) : TrinomialFactorStatement := by
  intro A B hma hmb ha hb hcard hc
  obtain ⟨k,j,n,hkj,hjn,x,a,y,hx,ha₀,hy,eA⟩ := card_support_eq_three.mp hcard
  change A = trinomial k j n x a y at eA
  obtain ⟨ta,tb⟩ := trailing_eq_one hma hmb ha hb hc
  rw [eA, trinomial_trailingCoeff hkj hjn hx] at ta
  have ly := hma.leadingCoeff
  rw [eA, trinomial_leadingCoeff hkj hjn hy] at ly
  subst x; subst y
  have ea : A.coeff j = a := by rw [eA, trinomial_middle_coeff hkj hjn]
  have pa : 0 < a := lt_of_le_of_ne (ea ▸ ha j) ha₀.symm
  have ua := factor_coeff_le_one ha hb hmb hc j
  rw [ea] at ua
  have er : j - k + k = j := by omega
  have em : n - k + k = n := by omega
  have shiftA : A = tri (j-k) (n-k) a * X^k := by
    rw [eA, tri_eq, trinomial_def, add_mul, add_mul, mul_assoc, ← pow_add, ← pow_add, er, em]
    simp
  have hr : 0 < j-k := by omega
  have hm : j-k < n-k := by omega
  rcases ua.eq_or_lt with h | h
  · rw [h] at shiftA
    have ba := (binary_shift_iff k).2 (tri_binary_one (R := ℝ) (j-k) (n-k) hr hm)
    rw [← shiftA] at ba
    exact ⟨ba, binary_cofactor hma ba hb hc⟩
  · obtain ⟨D, eD⟩ := (X_pow_dvd_iff.mpr
        (fun i (hi : i < B.natTrailingDegree) => coeff_eq_zero_of_lt_natTrailingDegree hi))
    have shB : B = D * X^B.natTrailingDegree := eD.trans (mul_comm _ _)
    have hD (i) : D.coeff i = B.coeff (i+B.natTrailingDegree) := by
      exact (coeff_mul_X_pow _ _ _).symm.trans (congrArg (fun P : ℝ[X] => P.coeff (i+B.natTrailingDegree)) shB.symm)
    have hD₀ : D.coeff 0 = 1 := by simpa [hD 0, trailingCoeff] using tb
    have hmD : D.Monic := by
      have key := congrArg leadingCoeff shB
      simpa only [leadingCoeff_mul, leadingCoeff_X_pow, mul_one, hmb.leadingCoeff] using key.symm
    have hprod : A*B = (tri (j-k) (n-k) a * D) * X^(k+B.natTrailingDegree) := by
      conv_lhs => rw [shiftA, shB]
      rw [pow_add]; ring
    have digits := (binary_shift_iff _).1 (hprod ▸ hc)
    exact (exclude (orient hr hm pa h hmD (fun i => hD i ▸ hb _) hD₀ digits).some).elim

end Trinomial
