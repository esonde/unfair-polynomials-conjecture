import Uniform.Walks.Geometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Int.Interval

/-! # The reciprocal-weight sum (Appendix A.3)
The tangent line to the reciprocal gives the cell-average Jensen inequality.
Its primitive lets the bounds on consecutive cells telescope. -/

noncomputable section
namespace Uniform.Walks

open Finset Real

def weight (j : ℕ) (d : ℤ) : ℝ := ell j*(ell j^2+9+(d:ℝ)^2)

theorem ell_pos (j : ℕ) : 0 < ell j := by unfold ell; positivity
theorem weight_pos (j : ℕ) (d : ℤ) : 0 < weight j d := by unfold weight; have := ell_pos j; positivity

private theorem cell (b d : ℝ) (hb : 0 < b) :
    let D := b^2+d^2+1/12
    1/D ≤ (arctan ((d+1/2)/b)-arctan ((d-1/2)/b))/b := by
  let D := b^2+d^2+1/12
  have hD : 0 < D := by dsimp [D]; positivity
  let F (y : ℝ) := (2/D-b^2/D^2)*y-y^3/(3*D^2)
  let A (y : ℝ) := arctan (y/b)/b
  have dA (y : ℝ) : HasDerivAt A (1/(b^2+y^2)) y := by
    have ne : 1+(y/b)^2 ≠ 0 := by positivity
    convert ((hasDerivAt_arctan (y/b)).comp y ((hasDerivAt_id y).div_const b)).div_const b using 1
    dsimp; field_simp; ring
  have dF (y : ℝ) : HasDerivAt F (2/D-(b^2+y^2)/D^2) y := by
    convert ((hasDerivAt_id y).const_mul (2/D-b^2/D^2)).sub
      (((hasDerivAt_id y).pow 3).div_const (3*D^2)) using 1
    dsimp; field_simp; ring
  have mono : Monotone (fun y => A y - F y) := by
    apply monotone_of_deriv_nonneg (fun y => ((dA y).sub (dF y)).differentiableAt)
    intro y
    rw [((dA y).sub (dF y)).deriv]
    have hpos : 0 < b^2+y^2 := by positivity
    field_simp
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg hD.le (sq_nonneg (D-(b^2+y^2)))]
  have he : F (d+1/2)-F (d-1/2) = 1/D := by
    dsimp [F]
    field_simp
    dsimp [D]; ring
  have hh := mono (show d-1/2 ≤ d+1/2 by linarith)
  change 1/D ≤ _
  rw [← he,sub_div]
  dsimp only [A] at hh
  linarith

private def radius (j : ℕ) := sqrt (ell j^2+9-1/12)

private theorem radius_bounds (j : ℕ) : radius j^2 = ell j^2+9-1/12 ∧
    3 ≤ radius j ∧ ell j ≤ radius j := by
  have he : 1/2 ≤ ell j := by unfold ell; linarith [Nat.cast_nonneg (α := ℝ) j]
  have e2 := sq_nonneg (ell j-1/2)
  have eq : radius j^2 = ell j^2+9-1/12 := Real.sq_sqrt (by nlinarith [sq_nonneg (ell j)])
  have hn : 0 ≤ radius j := sqrt_nonneg _
  refine ⟨eq,?_,?_⟩
  · nlinarith
  · nlinarith [ell_pos j]

private theorem row_weight (j : ℕ) (s : Finset ℤ) :
    ∑ d ∈ s, 1/weight j d ≤ π/(ell j*radius j) := by
  obtain ⟨hb,hb₃,_⟩ := radius_bounds j
  have hb₀ : 0 < radius j := by linarith
  have hl := ell_pos j
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs+1
    have sub : s ⊆ Ico a b := fun d hd => mem_Ico.mpr ⟨min'_le _ _ hd, by dsimp [b]; have := le_max' _ _ hd; omega⟩
    have cells : ∑ d ∈ s, 1/weight j d ≤ ∑ d ∈ Ico a b, 1/weight j d :=
      sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => (one_div_pos.mpr (weight_pos ..)).le)
    apply cells.trans
    rw [Int.Ico_eq_finset_map, Finset.sum_map]
    let n := (b-a).toNat
    let v (i : ℕ) := arctan (((a:ℝ)+i-1/2)/radius j)/(ell j*radius j)
    change ∑ i ∈ range n, 1/weight j (a+i) ≤ _
    calc
      _ ≤ ∑ i ∈ range n, (v (i+1)-v i) := by
        apply sum_le_sum; intro i _
        have he := cell (radius j) ((a:ℝ)+i) hb₀
        dsimp only at he
        rw [hb] at he
        rw [show ell j^2+9-1/12+((a:ℝ)+i)^2+1/12 = ell j^2+9+((a:ℝ)+i)^2 by ring] at he
        unfold weight v
        push_cast
        rw [show (a:ℝ)+(i+1)-1/2 = a+i+1/2 by ring]
        convert mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hl.le) using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
      _ = v n-v 0 := sum_range_sub v n
      _ ≤ _ := by
        unfold v
        rw [← sub_div]
        apply div_le_div_of_nonneg_right _ (mul_pos hl hb₀).le
        linarith [arctan_lt_pi_div_two (((a:ℝ)+n-1/2)/radius j),
          neg_pi_div_two_lt_arctan (((a:ℝ)+(0:ℕ)-1/2)/radius j)]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs,sum_empty]
    positivity

private theorem half_tail (n : ℕ) :
    ∑ i ∈ range n, (1/((i:ℝ)+2)-1/(i+3)) ≤ 1/2 := by
  have he := sum_range_sub' (fun i : ℕ => (1:ℝ)/(i+2)) n
  simp only [Nat.cast_succ,Nat.cast_zero,zero_add] at he
  simp_rw [show ∀ i : ℕ, (i:ℝ)+1+2 = i+3 by intro i; ring] at he
  rw [he]
  have : 0 ≤ (1:ℝ)/(n+2) := by positivity
  linarith

/-- Uniform bound on every rectangle, sufficient for arbitrary finite partial sums. -/
theorem reciprocal_bound (n : ℕ) (s : Finset ℤ) :
    ∑ j ∈ range n, ∑ d ∈ s, 1/weight j d ≤ (25/18)*π := by
  have h (j : ℕ) := row_weight j s
  apply (sum_le_sum (fun j (_ : j ∈ range n) => h j)).trans
  have hn : range n ⊆ range (n+2) := range_mono (by omega)
  apply (sum_le_sum_of_subset_of_nonneg hn (fun j _ _ => by
    have := ell_pos j
    have := (radius_bounds j).2.1
    exact div_nonneg pi_pos.le (mul_nonneg (ell_pos j).le (by linarith)))).trans
  rw [show n+2 = 2+n by omega, Finset.sum_range_add]
  have lead (j : ℕ) : π/(ell j*radius j) ≤ π/(ell j*3) :=
    div_le_div_of_nonneg_left pi_pos.le (by have := ell_pos j; positivity)
      (mul_le_mul_of_nonneg_left (radius_bounds j).2.1 (ell_pos j).le)
  have tail (i : ℕ) : π/(ell (2+i)*radius (2+i)) ≤ π*(1/((i:ℝ)+2)-1/(i+3)) := by
    have e := ell_pos (2+i)
    have hr := (radius_bounds (2+i)).2.2
    calc
      _ ≤ π/(ell (2+i)*ell (2+i)) := div_le_div_of_nonneg_left pi_pos.le (mul_pos e e)
        (mul_le_mul_of_nonneg_left hr e.le)
      _ ≤ _ := by
        unfold ell; push_cast
        rw [div_eq_mul_inv]; apply mul_le_mul_of_nonneg_left _ pi_pos.le
        field_simp
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have ts := sum_le_sum (fun i (_ : i ∈ range n) => tail i)
  rw [← mul_sum] at ts
  have head := add_le_add (lead 0) (lead 1)
  norm_num [ell] at head
  simp only [sum_range_succ, sum_range_zero,sum_empty,zero_add]
  have h₀ : ell 0 = 1/2 := by norm_num [ell]
  have h₁ : ell 1 = 3/2 := by norm_num [ell]
  rw [h₀,h₁]
  nlinarith [mul_le_mul_of_nonneg_left (half_tail n) pi_pos.le]

end Uniform.Walks
