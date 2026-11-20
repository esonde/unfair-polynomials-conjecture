module

public import Trinomial.Fourier.Energy
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! # Absolute summability and the strict kernel norm bound -/

noncomputable section
namespace Trinomial.Fourier

open Finset Real

private def upper (p : ℕ × ℤ) : ℤ × ℤ := (p.2, .ofNat p.1)
private def lower (p : ℕ × ℤ) : ℤ × ℤ := (p.2, .negSucc p.1)

private def kernelLimit (R : ℝ) := √(((11/10)*π)*(171*R^6))

private theorem rectangle_norm (R : ℝ) (hR : 1 ≤ R) (n : ℕ) (ds : Finset ℤ) :
    let k := kernel R (lt_of_lt_of_le zero_lt_one hR)
    ∑ p ∈ range n ×ˢ ds, (‖k p.2 (.ofNat p.1)‖ + ‖k p.2 (.negSucc p.1)‖) ≤ kernelLimit R := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let k := kernel R hp
  let S := range n ×ˢ ds
  let recip (p : ℕ × ℤ) := 1 / weight p.1 p.2
  let energy (p : ℕ × ℤ) := weight p.1 p.2*(‖k p.2 (.ofNat p.1)‖^2+‖k p.2 (.negSucc p.1)‖^2)
  have eq (p : ℕ × ℤ) : (‖k p.2 (.ofNat p.1)‖ + ‖k p.2 (.negSucc p.1)‖)^2 = recip p*energy p := by
    have hw := (weight_pos p.1 p.2).ne'
    dsimp only [recip,energy]
    rcases complementary R hp p.1 p.2 with h|h <;> change k _ _ = 0 at h <;>
      rw [h] <;> simp [hw,← mul_assoc]
  have gpos (p : ℕ × ℤ) : 0 ≤ energy p := mul_nonneg (weight_pos ..).le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  apply Real.le_sqrt_of_sq_le
  apply (sum_sq_le_sum_mul_sum_of_sq_eq_mul S (fun p _ => (one_div_pos.mpr (weight_pos ..)).le)
    (fun p _ => gpos p) (fun p _ => eq p)).trans
  apply mul_le_mul _ _ (sum_nonneg (fun p _ => gpos p)) (by positivity : 0 ≤ 11/10*π)
  · simpa only [S,recip,sum_product] using reciprocal_bound n ds
  · simpa only [S,energy,k,sum_product] using energy_bound R hR n ds

private theorem finite_norm (R : ℝ) (hR : 1 ≤ R) (t : Finset (ℤ × ℤ)) :
    ∑ p ∈ t, ‖kernel R (lt_of_lt_of_le zero_lt_one hR) p.1 p.2‖ ≤ kernelLimit R := by
  let a (p : ℤ × ℤ) := ‖kernel R (lt_of_lt_of_le zero_lt_one hR) p.1 p.2‖
  let ds := t.image Prod.fst
  let n := t.sup (fun p => p.2.natAbs) + 1
  let S := range n ×ˢ ds
  have sub : t ⊆ S.image upper ∪ S.image lower := by
    rintro ⟨d,s⟩ hd
    have hm := le_sup (f := fun p : ℤ × ℤ => p.2.natAbs) hd
    have hd' : d ∈ ds := mem_image_of_mem Prod.fst hd
    cases s with
    | ofNat j => exact mem_union_left _ (mem_image.mpr ⟨(j,d), mem_product.mpr
        ⟨mem_range.mpr (by dsimp [n]; change j ≤ _ at hm; omega),hd'⟩, rfl⟩)
    | negSucc j => exact mem_union_right _ (mem_image.mpr ⟨(j,d), mem_product.mpr
        ⟨mem_range.mpr (by dsimp [n]; change j+1 ≤ _ at hm; omega),hd'⟩, rfl⟩)
  calc
    _ ≤ ∑ p ∈ S.image upper ∪ S.image lower, a p :=
      sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => norm_nonneg _)
    _ = (∑ p ∈ S.image upper, a p) + ∑ p ∈ S.image lower, a p := by
      apply sum_union
      rw [Finset.disjoint_left]
      intro p hu hl
      obtain ⟨i,_,rfl⟩ := mem_image.mp hu
      obtain ⟨j,_,hj⟩ := mem_image.mp hl
      have := congrArg Prod.snd hj
      simp [upper,lower] at this
    _ = (∑ p ∈ S, a (upper p)) + ∑ p ∈ S, a (lower p) := by
      congr 1 <;> apply sum_image <;> rintro ⟨i,d⟩ _ ⟨j,e⟩ _ he <;> simpa [upper,lower,and_comm] using he
    _ ≤ _ := by rw [← sum_add_distrib]; exact rectangle_norm R hR n ds

/-- The infinite kernel is absolutely summable with the constant of Proposition 4. -/
theorem kernel_norm (R : ℝ) (hR : 1 ≤ R) :
    let a (p : ℤ × ℤ) := ‖kernel R (lt_of_lt_of_le zero_lt_one hR) p.1 p.2‖
    Summable a ∧ ∑' p, a p < 25*R^3 := by
  dsimp only
  have hs := summable_of_sum_le (fun p : ℤ × ℤ => norm_nonneg (kernel R (lt_of_lt_of_le zero_lt_one hR) p.1 p.2)) (finite_norm R hR)
  refine ⟨hs, (hs.tsum_le_of_sum_le (finite_norm R hR)).trans_lt ?_⟩
  have hπ : π < 22/7 := by linarith [pi_lt_d4]
  have factor : (11/10*π)*171 < (625 : ℝ) := by linarith
  have h := mul_lt_mul_of_pos_right factor (by positivity : 0 < R^6)
  exact (Real.sqrt_lt' (by positivity : 0 < 25*R^3)).mpr (by nlinarith only [h])

end Trinomial.Fourier
