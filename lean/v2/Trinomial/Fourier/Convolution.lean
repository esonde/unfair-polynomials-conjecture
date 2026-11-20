module

public import Trinomial.Fourier.Torus

@[expose] public section

/-! # From the torus estimate to the filtered cofactor differences -/

noncomputable section
namespace Trinomial.Fourier

open Polynomial Finset

/-- Reindex an absolutely convergent pairing with a bounded array. -/
private theorem pairing (lam : ℂ) (hR : 1 ≤ ‖lam‖) (h₂ : ‖lam‖ ≤ 2)
    (v : Lattice → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    let a := torusCoeff (quotient lam)
    ∑' i, a i*(v i + v (i+(1,0)) + lam*v (i+(0,1))) =
      ∑' i, polynomialArray (mask (‖lam‖^2-1) X) i * v i := by
  let a := torusCoeff (quotient lam)
  have ha := (fourier_bound lam hR h₂).2.1
  have eqA : a = coefficients lam (lt_of_lt_of_le zero_lt_one hR) :=
    funext (quotient_coefficient lam hR)
  let B (j i : Lattice) := a i*v (i+j)
  let A (j i : Lattice) := a (i-j)*v i
  have sb (j : Lattice) : Summable (B j) := (ha.mul_right C).of_norm_bounded (fun i => by
    simpa [B,norm_mul] using mul_le_mul_of_nonneg_left (hv (i+j)) (norm_nonneg (a i)))
  have eq (j i : Lattice) : A j ((Equiv.addRight j) i) = B j i := by simp [A,B]
  have sa (j : Lattice) : Summable (A j) := (Equiv.addRight j).summable_iff.mp (by
    simpa only [Function.comp_def,eq] using sb j)
  have reindex (j : Lattice) : ∑' i, B j i = ∑' i, A j i := by
    simpa only [eq] using (Equiv.addRight j).tsum_eq (A j)
  calc
    _ = ∑' i, (B 0 i + B (1,0) i + lam*B (0,1) i) := by
      apply tsum_congr; intro i; simp only [B,add_zero]; ring
    _ = (∑' i, B 0 i) + (∑' i, B (1,0) i) + lam*∑' i, B (0,1) i := by
      rw [Summable.tsum_add ((sb _).add (sb _)) ((sb _).mul_left _),
        Summable.tsum_add (sb _) (sb _),tsum_mul_left]
    _ = _ := by
      simp only [reindex]
      rw [← tsum_mul_left,← Summable.tsum_add (sa _) (sa _),
        ← Summable.tsum_add ((sa _).add (sa _)) ((sa _).mul_left _)]
      apply tsum_congr; intro i
      simpa only [A,eqA,sub_zero,add_mul,mul_assoc] using
        congrArg (fun x : ℂ => x*v i) (coefficient_equation lam (lt_of_lt_of_le zero_lt_one hR) i)

private theorem coeff_bound (B : ℂ[X]) (n : ℤ) : ‖coeffZ B n‖ ≤ ∑ i ∈ B.support, ‖B.coeff i‖ := by
  have hn : 0 ≤ ∑ i ∈ B.support, ‖B.coeff i‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  by_cases h : 0 ≤ n
  · lift n to ℕ using h
    rw [coeffZ_natCast]
    by_cases hm : n ∈ B.support
    · exact single_le_sum (fun i _ => norm_nonneg (B.coeff i)) hm
    · have hz : B.coeff n = 0 := by simpa [Polynomial.mem_support_iff] using hm
      simpa [hz] using hn
  · simpa [coeffZ,h] using hn

private theorem mask_pairing (t : ℝ) (m : ℕ) (N : ℤ) (D : ℂ[X]) :
    ∑' i, polynomialArray (mask t X) i * coeffZ D (N-m*i.1) = coeffZ (mask t (X^m)*D) N := by
  rw [polynomial_pairing]
  let P := mask t X
  have expand : P.comp (X^m) = mask t (X^m) := by simp [P,mask,Polynomial.sub_comp,Polynomial.mul_comp,
    Polynomial.pow_comp,Polynomial.add_comp]
  rw [← expand,Polynomial.comp_eq_sum_left,Polynomial.sum_def,Finset.sum_mul]
  have coeff_sum (s : Finset ℕ) (f : ℕ → ℂ[X]) : coeffZ (∑ i ∈ s, f i) N = ∑ i ∈ s, coeffZ (f i) N := by
    induction s using Finset.induction_on with
    | empty => simp [coeffZ]
    | insert x s hx ih => simp [hx,coeffZ_add,ih]
  rw [coeff_sum]
  apply sum_congr rfl
  intro n _
  rw [mul_assoc,coeffZ_C_mul,← pow_mul,coeffZ_X_pow_mul,Nat.cast_mul]
  rfl

theorem global_bound : GlobalBound := by
  intro r m lam B _ _ hR h₂ hc N
  let D := (1-X^r)*B
  let idx (i : Lattice) := N-m*i.1-r*i.2
  let v (i : Lattice) := coeffZ D (idx i)
  let a := torusCoeff (quotient lam)
  have hv (i : Lattice) : ‖v i‖ ≤ ∑ n ∈ D.support, ‖D.coeff n‖ := coeff_bound D _
  have pair := pairing lam hR h₂ v _ hv
  have act (i : Lattice) : v i + v (i+(1,0)) + lam*v (i+(0,1)) = coeffZ (tri r m lam*D) (idx i) := by
    rw [recurrence]
    have h₁ : idx (i+(1,0)) = idx i - m := by dsimp [idx]; ring
    have h₂' : idx (i+(0,1)) = idx i - r := by dsimp [idx]; ring
    simp only [v,h₁,h₂']
  have dig (i : Lattice) : ‖coeffZ (tri r m lam*D) (idx i)‖ ≤ 1 := by
    rw [show tri r m lam*D = tri r m lam*B-X^r*(tri r m lam*B) by dsimp [D]; ring,coeffZ_sub,coeffZ_X_pow_mul]
    rcases hc.coeffZ (idx i) with h|h <;> rcases hc.coeffZ (idx i-r) with g|g <;> simp [h,g]
  have bound := (fourier_bound lam hR h₂).2
  have est : ‖∑' i, a i*coeffZ (tri r m lam*D) (idx i)‖ ≤ ∑' i, ‖a i‖ := by
    apply tsum_of_norm_bounded bound.1.hasSum
    intro i; rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (dig i)
  dsimp only at pair
  simp_rw [act] at pair
  have rhs : ∑' i, polynomialArray (mask (‖lam‖^2-1) X) i * v i = coeffZ (mask (‖lam‖^2-1) (X^m)*D) N := by
    rw [← mask_pairing,polynomial_pairing,polynomial_pairing]
    apply sum_congr rfl; intro n _
    simp [v,idx,axis]
  rw [show (1-X^r)*mask (‖lam‖^2-1) (X^m)*B = mask (‖lam‖^2-1) (X^m)*D by dsimp [D]; ring,
    ← rhs,← pair]
  exact est.trans_lt bound.2

end Trinomial.Fourier
