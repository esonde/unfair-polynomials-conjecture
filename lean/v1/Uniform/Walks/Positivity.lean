module

public import Uniform.Walks.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-! # Positivity of the walk functional on the interval [-2,2] -/

noncomputable section
namespace Uniform.Walks

open Polynomial
open LaurentPolynomial (T invert)

private inductive Squares : Laurent → Prop
  | term (h : Laurent) : Squares (h*invert h)
  | add {p q} : Squares p → Squares q → Squares (p+q)

private theorem Squares.mul {p q : Laurent} (hp : Squares p) (hq : Squares q) : Squares (p*q) := by
  induction hp with
  | add h h' ih ih' => rw [add_mul]; exact .add ih ih'
  | term h =>
    induction hq with
    | add g g' ih ih' => rw [mul_add]; exact .add ih ih'
    | term g =>
      convert Squares.term (h*g) using 1
      rw [map_mul]; ring

private theorem Squares.coeff_zero {p : Laurent} (hp : Squares p) : 0 ≤ p.coeff 0 := by
  induction hp with
  | term h => rw [← sum_squares]; exact tsum_nonneg (fun i => sq_nonneg _)
  | add _ _ ih ih' => exact add_nonneg ih ih'

private theorem constant_squares {a : ℝ} (ha : 0 ≤ a) : Squares (walk (C a)) := by
  convert Squares.term (walk (C (Real.sqrt a))) using 1
  rw [invert_walk, ← map_mul, ← C_mul, Real.mul_self_sqrt ha]

private theorem linear_squares (z : ℝ) (hz : z ≤ -2) : Squares (walk (X-C z)) := by
  have hn : 0 ≤ -z-2 := by linarith
  convert (constant_squares hn).add (Squares.term (1+T 1)) using 1
  simp only [map_sub,walk_X,walk_C,map_add,map_one,LaurentPolynomial.invert_T,
    map_neg,map_ofNat,J]
  linear_combination -step_product

private theorem linear_squares' (z : ℝ) (hz : 2 ≤ z) : Squares (walk (C z-X)) := by
  have hn : 0 ≤ z-2 := by linarith
  convert (constant_squares hn).add (Squares.term (1-T 1)) using 1
  simp only [map_sub,walk_X,walk_C,map_one,LaurentPolynomial.invert_T,map_ofNat,J]
  linear_combination -step_product

private theorem quad_squares (z : ℂ) : Squares (walk (X^2-C (2*z.re)*X+C (‖z‖^2))) := by
  have sum := (Squares.term (walk (X-C z.re))).add (constant_squares (sq_nonneg z.im))
  rw [invert_walk, ← map_mul, ← map_add] at sum
  convert sum using 2
  have he := Complex.sq_norm_sub_sq_re z
  have h : ‖z‖^2 = z.re^2+z.im^2 := by linarith
  rw [h]; simp only [map_add,map_mul,map_pow,map_ofNat]; ring

private theorem strictly_positive_squares (p : ℝ[X]) (pos : ∀ u ∈ Set.Icc (-2 : ℝ) 2, 0 < p.eval u) :
    Squares (walk p) := by
  classical
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    have at0 := pos 0 (by constructor <;> norm_num)
    have pn : p ≠ 0 := by rintro rfl; simp at at0
    by_cases hd : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hd]
      apply constant_squares
      simpa only [coeff_zero_eq_eval_zero] using at0.le
    have divide (g : ℝ[X]) (hg : g ∣ p) (deg : 0 < g.natDegree)
        (pg : ∀ u ∈ Set.Icc (-2 : ℝ) 2, 0 < g.eval u) (sg : Squares (walk g)) : Squares (walk p) := by
      obtain ⟨q,hq⟩ := hg
      have qn : q ≠ 0 := fun e => pn (by rw [hq,e,mul_zero])
      have gn : g ≠ 0 := by rintro rfl; simp at deg
      have hn : q.natDegree < n := by rw [hq,natDegree_mul gn qn] at h; omega
      have posq (u : ℝ) (hu : u ∈ Set.Icc (-2 : ℝ) 2) : 0 < q.eval u := by
        have := pos u hu
        rw [hq,eval_mul] at this
        exact pos_of_mul_pos_right this (pg u hu).le
      rw [hq,map_mul]; exact sg.mul (ih _ hn q posq rfl)
    obtain ⟨z,hz⟩ : ∃ z : ℂ, aeval z p = 0 := IsAlgClosed.exists_aeval_eq_zero _ p
      (fun hdeg => hd (Nat.le_zero.mp (natDegree_le_iff_degree_le.mpr (by simpa using hdeg.le))))
    by_cases hz0 : z.im = 0
    · lift z to ℝ using hz0
      erw [aeval_ofReal] at hz
      have root : p.eval z = 0 := Complex.ofReal_eq_zero.mp hz
      have outside : z < -2 ∨ 2 < z := by
        by_cases lo : z < -2
        · exact Or.inl lo
        · exact Or.inr (lt_of_not_ge (fun hi => (pos z ⟨le_of_not_gt lo, hi⟩).ne' root))
      have dvd := dvd_iff_isRoot.mpr root
      rcases outside with lo | hi
      · apply divide (X-C z) dvd (by simp) _ (linear_squares z lo.le)
        intro u hu; simp only [eval_sub,eval_X,eval_C]; linarith [hu.1]
      · apply divide (C z-X) (by simpa only [← neg_sub X (C z), neg_dvd] using dvd)
            (by rw [← neg_sub X (C z),natDegree_neg]; simp) _ (linear_squares' z hi.le)
        intro u hu; simp only [eval_sub,eval_C,eval_X]; linarith [hu.2]
    · apply divide _ (p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hz0)
        (show 0 < (X^2-C (2*z.re)*X+C (‖z‖^2) : ℝ[X]).natDegree by rw [show (X^2-C (2*z.re)*X+C (‖z‖^2) : ℝ[X]).natDegree = 2 by compute_degree!]; decide) _ (quad_squares z)
      intro u _
      simp only [eval_add,eval_sub,eval_pow,eval_mul,eval_X,eval_C]
      nlinarith [Complex.sq_norm_sub_sq_re z, sq_pos_of_ne_zero hz0, sq_nonneg (u-z.re)]

theorem moment_nonneg {p : ℝ[X]} (h : ∀ u ∈ Set.Icc (-2 : ℝ) 2, 0 ≤ p.eval u) : 0 ≤ moment p := by
  by_contra! hn
  let e := -(moment p)/2
  have he : 0 < e := by dsimp [e]; linarith
  have hp := strictly_positive_squares (p+C e) (fun u hu => by simpa using add_pos_of_nonneg_of_pos (h u hu) he)
  have bound := hp.coeff_zero
  simp only [map_add,walk_C,add_coeff,LaurentPolynomial.C_apply,if_pos rfl] at bound
  change 0 ≤ moment p+e at bound
  dsimp [e] at bound; linarith

theorem moment_le {p q : ℝ[X]} (h : ∀ u ∈ Set.Icc (-2 : ℝ) 2, p.eval u ≤ q.eval u) :
    moment p ≤ moment q := by
  have := moment_nonneg (p := q-p) (fun u hu => by simpa using sub_nonneg.mpr (h u hu))
  simpa only [moment,map_sub,sub_coeff,sub_nonneg] using this

end Uniform.Walks
