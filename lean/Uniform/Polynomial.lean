import Mathlib.Algebra.Polynomial.UnitTrinomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Binary products and their factors (Section 1) -/

namespace Uniform

open Polynomial

def IsBinary {R : Type*} [Semiring R] (P : R[X]) : Prop :=
  ∀ n, P.coeff n = 0 ∨ P.coeff n = 1

def NonnegativeCoeffs (P : ℝ[X]) : Prop := ∀ n, 0 ≤ P.coeff n

/-- The statement of Theorem 1.1, before any normalization. -/
def TrinomialFactorStatement : Prop :=
  ∀ A B : ℝ[X], A.Monic → B.Monic → NonnegativeCoeffs A → NonnegativeCoeffs B →
    A.support.card = 3 → IsBinary (A * B) → IsBinary A ∧ IsBinary B

variable {A B : ℝ[X]}

theorem IsBinary.coeff_le_one (h : IsBinary A) (n : ℕ) : A.coeff n ≤ 1 := by
  rcases h n with h | h <;> simp [h]

/-- Each nonnegative summand of a product coefficient is bounded by that coefficient. -/
theorem coeff_pair_le_product (ha : NonnegativeCoeffs A) (hb : NonnegativeCoeffs B)
    (i j : ℕ) : A.coeff i * B.coeff j ≤ (A * B).coeff (i+j) := by
  rw [coeff_mul]
  exact Finset.single_le_sum
    (f := fun p : ℕ × ℕ => A.coeff p.1 * B.coeff p.2)
    (fun p _ => mul_nonneg (ha _) (hb _)) (show (i,j) ∈ Finset.antidiagonal (i+j) from Finset.mem_antidiagonal.mpr rfl)

theorem factor_coeff_le_one (ha : NonnegativeCoeffs A) (hb : NonnegativeCoeffs B)
    (hm : B.Monic) (hc : IsBinary (A * B)) (i : ℕ) : A.coeff i ≤ 1 := by
  have h := (coeff_pair_le_product ha hb i B.natDegree).trans (hc.coeff_le_one _)
  simpa [hm.coeff_natDegree] using h

theorem IsBinary.lifts_int (h : IsBinary A) : A ∈ lifts (algebraMap ℤ ℝ) := by
  apply (lifts_iff_coeff_lifts _).2
  intro n
  rcases h n with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

/-- Monic division over a subring computes the same cofactor after extension of scalars. -/
theorem cofactor_lifts {R : Type*} [CommRing R] (f : R →+* ℝ) (hf : Function.Injective f)
    (hm : A.Monic) (ha : A ∈ lifts f) (hc : A * B ∈ lifts f) : B ∈ lifts f := by
  obtain ⟨a, ea⟩ := (mem_lifts _).mp ha
  obtain ⟨c, ec⟩ := (mem_lifts _).mp hc
  have hma : a.Monic := hf.monic_map_iff.mpr (ea ▸ hm)
  exact (mem_lifts _).mpr ⟨c /ₘ a, by
    rw [map_divByMonic f hma, ea, ec, mul_divByMonic_cancel_left _ hm]⟩

/-- The integral case of the coefficient recurrence, for an arbitrary monic binary factor. -/
theorem binary_cofactor (hm : A.Monic) (ha : IsBinary A) (hb : NonnegativeCoeffs B)
    (hc : IsBinary (A * B)) : IsBinary B := by
  have hA : NonnegativeCoeffs A := fun n => by rcases ha n with h | h <;> simp [h]
  have hle := factor_coeff_le_one hb hA hm (mul_comm A B ▸ hc)
  have hl := cofactor_lifts (algebraMap ℤ ℝ) (Int.cast_injective) hm ha.lifts_int hc.lifts_int
  intro n
  obtain ⟨z, hz⟩ := (lifts_iff_coeff_lifts _).mp hl n
  change (z : ℝ) = B.coeff n at hz
  have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (hz ▸ hb n : 0 ≤ (z : ℝ))
  have hz1 : z ≤ (1 : ℤ) := by exact_mod_cast (hz ▸ hle n : (z : ℝ) ≤ 1)
  have : z = 0 ∨ z = 1 := by omega
  rcases this with rfl | rfl <;> simp [← hz]

theorem factor_coeff_integral (hm : A.Monic) (hn : B.Monic) (hc : IsBinary (A * B))
    (i : ℕ) : IsIntegral ℤ (A.coeff i) := by
  obtain ⟨c, ec⟩ := (mem_lifts _).mp hc.lifts_int
  have hinj : Function.Injective (algebraMap ℤ ℝ) := Int.cast_injective
  have hcm : c.Monic := hinj.monic_map_iff.mpr (ec ▸ hm.mul hn)
  have hl := integralClosure.mem_lifts_of_monic_of_dvd_map ℝ hcm hm
    (ec.symm ▸ dvd_mul_right A B)
  obtain ⟨x, hx⟩ := (lifts_iff_coeff_lifts _).mp hl i
  exact hx ▸ x.property

end Uniform
