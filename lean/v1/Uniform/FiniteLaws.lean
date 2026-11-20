module

public import Uniform.Trinomial

@[expose] public section

/-! # Uniformity of finitely supported mass functions on the integers

Multiplication of real Laurent polynomials is convolution of their coefficients.
Integer translations and positive rescaling reduce the assertion to Theorem 1.1.
-/

noncomputable section
namespace Uniform

open Polynomial
open LaurentPolynomial (T)

/-- All nonzero values of a mass function are equal. -/
def UniformOnSupport {ι K : Type*} [Zero K] (f : ι → K) : Prop :=
  ∀ i j, f i ≠ 0 → f j ≠ 0 → f i = f j

private def monicPart (P : ℝ[X]) := C P.leadingCoeff⁻¹ * P

private theorem part_monic (P : ℝ[X]) (hp : P ≠ 0) : (monicPart P).Monic := by
  simp [monicPart,Monic,leadingCoeff_mul,leadingCoeff_ne_zero.mpr hp]

private theorem part_nonneg (P : ℝ[X]) (hp : NonnegativeCoeffs P) : NonnegativeCoeffs (monicPart P) := by
  intro i
  rw [monicPart,coeff_C_mul]
  exact mul_nonneg (inv_nonneg.mpr (hp P.natDegree)) (hp i)

private theorem part_binary (P : ℝ[X]) (hp : P ≠ 0) :
    IsBinary (monicPart P) ↔ UniformOnSupport P.coeff := by
  have hl := leadingCoeff_ne_zero.mpr hp
  constructor
  · intro h i j hi hj
    have value (n : ℕ) (hn : P.coeff n ≠ 0) : P.coeff n = P.leadingCoeff := by
      have he := h n
      simp only [monicPart,coeff_C_mul] at he
      rcases he with hz|ho
      · exact ((mul_ne_zero (inv_ne_zero hl) hn) hz).elim
      · field_simp at ho; linarith
    exact (value i hi).trans (value j hj).symm
  · intro h n
    rw [monicPart,coeff_C_mul]
    by_cases hz : P.coeff n = 0
    · simp [hz]
    · right
      rw [h n P.natDegree hz hl,coeff_natDegree,inv_mul_cancel₀ hl]

private theorem polynomial_laws {A B : ℝ[X]} (ha : NonnegativeCoeffs A) (hb : NonnegativeCoeffs B)
    (na : A ≠ 0) (nb : B ≠ 0) (count : A.support.card = 3)
    (flat : UniformOnSupport (A*B).coeff) : UniformOnSupport A.coeff ∧ UniformOnSupport B.coeff := by
  have su : (monicPart A).support = A.support := by
    ext i; simp [monicPart,mem_support_iff,leadingCoeff_ne_zero.mpr na]
  have prod : monicPart A*monicPart B = monicPart (A*B) := by
    simp only [monicPart,leadingCoeff_mul,mul_inv_rev,map_mul]; ring
  have h := trinomial_factor (part_monic A na) (part_monic B nb) (part_nonneg A ha) (part_nonneg B hb)
    (su ▸ count) (prod ▸ (part_binary _ (mul_ne_zero na nb)).mpr flat)
  exact ⟨(part_binary A na).mp h.1, (part_binary B nb).mp h.2⟩

private theorem translated (P : ℝ[X]) (s n : ℤ) :
    (P.toLaurent * T s : LaurentPolynomial ℝ).coeff n = coeffZ P (n-s) := by
  rw [LaurentPolynomial.T,AddMonoidAlgebra.coeff_mul_single_apply,mul_one,LaurentPolynomial.coeff_toLaurent]
  rw [← sub_eq_add_neg]
  generalize n-s = d
  cases d with
  | ofNat i =>
    simpa [coeffZ, Polynomial.toFinsupp_apply] using
      Finsupp.mapDomain_apply_of_injective
        (Nat.castEmbedding : ℕ ↪ ℤ).injective P.toFinsupp.coeff i
  | negSucc i =>
    rw [coeffZ_of_neg _ (by omega)]
    exact Finsupp.mapDomain_notin_range _ _ (by
      rintro ⟨k, hk⟩
      change (k : ℤ) = Int.negSucc i at hk
      omega)

private theorem translated_flat (P : ℝ[X]) (s : ℤ) :
    UniformOnSupport (P.toLaurent*T s : LaurentPolynomial ℝ).coeff ↔ UniformOnSupport P.coeff := by
  constructor
  · intro h i j hi hj
    have H (n : ℕ) : (P.toLaurent*T s : LaurentPolynomial ℝ).coeff ((n:ℤ)+s) = P.coeff n := by simp [translated]
    exact H i ▸ H j ▸ h _ _ ((H i).trans_ne hi) ((H j).trans_ne hj)
  · intro h i j hi hj
    rw [translated] at hi hj ⊢
    rw [translated]
    by_cases ei : i-s < 0
    · exact (hi (coeffZ_of_neg _ ei)).elim
    by_cases ej : j-s < 0
    · exact (hj (coeffZ_of_neg _ ej)).elim
    simp [coeffZ,le_of_not_gt ei,le_of_not_gt ej] at hi hj ⊢
    simpa [hi.1,hj.1] using h _ _ hi.2 hj.2

private theorem translated_count (P : ℝ[X]) (s : ℤ) :
    (P.toLaurent*T s).coeff.support.card = P.support.card := by
  have eq : (P.toLaurent*T s).coeff.support = P.support.map (Nat.castEmbedding.trans (Equiv.addRight s).toEmbedding) := by
    ext z
    simp only [Finsupp.mem_support_iff,translated,Finset.mem_map,Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding,Nat.castEmbedding_apply,Polynomial.mem_support_iff]
    change coeffZ P (z-s) ≠ 0 ↔ ∃ i : ℕ, P.coeff i ≠ 0 ∧ (i:ℤ)+s = z
    by_cases hz : 0 ≤ z-s
    · simp only [coeffZ,hz,if_true]
      constructor
      · intro h; exact ⟨(z-s).toNat,h,by omega⟩
      · rintro ⟨i,hi,he⟩; rwa [show (z-s).toNat = i by omega]
    · rw [coeffZ_of_neg _ (lt_of_not_ge hz)]
      constructor
      · simp
      · rintro ⟨i,_,he⟩; omega
  rw [eq,Finset.card_map]

/-- Convolution form for arbitrary nonzero finite mass functions on ℤ. -/
theorem uniform_factors_of_convolution (a b : AddMonoidAlgebra ℝ ℤ)
    (ha : ∀ i, 0 ≤ a.coeff i) (hb : ∀ i, 0 ≤ b.coeff i) (nb : b ≠ 0)
    (count : a.coeff.support.card = 3) (flat : UniformOnSupport (a*b).coeff) :
    UniformOnSupport a.coeff ∧ UniformOnSupport b.coeff := by
  induction a using LaurentPolynomial.induction_on_mul_T with | mul_T =>
    induction b using LaurentPolynomial.induction_on_mul_T with | mul_T =>
      rename_i A s B t
      have idx (p : ℝ[X]) (u : ℤ) (n : ℕ) : (p.toLaurent*T u : LaurentPolynomial ℝ).coeff ((n:ℤ)+u) = p.coeff n := by simp [translated]
      have product : A.toLaurent*T (-(s:ℤ))*(B.toLaurent*T (-(t:ℤ))) =
          (A*B).toLaurent*T (-(s:ℤ)-t) := by rw [map_mul,sub_eq_add_neg,LaurentPolynomial.T_add]; ring
      rw [product,translated_flat] at flat
      rw [translated_count] at count
      have na : A ≠ 0 := by rintro rfl; simp at count
      have nb' : B ≠ 0 := by rintro rfl; simp at nb
      rw [translated_flat,translated_flat]
      exact polynomial_laws (fun n => idx A _ n ▸ ha _) (fun n => idx B _ n ▸ hb _) na nb' count flat

end Uniform
