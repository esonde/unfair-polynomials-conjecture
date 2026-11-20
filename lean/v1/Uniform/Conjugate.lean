module

public import Uniform.Normalization
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section

/-! # A conjugate in the annulus, Lemma 1.2 -/

noncomputable section
namespace Uniform

open Polynomial NumberField
open scoped IntermediateField NumberField

/-- The nonzero integral norm compensates for an embedding strictly inside the unit disk. -/
theorem exists_large_embedding {K : Type*} [Field K] [NumberField K] (x : K)
    (hx : IsIntegral ℤ x) (hne : x ≠ 0) (ι : K →ₐ[ℚ] ℂ) (hi : ‖ι x‖ < 1) :
    ∃ σ : K →ₐ[ℚ] ℂ, 1 < ‖σ x‖ := by
  classical
  by_contra! h
  let z : 𝓞 K := ⟨x, hx⟩
  have hz : z ≠ 0 := fun e => hne (congrArg Subtype.val e)
  have hnorm : (1 : ℝ) ≤ |(Algebra.norm ℚ x : ℝ)| := by
    change (1 : ℝ) ≤ |(Algebra.norm ℚ (z : K) : ℝ)|
    rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hz)
  have hprod : (∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖) < 1 := by
    calc
      _ < ∏ _ : K →ₐ[ℚ] ℂ, (1 : ℝ) := Finset.prod_lt_prod₀
        (fun σ _ => norm_pos_iff.mpr ((_root_.map_ne_zero σ).mpr hne))
        (fun σ _ => h σ) ⟨ι, Finset.mem_univ _, hi⟩
      _ = 1 := by simp
  rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings, eq_ratCast,
    ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs] at hprod
  exact (not_lt_of_ge hnorm) hprod

/-- A finite set stable under this two-summand relation bounds the expansion by two. -/
theorem diameter_bound {lam : ℂ} (S : Finset ℂ) (h₀ : 0 ∈ S) (h₁ : 1 ∈ S)
    (closed : ∀ x ∈ S, ∃ u ∈ S, ∃ v ∈ S, 1 - lam*x = u+v) : ‖lam‖ ≤ 2 := by
  classical
  have memPair {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) : (a,b) ∈ S ×ˢ S :=
    Finset.mem_product.mpr ⟨ha,hb⟩
  obtain ⟨⟨a,b⟩, hab, hmax⟩ := (S ×ˢ S).exists_max_image
    (fun p : ℂ × ℂ => ‖p.1 - p.2‖) ⟨_, memPair h₁ h₀⟩
  have hdist (x y : ℂ) (hx : x ∈ S) (hy : y ∈ S) : ‖x-y‖ ≤ ‖a-b‖ :=
    hmax (x,y) (memPair hx hy)
  have hd : 1 ≤ ‖a-b‖ := by simpa using hdist 1 0 h₁ h₀
  obtain ⟨u,hu,v,hv,he⟩ := closed a (Finset.mem_product.mp hab).1
  obtain ⟨s,hs,t,ht,hf⟩ := closed b (Finset.mem_product.mp hab).2
  have hid : lam*(a-b) = (s-u)+(t-v) := by linear_combination hf - he
  have hm : ‖lam‖ * ‖a-b‖ ≤ ‖a-b‖ + ‖a-b‖ := by
    rw [← norm_mul, hid]
    exact (norm_add_le _ _).trans (add_le_add (hdist _ _ hs hu) (hdist _ _ ht hv))
  by_contra! h
  nlinarith [mul_pos (sub_pos.mpr h) (show 0 < ‖a-b‖ by linarith)]


theorem map_tri {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (r m : ℕ) (x : K) :
    (tri r m x).map f = tri r m (f x) := by
  simp [tri_eq]

theorem map_coeffZ {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (P : K[X]) (n : ℤ) :
    coeffZ (P.map f) n = f (coeffZ P n) := by
  simp only [coeffZ, coeff_map]; split <;> simp

theorem NonnegativeCoeffs.coeffZ {P : ℝ[X]} (h : NonnegativeCoeffs P) (n : ℤ) :
    0 ≤ Uniform.coeffZ P n := by
  unfold Uniform.coeffZ; split; apply h; rfl

/-- A nonzero cofactor entry forces the digit one one column to its right. -/
theorem FractionalCase.digit_right (c : FractionalCase) (n : ℤ) (hn : coeffZ c.B n ≠ 0) :
    coeffZ (tri c.r c.m c.a * c.B) (n+c.r) = 1 := by
  apply (c.binary.coeffZ _).resolve_left
  rw [recurrence, add_sub_cancel_right]
  have := mul_pos c.a_pos (lt_of_le_of_ne (c.nonnegative.coeffZ n) hn.symm)
  linarith [c.nonnegative.coeffZ (n+c.r), c.nonnegative.coeffZ (n+c.r-c.m)]

/-- Every possible integer-indexed coefficient occurs in this finite set, including zero. -/
private def values (P : ℂ[X]) : Finset ℂ := by
  classical exact insert 0 (P.support.image P.coeff)

private theorem mem_values (P : ℂ[X]) (x : ℂ) : x ∈ values P ↔ ∃ n : ℤ, coeffZ P n = x := by
  classical
  simp only [values, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨n, _, rfl⟩)
    · exact ⟨-1, coeffZ_of_neg _ (by decide)⟩
    · exact ⟨n, coeffZ_natCast ..⟩
  · rintro ⟨n, rfl⟩
    by_cases hn : 0 ≤ n
    · rw [coeffZ, if_pos hn]
      by_cases h : P.coeff n.toNat = 0
      · exact Or.inl h
      · exact Or.inr ⟨_, mem_support_iff.mpr h, rfl⟩
    · exact Or.inl (coeffZ_of_neg _ (lt_of_not_ge hn))

namespace FractionalCase

abbrev field (c : FractionalCase) := ℚ⟮c.a⟯
abbrev gen (c : FractionalCase) : c.field := IntermediateField.AdjoinSimple.gen ℚ c.a

theorem integral (c : FractionalCase) : IsIntegral ℤ c.a := by
  simpa only [tri, trinomial_middle_coeff c.r_pos (show c.r < c.m by linarith [c.oriented])]
    using factor_coeff_integral (trinomial_monic (u := (1 : ℝ)) (v := c.a) c.r_pos
      (show c.r < c.m by linarith [c.oriented])) c.monic c.binary c.r

theorem lift_exists (c : FractionalCase) : ∃ D : c.field[X], D.map (algebraMap c.field ℝ) = c.B := by
  let f := algebraMap c.field ℝ
  have hm : (tri c.r c.m c.a).Monic := trinomial_monic c.r_pos (by linarith [c.oriented])
  apply (mem_lifts _).mp
  apply cofactor_lifts f f.injective hm
  · exact (mem_lifts _).mpr ⟨tri c.r c.m c.gen, map_tri ..⟩
  · apply (lifts_iff_coeff_lifts _).2
    intro n
    rcases c.binary n with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩

/-- The same embedding transports all cofactor entries and preserves the product digits. -/
theorem conjugate_annulus (c : FractionalCase) :
    ∃ σ : c.field →ₐ[ℚ] ℂ, 1 < ‖σ c.gen‖ ∧ ‖σ c.gen‖ ≤ 2 := by
  let f := algebraMap c.field ℝ
  have hfa : f c.gen = c.a := rfl
  letI : FiniteDimensional ℚ c.field := IntermediateField.adjoin.finiteDimensional c.integral.tower_top
  letI : NumberField c.field := {}
  let ι := (Complex.ofRealHom.comp f).toRatAlgHom
  have hgen : IsIntegral ℤ c.gen := isIntegral_algebraMap_iff.mp c.integral
  have hne : c.gen ≠ 0 := fun e => c.a_pos.ne' (by rw [← hfa, e, map_zero])
  have hi : ‖ι c.gen‖ < 1 := by
    change ‖(c.a : ℂ)‖ < 1
    simpa [Real.norm_eq_abs, abs_of_pos c.a_pos] using c.a_lt_one
  obtain ⟨σ, hσ⟩ := exists_large_embedding _ hgen hne ι hi
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨D, eD⟩ := c.lift_exists
  let E := D.map σ.toRingHom
  let C := tri c.r c.m c.gen * D
  have realC : C.map f = tri c.r c.m c.a * c.B := by
    rw [Polynomial.map_mul, map_tri, hfa, eD]
  have column (n : ℤ) : coeffZ E n ∈ values E := (mem_values ..).2 ⟨_, rfl⟩
  have e0 : coeffZ E 0 = 1 := by
    rw [map_coeffZ]
    have hz : f (coeffZ D 0) = 1 := by rw [← map_coeffZ, eD]; exact c.constant_one
    rw [f.injective (hz.trans (map_one f).symm), map_one]
  have zeroMem : 0 ∈ values E := (mem_values ..).2 ⟨-1, coeffZ_of_neg _ (by decide)⟩
  apply diameter_bound (values E) zeroMem (e0 ▸ column 0)
  intro x hx
  obtain ⟨n, rfl⟩ := (mem_values ..).1 hx
  by_cases h : coeffZ D n = 0
  · exact ⟨1, e0 ▸ column 0, 0, zeroMem, by simp [E, map_coeffZ, h]⟩
  · have hn : coeffZ c.B n ≠ 0 := by rw [← eD, map_coeffZ]; exact (_root_.map_ne_zero f).mpr h
    have hC : coeffZ C (n+c.r) = 1 := by
      apply f.injective
      rw [← map_coeffZ, realC, c.digit_right n hn, map_one]
    rw [recurrence, add_sub_cancel_right] at hC
    refine ⟨_, column (n+c.r), _, column (n+c.r-c.m), ?_⟩
    have he := congrArg σ hC
    simp only [map_add, map_mul, map_one] at he
    simp only [E, map_coeffZ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    linear_combination -he

end FractionalCase
end Uniform
