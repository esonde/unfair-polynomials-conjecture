module

public import Uniform.FourRows

@[expose] public section

/-! # Transport of strips to one complex embedding -/

noncomputable section
namespace Uniform

open Polynomial

structure Embedded (c : FractionalCase) where
  σ : c.field →ₐ[ℚ] ℂ
  D : c.field[X]
  lift_eq : D.map (algebraMap c.field ℝ) = c.B
  large : 1 < ‖σ c.gen‖
  small : ‖σ c.gen‖ ≤ 2

theorem FractionalCase.embedded (c : FractionalCase) : Nonempty (Embedded c) := by
  obtain ⟨σ,h₁,h₂⟩ := c.conjugate_annulus
  obtain ⟨D,hD⟩ := c.lift_exists
  exact ⟨⟨σ,D,hD,h₁,h₂⟩⟩

namespace Embedded

variable {c : FractionalCase}
abbrev lam (E : Embedded c) := E.σ c.gen
abbrev cofactor (E : Embedded c) := E.D.map E.σ.toRingHom

theorem ne_zero (E : Embedded c) : E.lam ≠ 0 := by
  intro he
  have hh := E.large
  change 1 < ‖E.lam‖ at hh
  norm_num [he] at hh

theorem product_binary (E : Embedded c) : IsBinary (tri c.r c.m E.lam*E.cofactor) := by
  let C := tri c.r c.m c.gen * E.D
  have realC : C.map (algebraMap c.field ℝ) = tri c.r c.m c.a * c.B := by
    rw [Polynomial.map_mul, map_tri, E.lift_eq]; rfl
  have complexC : C.map E.σ.toRingHom = tri c.r c.m E.lam * E.cofactor := by
    rw [Polynomial.map_mul, map_tri]; rfl
  intro n
  rw [← complexC, coeff_map]
  have h := c.binary n
  rw [← realC, coeff_map] at h
  rcases h with h | h
  · left
    rw [(algebraMap c.field ℝ).injective (h.trans (map_zero _).symm), map_zero]
  · right
    rw [(algebraMap c.field ℝ).injective (h.trans (map_one _).symm), map_one]

def index (S : c.Strip) (j : ℤ) (k : ℕ) : ℤ :=
  (c.bottom S.start+j)*c.m + (S.start+k)*c.r

def v (E : Embedded c) (S : c.Strip) (j : ℤ) (k : ℕ) := coeffZ E.cofactor (index S j k)

private theorem real_entry (E : Embedded c) (S : c.Strip) (j : ℤ) (k : ℕ) :
    algebraMap c.field ℝ (coeffZ E.D (index S j k)) = S.b j k := by
  rw [← map_coeffZ, E.lift_eq]; rfl

theorem transport (E : Embedded c) {S : c.Strip} {j : ℤ} {k : ℕ} {x : c.field}
    (hx : S.b j k = algebraMap c.field ℝ x) : E.v S j k = E.σ x := by
  rw [v, map_coeffZ]
  exact congrArg E.σ ((algebraMap c.field ℝ).injective ((E.real_entry ..).trans hx))

theorem transport_zero (E : Embedded c) {S : c.Strip} {j : ℤ} {k : ℕ} (h : S.b j k = 0) :
    E.v S j k = 0 := by simpa using E.transport (x := 0) (by simpa using h)

theorem transport_one (E : Embedded c) {S : c.Strip} {j : ℤ} {k : ℕ} (h : S.b j k = 1) :
    E.v S j k = 1 := by simpa using E.transport (x := 1) (by simpa using h)

theorem row (E : Embedded c) {S : c.Strip} {j : ℤ} {k : ℕ} (hd : S.d j (k+1) = 1) :
    E.v S j (k+1)+E.v S (j-1) (k+1)+E.lam*E.v S j k = 1 := by
  let f := algebraMap c.field ℝ
  have hr : f (coeffZ E.D (index S j (k+1)) + coeffZ E.D (index S (j-1) (k+1)) +
      c.gen*coeffZ E.D (index S j k)) = f 1 := by
    simp only [f, map_add, map_mul, map_one, E.real_entry, IntermediateField.AdjoinSimple.algebraMap_gen]
    exact (S.row j k).symm.trans hd
  have he := congrArg E.σ.toRingHom (f.injective hr)
  have gen : E.σ c.gen = E.σ.toRingHom c.gen := rfl
  simpa only [v, map_coeffZ, map_add, map_mul, map_one, lam, gen] using he

theorem map_rows {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a : K) (n : ℕ) :
    f (firstRow a n) = firstRow (f a) n ∧ f (secondRow a n) = secondRow (f a) n := by
  induction n with
  | zero => simp [firstRow, secondRow]
  | succ n ih => simp [firstRow, secondRow, ih]

theorem bottom_rows (E : Embedded c) (S : c.Strip) {n : ℕ} (hn : n ≤ S.width) :
    E.v S 0 n = firstRow E.lam n ∧ E.v S 1 n = secondRow E.lam n := by
  let f := algebraMap c.field ℝ
  obtain ⟨p,q,_⟩ := S.two_rows hn
  have h := map_rows f c.gen n
  have hσ := map_rows E.σ.toRingHom c.gen n
  exact ⟨(E.transport (p.trans h.1.symm)).trans hσ.1,
    (E.transport (q.trans h.2.symm)).trans hσ.2⟩

/-- The two parameters determined at the shared column. -/
def U (E : Embedded c) (S : c.Strip) : ℂ := ((1+E.lam)*E.v S 2 0-1)/E.lam
def V (E : Embedded c) (S : c.Strip) : ℂ := ((1+E.lam)*E.v S 3 0+E.v S 2 0-1)/E.lam

private theorem shared (E : Embedded c) {P S : c.Strip} (adj : P.start+P.width = S.start)
    {i j : ℤ} (h : c.bottom S.start+i = c.bottom P.start+j) :
    E.v S i 0 = E.v P j P.width := by simp [v, index, adj, h]

private theorem old_bottom {P S : c.Strip} (adj : P.start+P.width = S.start) :
    c.bottom (S.start-1) = c.bottom P.start := adj ▸ P.bottom_previous

private theorem adjacent_digits (S : c.Strip) {i : ℤ} (hi : c.bottom S.start+i+1 < c.bottom (S.start-1)) :
    (S.b i 0 = 0 ∧ S.b (i+1) 0 = 0) ∨ (S.b i 0 = 1 ∧ S.b (i+1) 0 = 0) ∨
    (S.b i 0 = 0 ∧ S.b (i+1) 0 = 1) := by
  have h := c.word_binary (l := S.start) (i := c.bottom S.start+i) (by omega)
  have h' := c.word_binary hi
  have he := c.array (c.bottom S.start+i+1) S.start
  have hd := c.binary_digit (c.bottom S.start+i+1) S.start
  rw [add_sub_cancel_right, c.below hi, mul_zero, add_zero] at he
  simp only [FractionalCase.Strip.b, Nat.cast_zero, add_zero, ← add_assoc]
  rcases h with h | h <;> rcases h' with h' | h' <;> simp [h, h']
  rcases hd with hd | hd <;> linarith

theorem inherited (E : Embedded c) {P S : c.Strip} (adj : P.start+P.width = S.start) :
    ‖E.U S‖ ≤ ‖E.lam‖^P.width ∧ ‖E.V S‖ ≤ P.width*‖E.lam‖^P.width := by
  let L := E.lam
  let R := ‖L‖
  have hR : 1 ≤ R := E.large.le
  have hRp : 1 ≤ R^P.width := one_le_pow₀ hR
  have hv : (1 : ℝ) ≤ P.width := by exact_mod_cast P.positive
  have hV : R^P.width ≤ P.width*R^P.width := le_mul_of_one_le_left (by positivity) hv
  have hinv : ‖-(1/L)‖ ≤ 1 := by rw [norm_neg, norm_div, norm_one]; exact div_le_one_of_le₀ hR (norm_nonneg _)
  have hp := E.bottom_rows P (le_refl P.width)
  have ends := row_endpoints L P.width
  have hd := c.drop_depth S.drop
  have old := old_bottom adj
  by_cases two : c.bottom (S.start-1) = c.bottom S.start+2
  · have H := (E.shared adj (i := 2) (j := 0) (by omega)).trans hp.1
    have G := (E.shared adj (i := 3) (j := 1) (by omega)).trans hp.2
    have u : E.U S = (-L)^P.width := by
      rw [U,H, div_eq_iff E.ne_zero]; change (1+L)*_-1 = _
      linear_combination ends.1
    have v : E.V S = -P.width*(-L)^P.width := by
      rw [V,H,G, div_eq_iff E.ne_zero]; change (1+L)*_+_-1 = _
      rw [ends.2, pow_succ]; ring
    rw [u,v]; simp [L, norm_mul]
  by_cases three : c.bottom (S.start-1) = c.bottom S.start+3
  · have hz := c.word_top_zero S.start
    have H : E.v S 2 0 = 0 := E.transport_zero (by
      simpa [FractionalCase.Strip.b, show c.bottom (S.start-1)-1 = c.bottom S.start+2 by omega] using hz)
    have G := (E.shared adj (i := 3) (j := 0) (by omega)).trans hp.1
    have v : E.V S = (-L)^P.width := by
      rw [V,H,G,add_zero, div_eq_iff E.ne_zero]; change (1+L)*_-1 = _
      linear_combination ends.1
    refine ⟨?_, ?_⟩
    · simpa [U,H, neg_div] using hinv.trans hRp
    · simpa [v,L,R] using hV
  · have hi : c.bottom S.start+2+1 < c.bottom (S.start-1) := by omega
    have digits := adjacent_digits S hi
    norm_num only at digits
    rcases digits with ⟨h,g⟩ | ⟨h,g⟩ | ⟨h,g⟩
    · have H := E.transport_zero h
      have G := E.transport_zero g
      constructor <;> simp only [U,V,H,G,mul_zero,add_zero,zero_sub]
      · simpa [neg_div] using hinv.trans hRp
      · simpa [neg_div] using (hinv.trans hRp).trans hV
    · have H := E.transport_one h
      have G := E.transport_zero g
      simpa [U,V,H,G,E.ne_zero,L,R] using And.intro hRp (show 0 ≤ P.width*R^P.width by positivity)
    · have H := E.transport_zero h
      have G := E.transport_one g
      simpa [U,V,H,G,E.ne_zero,L,R,neg_div] using And.intro (hinv.trans hRp) (hRp.trans hV)

end Embedded
end Uniform
