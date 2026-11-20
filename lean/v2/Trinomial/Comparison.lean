module

public import Trinomial.Differences
public import Trinomial.Filter

@[expose] public section

/-! # Filtered differences along a strip and the final comparison -/

noncomputable section
namespace Trinomial.Embedded

open Polynomial
variable {c : FractionalCase}

private theorem global_at (E : Embedded c) (global : GlobalBound) (S : c.Strip) (j : ℤ) (k : ℕ) :
    ‖filterAt (‖E.lam‖^2-1) (fun i => E.v S i (k+1)-E.v S i k) j‖ < 25*‖E.lam‖^3 := by
  let t := ‖E.lam‖^2-1
  let M := mask t (X^c.m)*E.cofactor
  have g := global c.r c.m E.lam E.cofactor c.r_pos (by linarith [c.oriented]) E.large.le E.small
    E.product_binary (index S j (k+1))
  rw [mul_assoc, sub_mul, one_mul, coeffZ_sub, coeffZ_X_pow_mul] at g
  have eq : index S j (k+1) - c.r = index S j k := by simp [index,Nat.cast_succ]; ring
  rw [eq] at g
  have h (n : ℕ) : coeffZ M (index S j n) = filterAt t (fun i => E.v S i n) j := by
    rw [index, mask_coeff]
    simp only [filterAt, v, index]
    ring_nf
  change ‖coeffZ M _ - coeffZ M _‖ < _ at g
  rwa [h, h, filterAt_sub] at g

private theorem negative_step (E : Embedded c) (S : c.Strip) {k : ℕ} (hw : k+1 ≤ S.width) {j : ℤ}
    (hj : j < 0) : E.v S j (k+1)-E.v S j k = (S.b j (k+1) : ℂ) := by
  rw [E.transport_zero (S.negative_before hj (by omega : k < S.width)), sub_zero]
  rcases lt_or_eq_of_le hw with interior | last
  · have hz := S.negative_before hj interior
    rw [E.transport_zero hz, hz, Complex.ofReal_zero]
  rw [last]
  have h := c.word_binary (l := S.start+S.width) (i := c.bottom S.start+j)
    (by rw [S.bottom_previous]; omega)
  change S.b j S.width = 0 ∨ S.b j S.width = 1 at h
  rcases h with h | h
  · rw [E.transport_zero h, h]; norm_num
  · rw [E.transport_one h, h]; norm_num

/-- Norm bounds for the three possible tails below the old bottom. -/
private theorem tails {t a b d f : ℝ} (ht : 0 ≤ t)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hd : d ∈ Set.Icc 0 1) (hf : f ∈ Set.Icc 0 1) :
    |-(2*(1+t^2))*a+(t^2+2*t)*b-2*t*d+f| ≤ 2*(1+t)^2 ∧
    |(t^2+2*t)*a-2*t*b+d| ≤ (1+t)^2 ∧ |-2*t*a+b| ≤ (1+t)^2 := by
  have bound (p : ℝ) (hp : 0 ≤ p) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
      0 ≤ p*x ∧ p*x ≤ p := ⟨mul_nonneg hp hx.1, by simpa using mul_le_mul_of_nonneg_left hx.2 hp⟩
  have A := bound (2*(1+t^2)) (by positivity) ha
  have B := bound (t^2+2*t) (by positivity) hb
  have D := bound (2*t) (by positivity) hd
  have A' := bound (t^2+2*t) (by positivity) ha
  have B' := bound (2*t) (by positivity) hb
  have A'' := bound (2*t) (by positivity) ha
  simp only [abs_le]
  exact ⟨⟨by nlinarith [A.2,B.1,D.2,hf.1], by nlinarith [A.1,B.2,D.1,hf.2,sq_nonneg t]⟩,
    ⟨by nlinarith [A'.1,B'.2,hd.1,sq_nonneg t], by nlinarith [A'.2,B'.1,hd.2]⟩,
    ⟨by nlinarith [A''.2,hb.1,sq_nonneg t], by nlinarith [A''.1,hb.2,sq_nonneg t]⟩⟩

/-- Section 3 bounds the filtered row differences at every step, including the next drop. -/
theorem filtered_bounds (E : Embedded c) (global : GlobalBound) (S : c.Strip)
    {k : ℕ} (hw : k+1 ≤ S.width) :
    let R := ‖E.lam‖
    let F := Four.filter (R^2-1) (E.delta S k)
    ‖F.c1‖ ≤ 27*R^4 ∧ ‖F.c2‖ ≤ 26*R^4 ∧ ‖F.c3‖ ≤ 26*R^4 := by
  let R := ‖E.lam‖
  let t := R^2-1
  let F := Four.filter t (E.delta S k)
  let D (j : ℤ) := E.v S j (k+1)-E.v S j k
  let x (j : ℤ) := S.b j (k+1)
  have ht : 0 ≤ t := by dsimp [t,R]; nlinarith [E.large, sq_nonneg (‖E.lam‖-1)]
  have hr : 1 ≤ R := E.large.le
  have h34 : R^3 ≤ R^4 := pow_le_pow_right₀ hr (by decide)
  have he : (1+t)^2 = R^4 := by dsimp [t]; ring
  have pair (j) : x j ∈ Set.Icc 0 1 := ⟨c.entry_nonneg .., c.entry_le_one ..⟩
  obtain ⟨h₁,h₂,h₃⟩ := tails ht (pair (-2)) (pair (-3)) (pair (-4)) (pair (-5))
  let a := x (-2)
  let b := x (-3)
  let d := x (-4)
  let f := x (-5)
  let e₁ := -(2*(1+t^2))*a+(t^2+2*t)*b-2*t*d+f
  let e₂ := (t^2+2*t)*a-2*t*b+d
  let e₃ := -2*t*a+b
  have dn {j : ℤ} (hj : j < 0) : D j = (x j : ℂ) := E.negative_step S hw hj
  have dz : D (-1) = 0 := by
    rw [dn (by decide)]
    change ((S.b (-1) (k+1) : ℝ) : ℂ) = 0
    rw [S.lower_neighbor hw, Complex.ofReal_zero]
  have calc₁ : filterAt t D 1 = F.c1+e₁ := by
    norm_num [filterAt,Four.filter,F,e₁,delta,dz,dn (show (-2:ℤ)<0 by decide),
      dn (show (-3:ℤ)<0 by decide),dn (show (-4:ℤ)<0 by decide),dn (show (-5:ℤ)<0 by decide),a,b,d,f,D]
    ring
  have calc₂ : filterAt t D 2 = F.c2+e₂ := by
    norm_num [filterAt,Four.filter,F,e₂,delta,dz,dn (show (-2:ℤ)<0 by decide),
      dn (show (-3:ℤ)<0 by decide),dn (show (-4:ℤ)<0 by decide),a,b,d,D]
    ring
  have calc₃ : filterAt t D 3 = F.c3+e₃ := by
    norm_num [filterAt,Four.filter,F,e₃,delta,dz,dn (show (-2:ℤ)<0 by decide),
      dn (show (-3:ℤ)<0 by decide),a,b,D]
    ring
  have bound (z : ℂ) (e : ℝ) (j : ℤ) (h : filterAt t D j = z+e) :
      ‖z‖ ≤ 25*R^3+|e| := by
    have h' : z = filterAt t D j-e := by rw [h,add_sub_cancel_right]
    rw [h']
    exact (norm_sub_le ..).trans (add_le_add (E.global_at global S j k).le
      (by rw [Complex.norm_real,Real.norm_eq_abs]))
  change ‖F.c1‖ ≤ _ ∧ ‖F.c2‖ ≤ _ ∧ ‖F.c3‖ ≤ _
  rw [he] at h₁ h₂ h₃
  exact ⟨by linarith [bound _ _ _ calc₁], by linarith [bound _ _ _ calc₂],
    by linarith [bound _ _ _ calc₃]⟩

theorem theorem_of_global_bound (global : GlobalBound) : TrinomialFactorStatement := by
  apply theorem_of_no_fractional_case
  intro c
  obtain ⟨E⟩ := c.embedded
  obtain ⟨S,P,adj,hw,h₅⟩ := c.widest
  obtain ⟨hU,hV⟩ := E.inherited adj
  let R := ‖E.lam‖
  let t := R^2-1
  have hR : 1 ≤ R := E.large.le
  have ht : 0 ≤ t := by dsimp [t]; nlinarith [sq_nonneg (R-1)]
  have hp := pow_le_pow_right₀ hR hw
  let k := S.width-1
  have he : k+1 = S.width := by dsimp [k]; omega
  obtain ⟨b₁,b₂,b₃⟩ := E.filtered_bounds global S he.le
  have hd := E.filtered_delta S t he.le
  rw [he] at hd
  change ‖(Four.filter t (E.delta S k)).c1‖ ≤ _ at b₁
  change ‖(Four.filter t (E.delta S k)).c2‖ ≤ _ at b₂
  change ‖(Four.filter t (E.delta S k)).c3‖ ≤ _ at b₃
  rw [hd] at b₁ b₂ b₃
  simp only [Four.scale,Four.formula,norm_mul,norm_pow,norm_neg] at b₁ b₂ b₃
  have hnorm : ‖(S.width : ℂ)+2*(t : ℂ)‖ = (S.width : ℝ)+2*t := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul,
      ← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [hnorm] at b₁
  exact widest_strip_impossible h₅ E.large E.small (hU.trans hp)
    (hV.trans (mul_le_mul (by exact_mod_cast hw) hp (by positivity) (by positivity)))
    (by simpa only [mul_comm (‖E.lam‖^S.width)] using b₁)
    (by simpa only [mul_comm (‖E.lam‖^S.width)] using b₂)
    (by simpa only [mul_comm (‖E.lam‖^S.width)] using b₃)

end Trinomial.Embedded
