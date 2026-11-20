import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Three weighted geometric sums used in the energy calculation -/

noncomputable section
namespace Uniform.Walks

def ell (j : ℕ) : ℝ := j+1/2

private theorem choose_three (j : ℕ) :
    ((j+3).choose 3 : ℝ) = ((j:ℝ)+3)*(j+2)*(j+1)/6 := by
  have h : ((j:ℝ)+3)*((j+2).choose 2 : ℝ) = ((j+3).choose 3 : ℝ)*3 := by
    exact_mod_cast Nat.succ_mul_choose_eq (j+2) 2
  rw [Nat.cast_choose_two] at h
  push_cast at h
  linarith

def geo1 (q : ℝ) := (1+q)/(2*(1-q)^2)
def geo2 (q : ℝ) := (1+6*q+q^2)/(4*(1-q)^3)
def geo3 (q : ℝ) := (1+23*q+23*q^2+q^3)/(8*(1-q)^4)

theorem geom_moments {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) :
    HasSum (fun j => ell j*q^j) (geo1 q) ∧
    HasSum (fun j => ell j^2*q^j) (geo2 q) ∧
    HasSum (fun j => ell j^3*q^j) (geo3 q) := by
  have hr : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq]
  have a := hasSum_geometric_of_lt_one hq hq'
  have b := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  have c := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have d := hasSum_choose_mul_geometric_of_norm_lt_one 3 hr
  have hn : 1-q ≠ 0 := sub_ne_zero.mpr hq'.ne'
  refine ⟨?_,?_,?_⟩
  · convert b.sub (a.mul_left (1/2)) using 1
    · funext n; simp [ell]; ring
    · dsimp [geo1]; field_simp; ring
  · convert ((c.mul_left 2).sub (b.mul_left 2)).add (a.mul_left (1/4)) using 1
    · funext n; simp [ell,Nat.cast_choose_two]; ring
    · dsimp [geo2]; field_simp; ring
  · convert (((d.mul_left 6).sub (c.mul_left 9)).add (b.mul_left (13/4))).sub (a.mul_left (1/8)) using 1
    · funext n; simp [ell,choose_three,Nat.cast_choose_two]; ring
    · dsimp [geo3]; field_simp; ring

/-- The pointwise density from Appendix A.3, as a polynomial in h and x. -/
def density {K : Type*} [CommRing K] [Algebra ℝ K] (h x : K) : K :=
  let w := 4-h
  let half := algebraMap ℝ K (1/2)
  let M := (h+x)*(h-x)^2*half
  let M' := (h-x)*(3*h+x)*half
  w^2*(algebraMap ℝ K (37/4)*M+3*h*x*(h+x)) +
    algebraMap ℝ K (3/2)*w^3*(3*h^2+x^2)+4*h*w*M-4*h*w^2*M'

/-- Value of the polynomial majorant at the switching point h = x. -/
theorem density_at_switch (x : ℝ) : density x x = 24*x^2*(4-x)^2 := by
  simp [density, show algebraMap ℝ ℝ = RingHom.id ℝ from rfl]
  ring

/-- Summing the square of the differentiated geometric term uses moments of
orders one, two and three. Here A and B give its affine dependence on ell. -/
theorem affine_energy {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (v w A B : ℝ) :
    HasSum (fun j => ell j*((ell j^2+9)*w^2+w*(A+B*ell j)^2)*(v*q^j))
      (v*(w^2*(geo3 q+9*geo1 q)+w*(A^2*geo1 q+2*A*B*geo2 q+B^2*geo3 q))) := by
  obtain ⟨s₁,s₂,s₃⟩ := geom_moments hq hq'
  have first := (s₃.add (s₁.mul_left 9)).mul_left (w^2)
  have second := (((s₁.mul_left (A^2)).add (s₂.mul_left (2*A*B))).add (s₃.mul_left (B^2))).mul_left w
  convert (first.add second).mul_left v using 1
  funext j; ring

end Uniform.Walks
