module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # Three weighted geometric sums used in the energy calculation -/

noncomputable section
namespace Trinomial.Fourier

def ell (j : ℕ) : ℝ := j+1/2

private theorem choose_three (j : ℕ) :
    ((j+3).choose 3 : ℝ) = ((j:ℝ)+3)*(j+2)*(j+1)/6 := by
  have h : ((j:ℝ)+3)*((j+2).choose 2 : ℝ) = ((j+3).choose 3 : ℝ)*3 := by
    exact_mod_cast Nat.add_one_mul_choose_eq (j+2) 2
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

end Trinomial.Fourier
